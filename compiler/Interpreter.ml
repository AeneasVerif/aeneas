open Cps
open InterpreterUtils
open InterpreterProjectors
open InterpreterBorrows
open InterpreterStatements
open LlbcAstUtils
module L = Logging
module T = Types
module A = LlbcAst
module SA = SymbolicAst

(** The local logger *)
let log = L.interpreter_log

let compute_type_fun_global_contexts (m : A.crate) :
    C.type_context * C.fun_context * C.global_context =
  let type_decls_list, _, _ = split_declarations m.declarations in
  let type_decls, fun_decls, global_decls = compute_defs_maps m in
  let type_decls_groups, _funs_defs_groups, _globals_defs_groups =
    split_declarations_to_group_maps m.declarations
  in
  let type_infos =
    TypesAnalysis.analyze_type_declarations type_decls type_decls_list
  in
  let type_context = { C.type_decls_groups; type_decls; type_infos } in
  let fun_context = { C.fun_decls } in
  let global_context = { C.global_decls } in
  (type_context, fun_context, global_context)

let initialize_eval_context (type_context : C.type_context)
    (fun_context : C.fun_context) (global_context : C.global_context)
    (region_groups : T.RegionGroupId.id list) (type_vars : T.type_var list) :
    C.eval_ctx =
  C.reset_global_counters ();
  {
    C.type_context;
    C.fun_context;
    C.global_context;
    C.region_groups;
    C.type_vars;
    C.env = [ C.Frame ];
    C.ended_regions = T.RegionId.Set.empty;
  }

(** Initialize an evaluation context to execute a function.

      Introduces local variables initialized in the following manner:
      - input arguments are initialized as symbolic values
      - the remaining locals are initialized as [⊥]
      Abstractions are introduced for the regions present in the function
      signature.
      
      We return:
      - the initialized evaluation context
      - the list of symbolic values introduced for the input values
      - the instantiated function signature
 *)
let initialize_symbolic_context_for_fun (type_context : C.type_context)
    (fun_context : C.fun_context) (global_context : C.global_context)
    (fdef : A.fun_decl) : C.eval_ctx * V.symbolic_value list * A.inst_fun_sig =
  (* The abstractions are not initialized the same way as for function
   * calls: they contain *loan* projectors, because they "provide" us
   * with the input values (which behave as if they had been returned
   * by some function calls...).
   * Also, note that we properly set the set of parents of every abstraction:
   * this should not be necessary, as those abstractions should never be
   * *automatically* ended (because ending some borrows requires to end
   * one of them), but rather selectively ended when generating code
   * for each of the backward functions. We do it only because we can
   * do it, and because it gives a bit of sanity.
   * *)
  let sg = fdef.signature in
  (* Create the context *)
  let region_groups =
    List.map (fun (g : T.region_var_group) -> g.id) sg.regions_hierarchy
  in
  let ctx =
    initialize_eval_context type_context fun_context global_context
      region_groups sg.type_params
  in
  (* Instantiate the signature *)
  let type_params = List.map (fun tv -> T.TypeVar tv.T.index) sg.type_params in
  let inst_sg = instantiate_fun_sig type_params sg in
  (* Create fresh symbolic values for the inputs *)
  let input_svs =
    List.map (fun ty -> mk_fresh_symbolic_value V.SynthInput ty) inst_sg.inputs
  in
  (* Initialize the abstractions as empty (i.e., with no avalues) abstractions *)
  let call_id = C.fresh_fun_call_id () in
  assert (call_id = V.FunCallId.zero);
  let compute_abs_avalues (abs : V.abs) (ctx : C.eval_ctx) :
      C.eval_ctx * V.typed_avalue list =
    (* Project over the values - we use *loan* projectors, as explained above *)
    let avalues =
      List.map (mk_aproj_loans_value_from_symbolic_value abs.regions) input_svs
    in
    (ctx, avalues)
  in
  let region_can_end _ = true in
  let ctx =
    create_push_abstractions_from_abs_region_groups
      (fun rg_id -> V.SynthInput rg_id)
      inst_sg.A.regions_hierarchy region_can_end compute_abs_avalues ctx
  in
  (* Split the variables between return var, inputs and remaining locals *)
  let body = Option.get fdef.body in
  let ret_var = List.hd body.locals in
  let input_vars, local_vars =
    Collections.List.split_at (List.tl body.locals) body.arg_count
  in
  (* Push the return variable (initialized with ⊥) *)
  let ctx = C.ctx_push_uninitialized_var ctx ret_var in
  (* Push the input variables (initialized with symbolic values) *)
  let input_values = List.map mk_typed_value_from_symbolic_value input_svs in
  let ctx = C.ctx_push_vars ctx (List.combine input_vars input_values) in
  (* Push the remaining local variables (initialized with ⊥) *)
  let ctx = C.ctx_push_uninitialized_vars ctx local_vars in
  (* Return *)
  (ctx, input_svs, inst_sg)

(** Small helper.

    This is a continuation function called by the symbolic interpreter upon
    reaching the [return] instruction when synthesizing a *backward* function:
    this continuation takes care of doing the proper manipulations to finish
    the synthesis (mostly by ending abstractions).

    [entered_loop]: [true] if we reached the end of the function because we
    (re-)entered a loop (results [EndEnterLoop] and [EndContinue]).

    [inside_loop]: [true] if we are *inside* a loop (result [EndContinue]).
*)
let evaluate_function_symbolic_synthesize_backward_from_return
    (config : C.config) (fdef : A.fun_decl) (inst_sg : A.inst_fun_sig)
    (back_id : T.RegionGroupId.id) (entered_loop : bool) (inside_loop : bool)
    (ctx : C.eval_ctx) : SA.expression option =
  (* We need to instantiate the function signature - to retrieve
   * the return type. Note that it is important to re-generate
   * an instantiation of the signature, so that we use fresh
   * region ids for the return abstractions. *)
  let sg = fdef.signature in
  let type_params = List.map (fun tv -> T.TypeVar tv.T.index) sg.type_params in
  let ret_inst_sg = instantiate_fun_sig type_params sg in
  let ret_rty = ret_inst_sg.output in
  (* Move the return value out of the return variable *)
  let pop_return_value = not entered_loop in
  let cf_pop_frame = pop_frame config pop_return_value in

  (* We need to find the parents regions/abstractions of the region we
   * will end - this will allow us to, first, mark the other return
   * regions as non-endable, and, second, end those parent regions in
   * proper order. *)
  let parent_rgs = list_ancestor_region_groups sg back_id in
  let parent_input_abs_ids =
    T.RegionGroupId.mapi
      (fun rg_id rg ->
        if T.RegionGroupId.Set.mem rg_id parent_rgs then Some rg.T.id else None)
      inst_sg.regions_hierarchy
  in
  let parent_input_abs_ids =
    List.filter_map (fun x -> x) parent_input_abs_ids
  in

  (* Insert the return value in the return abstractions (by applying
   * borrow projections) *)
  let cf_consume_ret (ret_value : V.typed_value option) ctx =
    let ctx =
      if not entered_loop then (
        let ret_value = Option.get ret_value in
        let compute_abs_avalues (abs : V.abs) (ctx : C.eval_ctx) :
            C.eval_ctx * V.typed_avalue list =
          let ctx, avalue =
            apply_proj_borrows_on_input_value config ctx abs.regions
              abs.ancestors_regions ret_value ret_rty
          in
          (ctx, [ avalue ])
        in

        (* Initialize and insert the abstractions in the context.
         *
         * We take care of allowing to end only the regions which should end (note
         * that this is important for soundness: this is part of the borrow checking).
         * Also see the documentation of the [can_end] field of [abs] for more
         * information. *)
        let parent_and_current_rgs =
          T.RegionGroupId.Set.add back_id parent_rgs
        in
        let region_can_end rid =
          T.RegionGroupId.Set.mem rid parent_and_current_rgs
        in
        assert (region_can_end back_id);
        let ctx =
          create_push_abstractions_from_abs_region_groups
            (fun rg_id -> V.SynthRet rg_id)
            ret_inst_sg.A.regions_hierarchy region_can_end compute_abs_avalues
            ctx
        in
        ctx)
      else ctx
    in

    (* Set the proper loop abstractions as endable *)
    let ctx =
      let visit_loop_abs =
        object
          inherit [_] C.map_eval_ctx

          method! visit_abs _ abs =
            match abs.kind with
            | V.Loop (_, rg_id', _) ->
                let rg_id' = Option.get rg_id' in
                if rg_id' = back_id then { abs with can_end = true } else abs
            | _ -> abs
        end
      in
      visit_loop_abs#visit_eval_ctx () ctx
    in

    (* We now need to end the proper *input* abstractions - pay attention
     * to the fact that we end the *input* abstractions, not the *return*
     * abstractions (of course, the corresponding return abstractions will
     * automatically be ended, because they consumed values coming from the
     * input abstractions...) *)
    (* End the parent abstractions and the current abstraction - note that we
     * end them in an order which follows the regions hierarchy: it should lead
     * to generated code which has a better consistency between the parent
     * and children backward functions.
     *
     * Note that we don't end the same abstraction if we are *inside* a loop (i.e.,
     * we are evaluating an [EndContinue]) or not.
     *)
    let current_abs_id =
      if not inside_loop then
        (T.RegionGroupId.nth inst_sg.regions_hierarchy back_id).id
      else
        let pred (abs : V.abs) =
          match abs.kind with
          | V.Loop (_, rg_id', kind) ->
              let rg_id' = Option.get rg_id' in
              let is_ret =
                match kind with
                | V.LoopSynthInput -> true
                | V.LoopSynthRet -> false
              in
              rg_id' = back_id && is_ret
          | _ -> false
        in
        let abs = Option.get (C.ctx_find_abs ctx pred) in
        abs.abs_id
    in
    let target_abs_ids = List.append parent_input_abs_ids [ current_abs_id ] in
    let cf_end_target_abs cf =
      List.fold_left
        (fun cf id -> end_abstraction config id cf)
        cf target_abs_ids
    in
    (* Generate the Return node *)
    let cf_return : m_fun = fun ctx -> Some (SA.Return (ctx, None)) in
    (* Apply *)
    cf_end_target_abs cf_return ctx
  in
  cf_pop_frame cf_consume_ret ctx

(** Evaluate a function with the symbolic interpreter.

    We return:
    - the list of symbolic values introduced for the input values (this is useful
      for the synthesis)
    - the symbolic AST generated by the symbolic execution
 *)
let evaluate_function_symbolic (synthesize : bool)
    (type_context : C.type_context) (fun_context : C.fun_context)
    (global_context : C.global_context) (fdef : A.fun_decl) :
    V.symbolic_value list * SA.expression option =
  (* Debug *)
  let name_to_string () = Print.fun_name_to_string fdef.A.name in
  log#ldebug (lazy ("evaluate_function_symbolic: " ^ name_to_string ()));

  (* Create the evaluation context *)
  let ctx, input_svs, inst_sg =
    initialize_symbolic_context_for_fun type_context fun_context global_context
      fdef
  in

  (* Create the continuation to finish the evaluation *)
  let config = C.mk_config C.SymbolicMode in
  let cf_finish res ctx =
    log#ldebug
      (lazy
        ("evaluate_function_symbolic: cf_finish: "
        ^ Cps.show_statement_eval_res res));

    match res with
    | Return | LoopReturn ->
        if synthesize then
          (* We have to "play different endings":
           * - one execution for the forward function
           * - one execution per backward function
           * We then group everything together.
           *)
          (* There are two cases:
           * - if this is a forward translation, we retrieve the returned value.
           * - if this is a backward translation, we introduce "return"
           *   abstractions to consume the return value, then end all the
           *   abstractions up to the one in which we are interested.
           *)
          (* Forward translation: retrieve the returned value *)
          let fwd_e =
            (* Pop the frame and retrieve the returned value at the same time*)
            let pop_return_value = true in
            let cf_pop = pop_frame config pop_return_value in
            (* Generate the Return node *)
            let cf_return ret_value : m_fun =
             fun ctx -> Some (SA.Return (ctx, ret_value))
            in
            (* Apply *)
            cf_pop cf_return ctx
          in
          let fwd_e = Option.get fwd_e in
          (* Backward translation: introduce "return"
             abstractions to consume the return value, then end all the
             abstractions up to the one in which we are interested.
          *)
          let entered_loop = false in
          let inside_loop =
            match res with
            | Return -> false
            | LoopReturn -> true
            | _ -> raise (Failure "Unreachable")
          in
          let finish_back_eval back_id =
            Option.get
              (evaluate_function_symbolic_synthesize_backward_from_return config
                 fdef inst_sg back_id entered_loop inside_loop ctx)
          in
          let back_el =
            T.RegionGroupId.mapi
              (fun gid _ -> (gid, finish_back_eval gid))
              fdef.signature.regions_hierarchy
          in
          let back_el = T.RegionGroupId.Map.of_list back_el in
          (* Put everything together *)
          S.synthesize_forward_end None fwd_e back_el
        else None
    | EndEnterLoop loop_input_values | EndContinue loop_input_values ->
        (* Similar to [Return]: we have to play different endings *)
        if synthesize then
          (* Forward translation *)
          let fwd_e =
            (* Pop the frame - there is no returned value to pop: in the
               translation we will simply call the loop function *)
            let pop_return_value = false in
            let cf_pop = pop_frame config pop_return_value in
            (* Generate the Return node *)
            let cf_return _ret_value : m_fun =
             fun ctx -> Some (SA.Return (ctx, None))
            in
            (* Apply *)
            cf_pop cf_return ctx
          in
          let fwd_e = Option.get fwd_e in
          (* Backward translation: introduce "return"
             abstractions to consume the return value, then end all the
             abstractions up to the one in which we are interested.
          *)
          let entered_loop = true in
          let inside_loop =
            match res with
            | EndEnterLoop _ -> false
            | EndContinue _ -> true
            | _ -> raise (Failure "Unreachable")
          in
          let finish_back_eval back_id =
            Option.get
              (evaluate_function_symbolic_synthesize_backward_from_return config
                 fdef inst_sg back_id entered_loop inside_loop ctx)
          in
          let back_el =
            T.RegionGroupId.mapi
              (fun gid _ -> (gid, finish_back_eval gid))
              fdef.signature.regions_hierarchy
          in
          let back_el = T.RegionGroupId.Map.of_list back_el in
          (* Put everything together *)
          S.synthesize_forward_end (Some loop_input_values) fwd_e back_el
        else None
    | Panic ->
        (* Note that as we explore all the execution branches, one of
         * the executions can lead to a panic *)
        if synthesize then Some SA.Panic else None
    | Unit | Break _ | Continue _ ->
        raise
          (Failure ("evaluate_function_symbolic failed on: " ^ name_to_string ()))
  in

  (* Evaluate the function *)
  let symbolic =
    eval_function_body config (Option.get fdef.A.body).body cf_finish ctx
  in

  (* Return *)
  (input_svs, symbolic)

module Test = struct
  (** Test a unit function (taking no arguments) by evaluating it in an empty
      environment.
   *)
  let test_unit_function (crate : A.crate) (fid : A.FunDeclId.id) : unit =
    (* Retrieve the function declaration *)
    let fdef = A.FunDeclId.nth crate.functions fid in
    let body = Option.get fdef.body in

    (* Debug *)
    log#ldebug
      (lazy ("test_unit_function: " ^ Print.fun_name_to_string fdef.A.name));

    (* Sanity check - *)
    assert (List.length fdef.A.signature.region_params = 0);
    assert (List.length fdef.A.signature.type_params = 0);
    assert (body.A.arg_count = 0);

    (* Create the evaluation context *)
    let type_context, fun_context, global_context =
      compute_type_fun_global_contexts crate
    in
    let ctx =
      initialize_eval_context type_context fun_context global_context [] []
    in

    (* Insert the (uninitialized) local variables *)
    let ctx = C.ctx_push_uninitialized_vars ctx body.A.locals in

    (* Create the continuation to check the function's result *)
    let config = C.mk_config C.ConcreteMode in
    let cf_check res ctx =
      match res with
      | Return ->
          (* Ok: drop the local variables and finish *)
          let pop_return_value = true in
          pop_frame config pop_return_value (fun _ _ -> None) ctx
      | _ ->
          raise
            (Failure
               ("Unit test failed (concrete execution) on: "
               ^ Print.fun_name_to_string fdef.A.name))
    in

    (* Evaluate the function *)
    let _ = eval_function_body config body.body cf_check ctx in
    ()

  (** Small helper: return true if the function is a *transparent* unit function
      (no parameters, no arguments) - TODO: move *)
  let fun_decl_is_transparent_unit (def : A.fun_decl) : bool =
    match def.body with
    | None -> false
    | Some body ->
        body.arg_count = 0
        && List.length def.A.signature.region_params = 0
        && List.length def.A.signature.type_params = 0
        && List.length def.A.signature.inputs = 0

  (** Test all the unit functions in a list of function definitions *)
  let test_unit_functions (crate : A.crate) : unit =
    let unit_funs = List.filter fun_decl_is_transparent_unit crate.functions in
    let test_unit_fun (def : A.fun_decl) : unit =
      test_unit_function crate def.A.def_id
    in
    List.iter test_unit_fun unit_funs

  (** Execute the symbolic interpreter on a function. *)
  let test_function_symbolic (synthesize : bool) (type_context : C.type_context)
      (fun_context : C.fun_context) (global_context : C.global_context)
      (fdef : A.fun_decl) : unit =
    (* Debug *)
    log#ldebug
      (lazy ("test_function_symbolic: " ^ Print.fun_name_to_string fdef.A.name));

    (* Evaluate *)
    let _ =
      evaluate_function_symbolic synthesize type_context fun_context
        global_context fdef
    in

    ()

  (** Small helper *)
  let fun_decl_is_transparent (def : A.fun_decl) : bool =
    Option.is_some def.body

  (** Execute the symbolic interpreter on a list of functions.

      TODO: for now we ignore the functions which contain loops, because
      they are not supported by the symbolic interpreter.
   *)
  let test_functions_symbolic (synthesize : bool) (crate : A.crate) : unit =
    (* Filter the functions which contain loops *)
    let no_loop_funs =
      List.filter
        (fun f -> not (LlbcAstUtils.fun_decl_has_loops f))
        crate.functions
    in
    (* Filter the opaque functions *)
    let no_loop_funs = List.filter fun_decl_is_transparent no_loop_funs in
    let type_context, fun_context, global_context =
      compute_type_fun_global_contexts crate
    in
    let test_fun (def : A.fun_decl) : unit =
      (* Execute the function - note that as the symbolic interpreter explores
       * all the path, some executions are expected to "panic": we thus don't
       * check the return value *)
      test_function_symbolic synthesize type_context fun_context global_context
        def
    in
    List.iter test_fun no_loop_funs
end
