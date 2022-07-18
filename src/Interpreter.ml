open Cps
open InterpreterUtils
open InterpreterProjectors
open InterpreterBorrows
open InterpreterStatements
open LlbcAstUtils
module L = Logging
module T = Types
module A = LlbcAst
module M = Modules
module SA = SymbolicAst

(** The local logger *)
let log = L.interpreter_log

let compute_type_fun_contexts (m : M.llbc_module) :
    C.type_context * C.fun_context * C.global_context =
  let type_decls_list, _ = M.split_declarations m.declarations in
  let type_decls, fun_decls, global_decls = M.compute_defs_maps m in
  let type_decls_groups, _funs_defs_groups =
    M.split_declarations_to_group_maps m.declarations
  in
  let type_infos =
    TypesAnalysis.analyze_type_declarations type_decls type_decls_list
  in
  let type_context = { C.type_decls_groups; type_decls; type_infos } in
  let fun_context = { C.fun_decls } in
  let global_context = { C.global_decls } in
  (type_context, fun_context, global_context)

let initialize_eval_context
    (type_context : C.type_context)
    (fun_context : C.fun_context)
    (global_context : C.global_context)
    (type_vars : T.type_var list) : C.eval_ctx =
  C.reset_global_counters ();
  {
    C.type_context;
    C.fun_context;
    C.global_context;
    C.type_vars;
    C.env = [ C.Frame ];
    C.ended_regions = T.RegionId.Set.empty;
  }

(** Initialize an evaluation context to execute a function.

      Introduces local variables initialized in the following manner:
      - input arguments are initialized as symbolic values
      - the remaining locals are initialized as ⊥
      Abstractions are introduced for the regions present in the function
      signature.
      
      We return:
      - the initialized evaluation context
      - the list of symbolic values introduced for the input values
      - the instantiated function signature
 *)
let initialize_symbolic_context_for_fun
    (type_context : C.type_context)
    (fun_context : C.fun_context)
    (global_context : C.global_context)
    (fdef : A.fun_decl) :
    C.eval_ctx * V.symbolic_value list * A.inst_fun_sig =
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
  let ctx = initialize_eval_context type_context fun_context global_context sg.type_params in
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
    create_push_abstractions_from_abs_region_groups call_id V.SynthInput
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
    reaching the `return` instruction when synthesizing a *backward* function:
    this continuation takes care of doing the proper manipulations to finish
    the synthesis (mostly by ending abstractions).
*)
let evaluate_function_symbolic_synthesize_backward_from_return
    (config : C.config) (fdef : A.fun_decl) (inst_sg : A.inst_fun_sig)
    (back_id : T.RegionGroupId.id) (ctx : C.eval_ctx) : SA.expression option =
  (* We need to instantiate the function signature - to retrieve
   * the return type. Note that it is important to re-generate
   * an instantiation of the signature, so that we use fresh
   * region ids for the return abstractions. *)
  let sg = fdef.signature in
  let type_params = List.map (fun tv -> T.TypeVar tv.T.index) sg.type_params in
  let ret_inst_sg = instantiate_fun_sig type_params sg in
  let ret_rty = ret_inst_sg.output in
  (* Move the return value out of the return variable *)
  let cf_pop_frame = ctx_pop_frame config in

  (* We need to find the parents regions/abstractions of the region we
   * will end - this will allow us to, first, mark the other return
   * regions as non-endable, and, second, end those parent regions in
   * proper order. *)
  let parent_rgs = list_parent_region_groups sg back_id in
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
  let cf_consume_ret ret_value ctx =
    let ret_call_id = C.fresh_fun_call_id () in
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
     * We take care of disallowing ending the return regions which we
     * shouldn't end (see the documentation of the `can_end` field of [abs]
     * for more information. *)
    let parent_and_current_rgs = T.RegionGroupId.Set.add back_id parent_rgs in
    let region_can_end rid =
      T.RegionGroupId.Set.mem rid parent_and_current_rgs
    in
    assert (region_can_end back_id);
    let ctx =
      create_push_abstractions_from_abs_region_groups ret_call_id V.SynthRet
        ret_inst_sg.A.regions_hierarchy region_can_end compute_abs_avalues ctx
    in

    (* We now need to end the proper *input* abstractions - pay attention
     * to the fact that we end the *input* abstractions, not the *return*
     * abstractions (of course, the corresponding return abstractions will
     * automatically be ended, because they consumed values coming from the
     * input abstractions...) *)
    (* End the parent abstractions and the current abstraction - note that we
     * end them in an order which follows the regions hierarchy: it should lead
     * to generated code which has a better consistency between the parent
     * and children backward functions *)
    let current_abs_id =
      (T.RegionGroupId.nth inst_sg.regions_hierarchy back_id).id
    in
    let target_abs_ids = List.append parent_input_abs_ids [ current_abs_id ] in
    let cf_end_target_abs cf =
      List.fold_left
        (fun cf id -> end_abstraction config [] id cf)
        cf target_abs_ids
    in
    (* Generate the Return node *)
    let cf_return : m_fun = fun _ -> Some (SA.Return None) in
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
let evaluate_function_symbolic (config : C.partial_config) (synthesize : bool)
    (type_context : C.type_context) (fun_context : C.fun_context) (global_context : C.global_context)
    (fdef : A.fun_decl) (back_id : T.RegionGroupId.id option) :
    V.symbolic_value list * SA.expression option =
  (* Debug *)
  let name_to_string () =
    Print.fun_name_to_string fdef.A.name
    ^ " ("
    ^ Print.option_to_string T.RegionGroupId.to_string back_id
    ^ ")"
  in
  log#ldebug (lazy ("evaluate_function_symbolic: " ^ name_to_string ()));

  (* Create the evaluation context *)
  let ctx, input_svs, inst_sg =
    initialize_symbolic_context_for_fun type_context fun_context global_context fdef
  in

  (* Create the continuation to finish the evaluation *)
  let config = C.config_of_partial C.SymbolicMode config in
  let cf_finish res ctx =
    match res with
    | Return ->
        if synthesize then
          (* There are two cases:
           * - if this is a forward translation, we retrieve the returned value.
           * - if this is a backward translation, we introduce "return"
           *   abstractions to consume the return value, then end all the
           *   abstractions up to the one in which we are interested.
           *)
          match back_id with
          | None ->
              (* Forward translation *)
              (* Pop the frame and retrieve the returned value at the same time*)
              let cf_pop = ctx_pop_frame config in
              (* Generate the Return node *)
              let cf_return ret_value : m_fun =
               fun _ -> Some (SA.Return (Some ret_value))
              in
              (* Apply *)
              cf_pop cf_return ctx
          | Some back_id ->
              (* Backward translation *)
              evaluate_function_symbolic_synthesize_backward_from_return config
                fdef inst_sg back_id ctx
        else None
    | Panic ->
        (* Note that as we explore all the execution branches, one of
         * the executions can lead to a panic *)
        if synthesize then Some SA.Panic else None
    | _ ->
        failwith ("evaluate_function_symbolic failed on: " ^ name_to_string ())
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
  let test_unit_function (config : C.partial_config) (m : M.llbc_module)
      (fid : A.FunDeclId.id) : unit =
    (* Retrieve the function declaration *)
    let fdef = A.FunDeclId.nth m.functions fid in
    let body = Option.get fdef.body in

    (* Debug *)
    log#ldebug
      (lazy ("test_unit_function: " ^ Print.fun_name_to_string fdef.A.name));

    (* Sanity check - *)
    assert (List.length fdef.A.signature.region_params = 0);
    assert (List.length fdef.A.signature.type_params = 0);
    assert (body.A.arg_count = 0);

    (* Create the evaluation context *)
    let type_context, fun_context, global_context = compute_type_fun_contexts m in
    let ctx = initialize_eval_context type_context fun_context global_context [] in

    (* Insert the (uninitialized) local variables *)
    let ctx = C.ctx_push_uninitialized_vars ctx body.A.locals in

    (* Create the continuation to check the function's result *)
    let config = C.config_of_partial C.ConcreteMode config in
    let cf_check res ctx =
      match res with
      | Return ->
          (* Ok: drop the local variables and finish *)
          ctx_pop_frame config (fun _ _ -> None) ctx
      | _ ->
          failwith
            ("Unit test failed (concrete execution) on: "
            ^ Print.fun_name_to_string fdef.A.name)
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
  let test_unit_functions (config : C.partial_config) (m : M.llbc_module) : unit
      =
    let unit_funs = List.filter fun_decl_is_transparent_unit m.functions in
    let test_unit_fun (def : A.fun_decl) : unit =
      test_unit_function config m def.A.def_id
    in
    List.iter test_unit_fun unit_funs

  (** Execute the symbolic interpreter on a function. *)
  let test_function_symbolic (config : C.partial_config) (synthesize : bool)
      (type_context : C.type_context) (fun_context : C.fun_context) (global_context : C.global_context)
      (fdef : A.fun_decl) : unit =
    (* Debug *)
    log#ldebug
      (lazy ("test_function_symbolic: " ^ Print.fun_name_to_string fdef.A.name));

    (* Evaluate *)
    let evaluate =
      evaluate_function_symbolic config synthesize type_context fun_context global_context fdef
    in
    (* Execute the forward function *)
    let _ = evaluate None in
    (* Execute the backward functions *)
    let _ =
      T.RegionGroupId.mapi
        (fun gid _ -> evaluate (Some gid))
        fdef.signature.regions_hierarchy
    in

    ()

  (** Small helper *)
  let fun_decl_is_transparent (def : A.fun_decl) : bool =
    Option.is_some def.body

  (** Execute the symbolic interpreter on a list of functions.

      TODO: for now we ignore the functions which contain loops, because
      they are not supported by the symbolic interpreter.
   *)
  let test_functions_symbolic (config : C.partial_config) (synthesize : bool)
      (m : M.llbc_module) : unit =
    (* Filter the functions which contain loops *)
    let no_loop_funs =
      List.filter (fun f -> not (LlbcAstUtils.fun_decl_has_loops f)) m.functions
    in
    (* Filter the opaque functions *)
    let no_loop_funs = List.filter fun_decl_is_transparent no_loop_funs in
    let type_context, fun_context, global_context = compute_type_fun_contexts m in
    let test_fun (def : A.fun_decl) : unit =
      (* Execute the function - note that as the symbolic interpreter explores
       * all the path, some executions are expected to "panic": we thus don't
       * check the return value *)
      test_function_symbolic config synthesize type_context fun_context global_context def
    in
    List.iter test_fun no_loop_funs
end
