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

let compute_contexts (m : A.crate) : C.decls_ctx =
  let type_decls_list, _, _, _, _ = split_declarations m.declarations in
  let type_decls = m.types in
  let fun_decls = m.functions in
  let global_decls = m.globals in
  let trait_decls = m.trait_decls in
  let trait_impls = m.trait_impls in
  let type_decls_groups, _, _, _, _ =
    split_declarations_to_group_maps m.declarations
  in
  let type_infos =
    TypesAnalysis.analyze_type_declarations type_decls type_decls_list
  in
  let type_ctx = { C.type_decls_groups; type_decls; type_infos } in
  let fun_infos =
    FunsAnalysis.analyze_module m fun_decls global_decls !Config.use_state
  in
  let fun_ctx = { C.fun_decls; fun_infos } in
  let global_ctx = { C.global_decls } in
  let trait_decls_ctx = { C.trait_decls } in
  let trait_impls_ctx = { C.trait_impls } in
  { C.type_ctx; fun_ctx; global_ctx; trait_decls_ctx; trait_impls_ctx }

(** Small helper.

    Normalize an instantiated function signature provided we used this signature
    to compute a normalization map (for the associated types) and that we added
    it in the context.
 *)
let normalize_inst_fun_sig (ctx : C.eval_ctx) (sg : A.inst_fun_sig) :
    A.inst_fun_sig =
  let { A.regions_hierarchy = _; trait_type_constraints = _; inputs; output } =
    sg
  in
  let norm = AssociatedTypes.ctx_normalize_ty ctx in
  let inputs = List.map norm inputs in
  let output = norm output in
  { sg with A.inputs; output }

(** Instantiate a function signature for a symbolic execution.

    We return a new context because we compute and add the type normalization
    map in the same step.

    **WARNING**: this doesn't normalize the types. This step has to be done
    separately. Remark: we need to normalize essentially because of the where
    clauses (we are not considering a function call, so we don't need to
    normalize because a trait clause was instantiated with a specific trait ref).
 *)
let symbolic_instantiate_fun_sig (ctx : C.eval_ctx) (sg : A.fun_sig)
    (kind : A.fun_kind) : C.eval_ctx * A.inst_fun_sig =
  let tr_self =
    match kind with
    | RegularKind | TraitMethodImpl _ -> T.UnknownTrait __FUNCTION__
    | TraitMethodDecl _ | TraitMethodProvided _ -> T.Self
  in
  let generics =
    let { T.regions; types; const_generics; trait_clauses } = sg.generics in
    let regions = List.map (fun _ -> T.RErased) regions in
    let types = List.map (fun (v : T.type_var) -> T.TypeVar v.T.index) types in
    let const_generics =
      List.map
        (fun (v : T.const_generic_var) -> T.CGVar v.T.index)
        const_generics
    in
    (* Annoying that we have to generate this substitution here *)
    let r_subst _ = raise (Failure "Unexpected region") in
    let ty_subst = Subst.make_type_subst_from_vars sg.generics.types types in
    let cg_subst =
      Subst.make_const_generic_subst_from_vars sg.generics.const_generics
        const_generics
    in
    (* TODO: some clauses may use the types of other clauses, so we may have to
       reorder them.

       Example:
       If in Rust we write:
       {[
         pub fn use_get<'a, T: Get>(x: &'a mut T) -> u32
         where
             T::Item: ToU32,
         {
             x.get().to_u32()
         }
       ]}

       In LLBC we get:
       {[
         fn demo::use_get<'a, T>(@1: &'a mut (T)) -> u32
         where
             [@TraitClause0]: demo::Get<T>,
             [@TraitClause1]: demo::ToU32<@TraitClause0::Item>, // HERE
         {
             ... // Omitted
         }
       ]}
    *)
    (* We will need to update the trait refs map while we perform the instantiations *)
    let mk_tr_subst (tr_map : T.trait_instance_id T.TraitClauseId.Map.t)
        clause_id : T.trait_instance_id =
      match T.TraitClauseId.Map.find_opt clause_id tr_map with
      | Some tr -> tr
      | None -> raise (Failure "Local trait clause not found")
    in
    let mk_subst tr_map =
      let tr_subst = mk_tr_subst tr_map in
      { Subst.r_subst; ty_subst; cg_subst; tr_subst; tr_self }
    in
    let _, trait_refs =
      List.fold_left_map
        (fun tr_map (c : T.trait_clause) ->
          let subst = mk_subst tr_map in
          let { T.trait_id = trait_decl_id; generics; _ } = c in
          let generics = Subst.generic_args_substitute subst generics in
          let trait_decl_ref = { T.trait_decl_id; decl_generics = generics } in
          (* Note that because we directly refer to the clause, we give it
             empty generics *)
          let trait_id = T.Clause c.clause_id in
          let trait_ref =
            {
              T.trait_id;
              generics = TypesUtils.mk_empty_generic_args;
              trait_decl_ref;
            }
          in
          (* Update the traits map *)
          let tr_map = T.TraitClauseId.Map.add c.T.clause_id trait_id tr_map in
          (tr_map, trait_ref))
        T.TraitClauseId.Map.empty trait_clauses
    in
    { T.regions; types; const_generics; trait_refs }
  in
  let inst_sg = instantiate_fun_sig ctx generics tr_self sg in
  (* Compute the normalization maps *)
  let ctx =
    AssociatedTypes.ctx_add_norm_trait_types_from_preds ctx
      inst_sg.trait_type_constraints
  in
  (* Normalize the signature *)
  let inst_sg = normalize_inst_fun_sig ctx inst_sg in
  (* Return *)
  (ctx, inst_sg)

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
let initialize_symbolic_context_for_fun (ctx : C.decls_ctx) (fdef : A.fun_decl)
    : C.eval_ctx * V.symbolic_value list * A.inst_fun_sig =
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
    List.map (fun (g : T.region_group) -> g.id) sg.regions_hierarchy
  in
  let ctx =
    initialize_eval_context ctx region_groups sg.generics.types
      sg.generics.const_generics
  in
  (* Instantiate the signature. This updates the context because we compute
     at the same time the normalization map for the associated types.
  *)
  let ctx, inst_sg =
    symbolic_instantiate_fun_sig ctx fdef.signature fdef.kind
  in
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
  let region_can_end _ = false in
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

    [is_regular_return]: [true] if we reached a [Return] instruction (i.e., the
    result is {!constructor:Cps.statement_eval_res.Return} or {!constructor:Cps.statement_eval_res.LoopReturn}).

    [inside_loop]: [true] if we are *inside* a loop (result [EndContinue]).
*)
let evaluate_function_symbolic_synthesize_backward_from_return
    (config : C.config) (fdef : A.fun_decl) (inst_sg : A.inst_fun_sig)
    (back_id : T.RegionGroupId.id) (loop_id : V.LoopId.id option)
    (is_regular_return : bool) (inside_loop : bool) (ctx : C.eval_ctx) :
    SA.expression option =
  log#ldebug
    (lazy
      ("evaluate_function_symbolic_synthesize_backward_from_return:"
     ^ "\n- fname: "
      ^ Print.fun_name_to_string fdef.name
      ^ "\n- back_id: "
      ^ T.RegionGroupId.to_string back_id
      ^ "\n- loop_id: "
      ^ Print.option_to_string V.LoopId.to_string loop_id
      ^ "\n- is_regular_return: "
      ^ Print.bool_to_string is_regular_return
      ^ "\n- inside_loop: "
      ^ Print.bool_to_string inside_loop
      ^ "\n- ctx:\n"
      ^ Print.Contexts.eval_ctx_to_string ctx));
  (* We need to instantiate the function signature - to retrieve
   * the return type. Note that it is important to re-generate
   * an instantiation of the signature, so that we use fresh
   * region ids for the return abstractions. *)
  let sg = fdef.signature in
  let _, ret_inst_sg =
    symbolic_instantiate_fun_sig ctx fdef.signature fdef.kind
  in
  let ret_rty = ret_inst_sg.output in
  (* Move the return value out of the return variable *)
  let pop_return_value = is_regular_return in
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
      if is_regular_return then (
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
    let current_abs_id, end_fun_synth_input =
      let fun_abs_id =
        (T.RegionGroupId.nth inst_sg.regions_hierarchy back_id).id
      in
      if not inside_loop then (fun_abs_id, true)
      else
        let pred (abs : V.abs) =
          match abs.kind with
          | V.Loop (_, rg_id', kind) ->
              let rg_id' = Option.get rg_id' in
              let is_ret =
                match kind with V.LoopSynthInput -> true | V.LoopCall -> false
              in
              rg_id' = back_id && is_ret
          | _ -> false
        in
        (* There is not necessarily an input synthesis abstraction specifically
           for the loop.
           If there is none, the input synthesis abstraction is actually the
           function input synthesis abstraction.

           Example:
           ========
           {[
             fn clear(v: &mut Vec<u32>) {
                 let mut i = 0;
                 while i < v.len() {
                     v[i] = 0;
                     i += 1;
                 }
             }
           ]}
        *)
        let abs = Option.get (C.ctx_find_abs ctx pred) in
        (abs.abs_id, false)
    in
    log#ldebug
      (lazy
        ("evaluate_function_symbolic_synthesize_backward_from_return: ending \
          input abstraction: "
        ^ V.AbstractionId.to_string current_abs_id));

    (* Set the proper abstractions as endable *)
    let ctx =
      let visit_loop_abs =
        object
          inherit [_] C.map_eval_ctx

          method! visit_abs _ abs =
            match abs.kind with
            | V.Loop (loop_id', rg_id', V.LoopSynthInput) ->
                (* We only allow to end the loop synth input abs for the region
                   group [rg_id] *)
                assert (
                  if Option.is_some loop_id then loop_id = Some loop_id'
                  else true);
                (* Loop abstractions *)
                let rg_id' = Option.get rg_id' in
                if rg_id' = back_id && inside_loop then
                  { abs with can_end = true }
                else abs
            | V.Loop (loop_id', _, V.LoopCall) ->
                (* We can end all the loop call abstractions *)
                assert (loop_id = Some loop_id');
                { abs with can_end = true }
            | V.SynthInput rg_id' ->
                if rg_id' = back_id && end_fun_synth_input then
                  { abs with can_end = true }
                else abs
            | _ ->
                (* Other abstractions *)
                abs
        end
      in
      visit_loop_abs#visit_eval_ctx () ctx
    in

    let target_abs_ids = List.append parent_input_abs_ids [ current_abs_id ] in
    let cf_end_target_abs cf =
      List.fold_left
        (fun cf id -> end_abstraction config id cf)
        cf target_abs_ids
    in
    (* Generate the Return node *)
    let cf_return : m_fun =
     fun ctx ->
      match loop_id with
      | None -> Some (SA.Return (ctx, None))
      | Some loop_id -> Some (SA.ReturnWithLoop (loop_id, inside_loop))
    in
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
let evaluate_function_symbolic (synthesize : bool) (ctx : C.decls_ctx)
    (fdef : A.fun_decl) : V.symbolic_value list * SA.expression option =
  (* Debug *)
  let name_to_string () = Print.fun_name_to_string fdef.A.name in
  log#ldebug (lazy ("evaluate_function_symbolic: " ^ name_to_string ()));

  (* Create the evaluation context *)
  let ctx, input_svs, inst_sg = initialize_symbolic_context_for_fun ctx fdef in

  (* Create the continuation to finish the evaluation *)
  let config = C.mk_config C.SymbolicMode in
  let cf_finish res ctx =
    let ctx0 = ctx in
    log#ldebug
      (lazy
        ("evaluate_function_symbolic: cf_finish: "
        ^ Cps.show_statement_eval_res res));

    match res with
    | Return | LoopReturn _ ->
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
          let loop_id =
            match res with
            | Return -> None
            | LoopReturn loop_id -> Some loop_id
            | _ -> raise (Failure "Unreachable")
          in
          let is_regular_return = true in
          let inside_loop = Option.is_some loop_id in
          let finish_back_eval back_id =
            Option.get
              (evaluate_function_symbolic_synthesize_backward_from_return config
                 fdef inst_sg back_id loop_id is_regular_return inside_loop ctx)
          in
          let back_el =
            T.RegionGroupId.mapi
              (fun gid _ -> (gid, finish_back_eval gid))
              fdef.signature.regions_hierarchy
          in
          let back_el = T.RegionGroupId.Map.of_list back_el in
          (* Put everything together *)
          S.synthesize_forward_end ctx0 None fwd_e back_el
        else None
    | EndEnterLoop (loop_id, loop_input_values)
    | EndContinue (loop_id, loop_input_values) ->
        (* Similar to [Return]: we have to play different endings *)
        if synthesize then
          let inside_loop =
            match res with
            | EndEnterLoop _ -> false
            | EndContinue _ -> true
            | _ -> raise (Failure "Unreachable")
          in
          (* Forward translation *)
          let fwd_e =
            (* Pop the frame - there is no returned value to pop: in the
               translation we will simply call the loop function *)
            let pop_return_value = false in
            let cf_pop = pop_frame config pop_return_value in
            (* Generate the Return node *)
            let cf_return _ret_value : m_fun =
             fun _ctx -> Some (SA.ReturnWithLoop (loop_id, inside_loop))
            in
            (* Apply *)
            cf_pop cf_return ctx
          in
          let fwd_e = Option.get fwd_e in
          (* Backward translation: introduce "return"
             abstractions to consume the return value, then end all the
             abstractions up to the one in which we are interested.
          *)
          let is_regular_return = false in
          let finish_back_eval back_id =
            Option.get
              (evaluate_function_symbolic_synthesize_backward_from_return config
                 fdef inst_sg back_id (Some loop_id) is_regular_return
                 inside_loop ctx)
          in
          let back_el =
            T.RegionGroupId.mapi
              (fun gid _ -> (gid, finish_back_eval gid))
              fdef.signature.regions_hierarchy
          in
          let back_el = T.RegionGroupId.Map.of_list back_el in
          (* Put everything together *)
          S.synthesize_forward_end ctx0 (Some loop_input_values) fwd_e back_el
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
  let test_unit_function (crate : A.crate) (decls_ctx : C.decls_ctx)
      (fid : A.FunDeclId.id) : unit =
    (* Retrieve the function declaration *)
    let fdef = A.FunDeclId.Map.find fid crate.functions in
    let body = Option.get fdef.body in

    (* Debug *)
    log#ldebug
      (lazy ("test_unit_function: " ^ Print.fun_name_to_string fdef.A.name));

    (* Sanity check - *)
    assert (fdef.A.signature.generics = TypesUtils.mk_empty_generic_params);
    assert (body.A.arg_count = 0);

    (* Create the evaluation context *)
    let ctx = initialize_eval_context decls_ctx [] [] [] in

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
    Option.is_some def.body
    && def.A.signature.generics = TypesUtils.mk_empty_generic_params
    && def.A.signature.inputs = []

  (** Test all the unit functions in a list of function definitions *)
  let test_unit_functions (crate : A.crate) : unit =
    let unit_funs =
      A.FunDeclId.Map.filter
        (fun _ -> fun_decl_is_transparent_unit)
        crate.functions
    in
    let decls_ctx = compute_contexts crate in
    let test_unit_fun _ (def : A.fun_decl) : unit =
      test_unit_function crate decls_ctx def.A.def_id
    in
    A.FunDeclId.Map.iter test_unit_fun unit_funs
end
