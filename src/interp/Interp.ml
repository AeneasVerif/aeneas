open Cps
open InterpUtils
open InterpProjectors
open InterpBorrows
open InterpStatements
open LlbcAstUtils
open Types
open TypesUtils
open Values
open ValuesUtils
open LlbcAst
open Contexts
open Errors
module SA = SymbolicAst

(** The local logger *)
let log = Logging.interp_log

(** Compute the type information for every *type definition* in a list of
    declarations. This type definition information is later used to easily
    compute the information of arbitrary types.

    Rem.: pay attention to the difference between type definitions and types!
    Rem.: this definition is in Interp.ml and not in TypesAnalysis.ml because
    otherwise we have cyclic dependencies. *)
let analyze_type_declarations (crate : crate)
    (type_decls : type_decl TypeDeclId.Map.t)
    (decls : type_declaration_group list) : TypesAnalysis.type_infos =
  let open TypesAnalysis in
  List.fold_left
    (fun infos decl ->
      try analyze_type_declaration_group type_decls infos decl
      with CFailure error ->
        let fmt_env : Print.fmt_env =
          Charon.PrintLlbcAst.Crate.crate_to_fmt_env crate
        in
        let decls = Charon.GAstUtils.g_declaration_group_to_list decl in
        let decl_id_to_string (id : TypeDeclId.id) : string =
          match TypeDeclId.Map.find_opt id crate.type_decls with
          | None -> show_type_decl_id id
          | Some d ->
              Print.name_to_string fmt_env d.item_meta.name
              ^ " ("
              ^ span_to_string d.item_meta.span
              ^ ")"
        in
        let decls = List.map decl_id_to_string decls in
        let decls = String.concat "\n" decls in
        [%save_error_opt_span] error.span
          ("Encountered an error when analyzing the following type \
            declarations group:\n" ^ decls);
        infos)
    TypeDeclId.Map.empty decls

let compute_contexts (crate : crate) : decls_ctx =
  let type_decls_list, _, _, _, _, _ = split_declarations crate.declarations in
  let fmt_env : Print.fmt_env =
    Charon.PrintLlbcAst.Crate.crate_to_fmt_env crate
  in
  (* Split the declaration groups between the declaration kinds (types, functions, etc.) *)
  let type_decls_groups, _, _, _, _, mixed_groups =
    split_declarations_to_group_maps crate.declarations
  in
  (* Check if there are mixed groups: if there are, we report an error
     and ignore those *)
  (if mixed_groups <> [] then
     (* We detected mixed groups: print a nice error message *)
     let item_id_to_string (id : item_id) : string =
       let kind = item_id_to_kind_name id in
       let meta = LlbcAstUtils.crate_get_item_meta crate id in
       let s =
         match meta with
         | None -> show_item_id id
         | Some meta ->
             kind ^ "(" ^ span_to_string meta.span ^ "): "
             ^ Print.name_to_string fmt_env meta.name
       in
       "- " ^ s
     in
     let group_to_msg (i : int) (g : mixed_declaration_group) : string =
       let ids = g_declaration_group_to_list g in
       let decls = List.map item_id_to_string ids in
       let local_requires =
         LlbcAstUtils.find_local_transitive_dep crate (AnyDeclIdSet.of_list ids)
       in
       let local_requires = List.map span_to_string local_requires in
       let local_requires =
         if local_requires <> [] then
           "\n\n\
            The declarations in this group are (transitively) used at the \
            following location(s):\n"
           ^ String.concat "\n" local_requires
         else ""
       in
       "# Group "
       ^ string_of_int (i + 1)
       ^ ":\n" ^ String.concat "\n" decls ^ local_requires
     in
     let msgs = List.mapi group_to_msg mixed_groups in
     let msgs = String.concat "\n\n" msgs in
     [%save_error_opt_span] None
       ("Detected groups of mixed mutually recursive definitions (such as a \
         type mutually recursive with a function, or a function mutually \
         recursive with a trait implementation):\n\n" ^ msgs));

  let type_decls = crate.type_decls in
  let type_infos = analyze_type_declarations crate type_decls type_decls_list in
  let type_ctx = { type_decls_groups; type_decls; type_infos } in

  let fun_decls = crate.fun_decls in
  let fun_infos = FunsAnalysis.analyze_module crate fun_decls in
  let regions_hierarchies =
    RegionsHierarchy.compute_regions_hierarchies crate
  in
  let fun_ctx = { fun_decls; fun_infos; regions_hierarchies } in

  { crate; type_ctx; fun_ctx }

(** Instantiate a function signature for a symbolic execution.

    We return a new context because we compute and add the type normalization
    map in the same step. *)
let symbolic_instantiate_fun_sig (span : Meta.span) (ctx : eval_ctx)
    (sg : fun_sig) (regions_hierarchy : region_var_groups) (_kind : item_source)
    : eval_ctx * inst_fun_sig =
  let tr_self = UnknownTrait "symbolic_instantiate_fun_sig" in
  let generics =
    Substitute.generic_args_of_params_erase_regions (Some span) sg.generics
  in
  let inst_sg =
    instantiate_fun_sig span ctx generics tr_self sg regions_hierarchy
  in
  (* Return *)
  (ctx, inst_sg)

(** Initialize an evaluation context to execute a function.

    Introduces local variables initialized in the following manner:
    - input arguments are initialized as symbolic values
    - the remaining locals are initialized as [⊥] Abstractions are introduced
      for the regions present in the function signature.

    We return:
    - the initialized evaluation context
    - the list of symbolic values introduced for the input values
    - the instantiated function signature *)
let initialize_symbolic_context_for_fun (ctx : decls_ctx)
    (marked_ids : marked_ids) (fdef : fun_decl) :
    eval_ctx * symbolic_value list * inst_fun_sig =
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
   *)
  let sg = fdef.signature in
  let span = fdef.item_meta.span in
  (* Sanity check: no nested borrows *)
  [%cassert] span
    (List.for_all
       (fun ty ->
         not (ty_has_nested_borrows (Some span) ctx.type_ctx.type_infos ty))
       (sg.output :: sg.inputs))
    "Nested borrows are not supported yet";

  (* Create the context *)
  let regions_hierarchy =
    [%silent_unwrap] fdef.item_meta.span
      (FunIdMap.find_opt (FRegular fdef.def_id) ctx.fun_ctx.regions_hierarchies)
  in
  let region_groups =
    List.map (fun (g : region_var_group) -> g.id) regions_hierarchy
  in
  let ctx =
    initialize_eval_ctx (Some span) ctx region_groups sg.generics.types
      sg.generics.const_generics marked_ids
  in
  (* Instantiate the signature. This updates the context because we compute
     at the same time the normalization map for the associated types.
  *)
  let ctx, inst_sg =
    symbolic_instantiate_fun_sig span ctx fdef.signature regions_hierarchy
      fdef.src
  in
  (* Create fresh symbolic values for the inputs *)
  let input_svs =
    List.map (fun ty -> mk_fresh_symbolic_value span ctx ty) inst_sg.inputs
  in
  (* Initialize the abstractions as empty (i.e., with no avalues) abstractions *)
  let call_id = ctx.fresh_fun_call_id () in
  [%sanity_check] span (call_id = FunCallId.zero);
  let compute_abs_avalues (rg_id : region_group_id) (abs : abs)
      (_ctx : eval_ctx) : tavalue list * abs_cont option =
    (* Project over the values - we use *loan* projectors, as explained above *)
    let avalues =
      List.map
        (fun (sv : symbolic_value) ->
          mk_aproj_loans_value_from_symbolic_value abs.regions.owned sv sv.sv_ty)
        input_svs
    in
    (* The continuation expression *)
    let cont : abs_cont =
      (* We only create an input expression: no output is needed (we're only
         interested in computing *which* values get consumed upon ending a
         lifetime) *)
      let inputs =
        List.map
          (fun (sv : symbolic_value) ->
            mk_eproj_loans_value_from_symbolic_value ctx.type_ctx.type_infos
              abs.regions.owned sv sv.sv_ty)
          input_svs
      in
      (* Note that we don't really care about the type of the input *)
      let input = { value = EApp (EInputAbs rg_id, inputs); ty = mk_unit_ty } in
      { output = None; input = Some input }
    in
    (avalues, Some cont)
  in
  let region_can_end _ = false in
  let ctx =
    create_push_abstractions_from_abs_region_groups
      (fun rg_id -> SynthInput rg_id)
      inst_sg.abs_regions_hierarchy region_can_end compute_abs_avalues ctx
  in
  (* Split the variables between return var, inputs and remaining locals *)
  let body = Option.get fdef.body in
  let ret_var = List.hd body.locals.locals in
  let input_vars, local_vars =
    Collections.List.split_at (List.tl body.locals.locals) body.locals.arg_count
  in
  (* Push the return variable (initialized with ⊥) *)
  let ctx = ctx_push_uninitialized_var span ctx ret_var in
  (* Push the input variables (initialized with symbolic values) *)
  let input_values = List.map mk_tvalue_from_symbolic_value input_svs in
  let ctx = ctx_push_vars span ctx (List.combine input_vars input_values) in
  (* Push the remaining local variables (initialized with ⊥) *)
  let ctx = ctx_push_uninitialized_vars span ctx local_vars in
  (* Return *)
  (ctx, input_svs, inst_sg)

(** Small helper.

    This is a continuation function called by the symbolic interpreter upon
    reaching the [return] instruction when synthesizing a *backward* function:
    this continuation takes care of doing the proper manipulations to finish the
    synthesis (mostly by ending abstractions). *)
let evaluate_function_symbolic_synthesize_backward_from_return (config : config)
    (fdef : fun_decl) (inst_sg : inst_fun_sig) (back_id : RegionGroupId.id)
    (ret_value : tvalue) (ctx : eval_ctx) : SA.expr =
  let span = fdef.item_meta.span in
  [%ltrace
    "- fname: "
    ^ Print.EvalCtx.name_to_string ctx fdef.item_meta.name
    ^ "\n- back_id: "
    ^ RegionGroupId.to_string back_id
    ^ "\n- ctx:\n"
    ^ Print.Contexts.eval_ctx_to_string ~span:(Some span) ctx];
  (* We need to instantiate the function signature - to retrieve
   * the return type. Note that it is important to re-generate
   * an instantiation of the signature, so that we use fresh
   * region ids for the return abstractions. *)
  let regions_hierarchy =
    FunIdMap.find (FRegular fdef.def_id) ctx.fun_ctx.regions_hierarchies
  in
  let _, ret_inst_sg =
    symbolic_instantiate_fun_sig span ctx fdef.signature regions_hierarchy
      fdef.src
  in
  let ret_rty = ret_inst_sg.output in

  (* We need to find the parents regions/abstractions of the region we
     will end - this will allow us to, first, mark the other return
     regions as non-endable, and, second, end those parent regions in
     proper order. *)
  let parent_rgs = list_ancestor_region_groups regions_hierarchy back_id in
  let parent_input_abs_ids =
    RegionGroupId.mapi
      (fun rg_id rg ->
        if RegionGroupId.Set.mem rg_id parent_rgs then Some rg.id else None)
      inst_sg.abs_regions_hierarchy
  in
  let parent_input_abs_ids =
    List.filter_map (fun x -> x) parent_input_abs_ids
  in
  (* TODO: need to be careful for loops *)
  [%sanity_check] fdef.item_meta.span (parent_input_abs_ids = []);

  (* Insert the return value in the return abstractions (by applying
   * borrow projections) *)
  let ctx =
    let compute_abs_avalues (rg_id : region_group_id) (abs : abs)
        (ctx : eval_ctx) : tavalue list * abs_cont option =
      (* Create the abstraction values *)
      let avalue =
        apply_proj_borrows_on_input_value span ctx abs.regions.owned ret_value
          ret_rty
      in
      (* Create the abstraction continuation expression *)
      let cont : abs_cont =
        let output =
          apply_eproj_borrows_on_input_value span ctx abs.regions.owned
            ret_value ret_rty
        in
        let input = EApp (EOutputAbs rg_id, []) in
        let input = { value = input; ty = ret_rty } in
        { output = Some output; input = Some input }
      in
      ([ avalue ], Some cont)
    in

    (* Initialize and insert the abstractions in the context.

         We take care of allowing to end only the regions which should end (note
         that this is important for soundness: this is part of the borrow checking).
         Also see the documentation of the [can_end] field of [abs] for more
         information. *)
    let parent_and_current_rgs = RegionGroupId.Set.add back_id parent_rgs in
    let region_can_end rid = RegionGroupId.Set.mem rid parent_and_current_rgs in
    [%sanity_check] span (region_can_end back_id);
    let ctx =
      create_push_abstractions_from_abs_region_groups
        (fun rg_id -> SynthRet rg_id)
        ret_inst_sg.abs_regions_hierarchy region_can_end compute_abs_avalues ctx
    in
    ctx
  in
  [%ltrace
    "After putting the return value in the proper abstraction:\n" ^ "\n- ctx:\n"
    ^ Print.Contexts.eval_ctx_to_string ~span:(Some span) ctx];

  (* We now need to end the proper *input* abstractions - pay attention
     to the fact that we end the *input* abstractions, not the *return*
     abstractions (of course, the corresponding return abstractions will
     automatically be ended, because they consumed values coming from the
     input abstractions...) *)
  (* End the parent abstractions and the current abstraction - note that we
     end them in an order which follows the regions hierarchy: it should lead
     to generated code which has a better consistency between the parent
     and children backward functions.
   *)
  let current_abs_id =
    (RegionGroupId.nth inst_sg.abs_regions_hierarchy back_id).id
  in
  [%ltrace "ending input abstraction: " ^ AbsId.to_string current_abs_id];

  let target_abs_ids = List.append parent_input_abs_ids [ current_abs_id ] in

  (* Set the abstrations as endable *)
  let ctx = InterpBorrowsCore.update_endable ctx target_abs_ids ~can_end:true in

  (* Actually end them *)
  let ctx, cc =
    fold_left_apply_continuation
      (fun id ctx -> end_abstraction config span id ctx)
      target_abs_ids ctx
  in
  (* Generate the Return node *)
  let return_expr = SA.Return (ctx, None) in
  (* Apply *)
  cc return_expr

(** Evaluate a function with the symbolic interpreter.

    We return:
    - the list of symbolic values introduced for the input values (this is
      useful for the synthesis)
    - the symbolic AST generated by the symbolic execution

    If [synthesize] is [true]: we synthesize the symbolic AST that is used for
    the translation. Otherwise, we do not (the symbolic execution then simply
    borrow-checks the function). *)
let evaluate_function_symbolic (synthesize : bool) (ctx : decls_ctx)
    (marked_ids : marked_ids) (fdef : fun_decl) :
    symbolic_value list * SA.expr option =
  (* Debug *)
  let span = fdef.item_meta.span in
  let name_to_string () =
    Print.Types.name_to_string
      (Print.Contexts.decls_ctx_to_fmt_env ctx)
      fdef.item_meta.name
  in
  [%ltrace name_to_string ()];

  (* Create the evaluation context *)
  let ctx, input_svs, inst_sg =
    initialize_symbolic_context_for_fun ctx marked_ids fdef
  in

  let regions_hierarchy =
    FunIdMap.find (FRegular fdef.def_id) ctx.fun_ctx.regions_hierarchies
  in

  (* Create the continuation to finish the evaluation *)
  let config = mk_config SymbolicMode in
  let finish (res : statement_eval_res) (ctx : eval_ctx) =
    let ctx0 = ctx in
    [%ltrace
      "cf_finish:\n"
      ^ Cps.show_statement_eval_res res
      ^ "\n- ctx:\n" ^ eval_ctx_to_string ctx];

    match res with
    | Return ->
        (* We have to "play different endings":
         * - one execution for the forward function
         * - one execution per backward function
         * We then group everything together.
         *)
        (* There are two cases:
         - if this is a forward translation, we retrieve the returned value.
         - if this is a backward translation, we introduce "return"
           abstractions to consume the return value, then end all the
           abstractions up to the one in which we are interested.
        *)
        (* Whatever the scenario, we need to pop the frame and retrieve the returned value *)
        let ret_value, ctx, cc_pop =
          let pop_return_value = true in
          pop_frame config span pop_return_value ctx
        in
        let ret_value = Option.get ret_value in
        let ctx_return = ctx in

        (* Forward translation: generate the Return node *)
        let fwd_e = cc_pop (SA.Return (ctx, Some ret_value)) in
        (* Backward translation: introduce "return"
           abstractions to consume the return value, then end all the
           abstractions up to the one in which we are interested.
        *)
        let finish_back_eval back_id =
          evaluate_function_symbolic_synthesize_backward_from_return config fdef
            inst_sg back_id ret_value ctx
        in
        let back_el =
          RegionGroupId.mapi
            (fun gid _ -> (gid, cc_pop (finish_back_eval gid)))
            regions_hierarchy
        in
        let back_el = RegionGroupId.Map.of_list back_el in
        (* Put everything together *)
        SA.ForwardEnd (Some (ctx_return, ret_value), ctx0, fwd_e, back_el)
    | Panic ->
        (* Note that as we explore all the execution branches, one of
         * the executions can lead to a panic *)
        SA.Panic
    | Unit | Break _ | Continue _ ->
        [%craise] span
          ("evaluate_function_symbolic failed on: " ^ name_to_string ())
  in

  (* Evaluate the function *)
  let symbolic =
    try
      let ctx_resl, cc =
        eval_function_body config (Option.get fdef.body).body ctx
      in
      let el = List.map (fun (ctx, res) -> finish res ctx) ctx_resl in
      (* Finish synthesizing *)
      if synthesize then Some (cc el) else None
    with CFailure error ->
      if synthesize then Some (Error (error.span, error.msg)) else None
  in
  (* Return *)
  (input_svs, symbolic)

module Test = struct
  (** Test a unit function (taking no arguments) by evaluating it in an empty
      environment. *)
  let test_unit_function (crate : crate) (decls_ctx : decls_ctx)
      (fid : FunDeclId.id) : unit =
    (* Retrieve the function declaration *)
    let fdef = FunDeclId.Map.find fid crate.fun_decls in
    let body = Option.get fdef.body in
    let span = fdef.item_meta.span in

    (* Debug *)
    [%ltrace
      Print.Types.name_to_string
        (Print.Contexts.decls_ctx_to_fmt_env decls_ctx)
        fdef.item_meta.name];

    (* Sanity check - *)
    [%sanity_check] span (fdef.signature.generics = empty_generic_params);
    [%sanity_check] span (body.locals.arg_count = 0);

    (* Create the evaluation context *)
    let ctx =
      initialize_eval_ctx (Some span) decls_ctx [] [] [] empty_marked_ids
    in

    (* Insert the (uninitialized) local variables *)
    let ctx = ctx_push_uninitialized_vars span ctx body.locals.locals in

    (* Create the continuation to check the function's result *)
    let config = mk_config ConcreteMode in
    let check (res : statement_eval_res) (ctx : eval_ctx) =
      match res with
      | Return ->
          (* Ok: drop the local variables and finish *)
          let pop_return_value = true in
          pop_frame config span pop_return_value ctx
      | _ ->
          [%craise] span
            ("Unit test failed (concrete execution) on: "
            ^ Print.Types.name_to_string
                (Print.Contexts.decls_ctx_to_fmt_env decls_ctx)
                fdef.item_meta.name)
    in
    (* Evaluate the function *)
    let ctx_resl, _ = eval_function_body config body.body ctx in
    let _ = List.map (fun (ctx, res) -> check res ctx) ctx_resl in
    ()

  (** Small helper: return true if the function is a *transparent* unit function
      (no parameters, no arguments) - TODO: move *)
  let fun_decl_is_transparent_unit (def : fun_decl) : bool =
    Option.is_some def.body
    && def.signature.generics = empty_generic_params
    && def.signature.inputs = []

  (** Test all the unit functions in a list of function definitions *)
  let test_unit_functions (crate : crate) : unit =
    let unit_funs =
      FunDeclId.Map.filter
        (fun _ -> fun_decl_is_transparent_unit)
        crate.fun_decls
    in
    let decls_ctx = compute_contexts crate in
    let test_unit_fun _ (def : fun_decl) : unit =
      test_unit_function crate decls_ctx def.def_id
    in
    FunDeclId.Map.iter test_unit_fun unit_funs
end
