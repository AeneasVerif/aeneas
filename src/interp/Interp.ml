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
    (decls : type_declaration_group list) : TypesAnalysis.type_infos =
  let open TypesAnalysis in
  List.fold_left
    (fun infos decl ->
      try analyze_type_declaration_group None crate infos decl
      with CFailure error ->
        let fmt_env : Print.fmt_env = Charon.Print.crate_to_fmt_env crate in
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
    TypeDeclId.TreeMap.empty decls

let compute_contexts (crate : crate) : decls_ctx =
  let crate_graph = Deps.compute_graph_of_uses crate in
  let declarations = Option.get crate.declarations in
  let type_decls_list, _, _, _, _, _ = split_declarations declarations in
  let fmt_env : Print.fmt_env = Charon.Print.crate_to_fmt_env crate in

  (* Split the declaration groups between the declaration kinds (types, functions, etc.) *)
  let type_decls_groups, _, _, _, _, mixed_groups =
    split_declarations_to_group_maps declarations
  in
  (* Check if there are mixed groups: if there are, we report an error
     and ignore those. *)
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
       (* If the definitions are external, add information about where they
          are (transitively) used in the local crate *)
       let local_uses = Deps.compute_local_uses crate_graph ids in
       let local_uses =
         List.map
           (fun (info : Deps.item_info) ->
             item_id_to_string info.id ^ ": " ^ span_to_string info.span)
           (Deps.ItemInfoSet.to_list local_uses)
       in
       let local_uses =
         if local_uses <> [] then
           "\n\n\
            The declarations in this group are (transitively) used at the \
            following location(s):\n"
           ^ String.concat "\n" local_uses
         else ""
       in
       "# Group "
       ^ string_of_int (i + 1)
       ^ ":\n" ^ String.concat "\n" decls ^ local_uses ^ "\n"
     in
     let msgs = List.mapi group_to_msg mixed_groups in
     let msgs = String.concat "\n\n" msgs in
     [%save_error_opt_span] None
       ("Detected groups of mixed mutually recursive definitions (such as a \
         type mutually recursive with a function, or a function mutually \
         recursive with a trait implementation):\n\n" ^ msgs));

  (* Compute the set of ids which appear in the declaration groups: only those
     should be extracted.

     Note that Charon includes extra definitions in the crate as they needed for
     pretty printing. The set of declarations to extract is given by the [declarations]
     field.
  *)
  let type_decl_ids = ref TypeDeclId.TreeSet.empty in
  let fun_decl_ids = ref FunDeclId.TreeSet.empty in
  let global_decl_ids = ref GlobalDeclId.TreeSet.empty in
  let trait_decl_ids = ref TraitDeclId.TreeSet.empty in
  let trait_impl_ids = ref TraitImplId.TreeSet.empty in

  let visitor =
    object
      inherit [_] iter_crate

      method! visit_type_decl_id _ id =
        TypeDeclId.TreeSet.add_in_place id type_decl_ids

      method! visit_fun_decl_id _ id =
        FunDeclId.TreeSet.add_in_place id fun_decl_ids

      method! visit_global_decl_id _ id =
        GlobalDeclId.TreeSet.add_in_place id global_decl_ids

      method! visit_trait_decl_id _ id =
        TraitDeclId.TreeSet.add_in_place id trait_decl_ids

      method! visit_trait_impl_id _ id =
        TraitImplId.TreeSet.add_in_place id trait_impl_ids
    end
  in
  List.iter (visitor#visit_declaration_group ()) declarations;

  let type_decls = crate.type_decls in
  let to_extract =
    TypeDeclId.Map.filter
      (fun id (d : type_decl) ->
        (* Charon introduces declarations for the builtin types (tuples, [Box],
           [str]): we handle those separately, and don't extract them *)
        TypeDeclId.TreeSet.mem id !type_decl_ids
        &&
        match d.src with
        | BuiltinType _ -> false
        | _ -> true)
      type_decls
  in
  let type_infos = analyze_type_declarations crate type_decls_list in
  let type_ctx = { type_decls_groups; type_decls; type_infos; to_extract } in

  let fun_decls = crate.fun_decls in
  let to_extract =
    FunDeclId.Map.filter
      (fun id _ -> FunDeclId.TreeSet.mem id !fun_decl_ids)
      fun_decls
  in
  let fun_infos = FunsAnalysis.analyze_module crate fun_decls in
  let fun_ctx = { fun_decls; fun_infos; to_extract } in

  let global_decls_to_extract =
    GlobalDeclId.Map.filter
      (fun id g ->
        GlobalDeclId.TreeSet.mem id !global_decl_ids
        (* The globals without initializers are constants which we inline *)
        && Option.is_some (Charon.GAstUtils.init_fun_id_of_global g))
      crate.global_decls
  in

  let trait_decls_to_extract =
    TraitDeclId.Map.filter
      (fun id _ -> TraitDeclId.TreeSet.mem id !trait_decl_ids)
      crate.trait_decls
  in

  let trait_impls_to_extract =
    TraitImplId.Map.filter
      (fun id _ -> TraitImplId.TreeSet.mem id !trait_impl_ids)
      crate.trait_impls
  in

  let trait_methods_to_extract =
    let trait_method_ids = ref TraitDeclId.TreeMap.empty in
    let add_trait_method_id trait_decl_id method_id =
      trait_method_ids :=
        TraitDeclId.TreeMap.update trait_decl_id
          (fun opt_set ->
            let set = Option.value opt_set ~default:TraitMethodId.Set.empty in
            Some (TraitMethodId.Set.add method_id set))
          !trait_method_ids
    in
    let visitor =
      object
        inherit [_] iter_crate as super

        (* Include a method if an implementation of it is in the extracted functions. *)
        method! visit_fun_source env (src : fun_source) =
          (match src with
          | TraitDefaultFun (trait_ref, method_id)
          | TraitImplFun (_, trait_ref, method_id, _) ->
              add_trait_method_id trait_ref.id method_id
          | _ -> ());
          super#visit_fun_source env src

        (* Include a method if it is mentioned in the extracted functions. *)
        method! visit_fn_ptr env fn_ptr =
          (match fn_ptr.kind with
          | TraitMethod (trait_ref, method_id) ->
              let trait_decl_id = trait_ref.trait_decl_ref.id in
              add_trait_method_id trait_decl_id method_id
          | _ -> ());
          super#visit_fn_ptr env fn_ptr
      end
    in
    List.iter
      (visitor#visit_fun_decl ())
      (FunDeclId.Map.values fun_ctx.to_extract);
    List.iter
      (visitor#visit_global_decl ())
      (GlobalDeclId.Map.values global_decls_to_extract);
    TraitDeclId.Map.iter
      (fun trait_decl_id (trait_decl : trait_decl) ->
        TraitMethodId.Map.iter
          (fun method_id (_method : trait_method binder) ->
            add_trait_method_id trait_decl_id method_id)
          trait_decl.methods)
      trait_decls_to_extract;

    TraitDeclId.Map.filter_map
      (fun trait_decl_id (trait_decl : trait_decl) ->
        match TraitDeclId.TreeMap.find_opt trait_decl_id !trait_method_ids with
        | None -> Some TraitMethodId.Map.empty
        | Some method_ids ->
            Some
              (TraitMethodId.Map.filter
                 (fun method_id _ -> TraitMethodId.Set.mem method_id method_ids)
                 trait_decl.methods))
      crate.trait_decls
  in

  {
    crate;
    graph_of_uses = crate_graph;
    type_ctx;
    fun_ctx;
    global_decls_to_extract;
    trait_decls_to_extract;
    trait_methods_to_extract;
    trait_impls_to_extract;
  }

(** Instantiate a function signature for a symbolic execution.

    We return a new context because we compute and add the type normalization
    map in the same step. *)
let symbolic_instantiate_fun_sig (span : Meta.span) (ctx : eval_ctx)
    (sg : bound_fun_sig) (_kind : fun_source) : eval_ctx * inst_fun_sig =
  let tr_self = UnknownTrait "symbolic_instantiate_fun_sig" in
  let generics =
    Substitute.generic_args_of_params_erase_regions (Some span)
      sg.item_binder_params
  in
  let inst_sg = instantiate_fun_sig (Some span) ctx generics tr_self sg in
  let region_groups =
    List.map (fun (g : region_group) -> g.id) inst_sg.regions_hierarchy
  in
  let ctx = { ctx with region_groups } in
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
  let span = fdef.item_meta.span in

  (* Create the context.

     We start with an empty list of region groups, then update the list of
     region groups when analyzing the function signature. *)
  let ctx =
    initialize_eval_ctx (Some span) ctx [] fdef.generics.types
      fdef.generics.const_generics marked_ids
  in
  (* Instantiate the signature. This updates the context because we compute
     at the same time the list of region groups. *)
  let ctx, inst_sg =
    symbolic_instantiate_fun_sig span ctx (bound_fun_sig_of_decl fdef) fdef.src
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
          mk_aproj_loans_value_from_symbolic_value ctx.type_ctx.type_infos
            abs.regions.owned sv sv.sv_ty)
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
            mk_eproj_loans_value_from_symbolic_value ctx.env
              ctx.type_ctx.type_infos abs.regions.owned sv sv.sv_ty)
          input_svs
      in
      (* Note that we don't really care about the type of the input *)
      let input =
        { value = EApp (EInputAbs rg_id, [ inputs ]); ty = mk_unit_ty }
      in
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
  let body = [%add_loc] body_as_body_exn fdef.body in
  let ret_var = List.hd body.locals.locals in
  let input_vars, local_vars =
    Collections.List.split_at (List.tl body.locals.locals) body.locals.arg_count
  in
  (* Push the return variable (initialized with ⊥) *)
  let ctx = ctx_push_uninitialized_var span ctx ret_var in
  (* Push the input variables (initialized with symbolic values) *)
  let input_values = List.map mk_tvalue_from_symbolic_value input_svs in
  [%ldebug
    "input vars and values:\n"
    ^ String.concat "\n"
        (List.map
           (fun ((var, value) : local * tvalue) ->
             local_to_string ctx var ^ " -> " ^ tvalue_to_string ctx value)
           (List.combine input_vars input_values))];
  let ctx = ctx_push_vars span ctx (List.combine input_vars input_values) in
  (* Push the remaining local variables (initialized with ⊥) *)
  let ctx = ctx_push_uninitialized_vars span ctx local_vars in
  (* Return *)
  (ctx, input_svs, inst_sg)

let stateful_lifetime_abs_ids_in_env (env : env) : AbsId.id list =
  List.filter_map
    (function
      | EAbs abs when Option.is_some abs.stateful_lifetime -> Some abs.abs_id
      | _ -> None)
    env

(** Small helper.

    This is a continuation function called by the symbolic interpreter upon
    reaching the [return] instruction when synthesizing a *backward* function:
    this continuation takes care of doing the proper manipulations to finish the
    synthesis (mostly by ending abstractions). *)
let evaluate_function_symbolic_synthesize_backward_from_return (config : config)
    (fdef : fun_decl) (inst_sg : inst_fun_sig) (back_id : RegionGroupId.id)
    ~(is_stateful_lifetime_rg : bool) ~(end_unattached_stateful : bool)
    (ret_value : tvalue) (ctx : eval_ctx) : AbsId.Set.t * SA.expr =
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
  let _, ret_inst_sg =
    symbolic_instantiate_fun_sig span ctx (bound_fun_sig_of_decl fdef) fdef.src
  in
  let ret_rty = ret_inst_sg.output in

  (* We need to find the ancestor regions/abstractions of the region group we
     will end - this will allow us to, first, mark the return regions which are
     neither ancestors nor in the current group as non-endable (except when
     synthesizing the backward function of the static region group: see below),
     and, second, end the ancestor regions in proper order. *)
  let parent_rgs =
    RegionsHierarchy.list_ancestor_region_groups inst_sg.regions_hierarchy
      back_id
  in
  let target_abs_ids_of h =
    List.filter_map
      (fun x -> x)
      (RegionGroupId.mapi
         (fun rg_id (rg : abs_region_group) ->
           if RegionGroupId.Set.mem rg_id parent_rgs then Some rg.id else None)
         h)
    @ [ (RegionGroupId.nth h back_id).id ]
  in
  (* Are we synthesizing the backward function of the static region group? *)
  let is_static_rg =
    List.mem RStatic
      (RegionGroupId.nth inst_sg.regions_hierarchy back_id).regions
  in

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
       information.

       Remark: we need to distinguish two notions:
       - the regions which *may* end when we end the current region group:
         those are the regions of the current group and the regions which are
         shorter than them
       - the ancestors of the current region group (its parents, transitively),
         which *must* end first: ending an abstraction always starts by ending
         its parents, hence, recursively, its ancestors.

       For a region group which doesn't contain the static region, the two
       notions coincide: the ancestors are given by the transitive closure of
       the outlives relation given by the signature, which is exactly the
       information which tells us which regions are shorter.

       The static region, however, outlives all the other regions: all the
       regions *may* end when we end the static region. But this doesn't mean
       they *have to* end first: whether ending the static region requires
       ending another region depends on how the borrows flow in the body of the
       function, which we can't know by looking only at the signature. For
       instance, with the signature
       [fn f<'b>(x: &'static str, y: &'b str) -> (&'static str, &'b str)],
       the regions ['static] and ['b] are independent if the body is
       [{ (x, y) }], while if the body is [{ (x, x) }], ending ['static]
       requires ending ['b] (because the static borrow was coerced to a borrow
       of region ['b], ending the static loan requires ending this borrow -
       note that ['b] doesn't need to end *as an ancestor*, i.e., before we
       start ending the static region).

       This is why the static region group doesn't always have all the other
       region groups as parents: it only has them when the signature may
       require them to end first (this is a conservative check), or when some
       region variables outlive ['static] and are thus merged into the static
       region group (see {!RegionsHierarchy.compute_regions_hierarchy_for_sig}).
       In the other cases, we don't make the other regions end first, but we
       allow them to end, so that the symbolic execution can end them if the
       body of the function requires it. *)
    let parent_and_current_rgs = RegionGroupId.Set.add back_id parent_rgs in
    let region_can_end rid =
      is_static_rg || RegionGroupId.Set.mem rid parent_and_current_rgs
    in
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

  let target_abs_ids = target_abs_ids_of inst_sg.abs_regions_hierarchy in
  let target_ret_abs_ids =
    target_abs_ids_of ret_inst_sg.abs_regions_hierarchy
  in

  (* Set the abstractions as endable. If we are synthesizing the backward
     function for the static region, we allow ending all the input
     abstractions, even if we only end the ancestor abstractions (and the
     current abstraction) explicitly below: see the remark above about the
     regions which *may* end and the ancestors which *must* end first. *)
  let endable_abs_ids =
    if is_static_rg then
      List.map
        (fun (rg : abs_region_group) -> rg.id)
        inst_sg.abs_regions_hierarchy
    else target_abs_ids
  in
  let ctx =
    InterpBorrowsCore.update_endable ctx endable_abs_ids ~can_end:true
  in

  (* If we are synthesizing the backward function for the static region, we
     need to allow ending the region abstractions which own the static region
     (see [abs_is_endable]) *)
  let ctx = if is_static_rg then { ctx with can_end_static = true } else ctx in

  let alive_before = stateful_lifetime_abs_ids_in_env ctx.env in

  (* For a stateful lifetime, end [SynthRet] and simplify first so output-lending
     abstractions whose loans just ended (e.g. [Ptr::as_mut]/[Ptr::as_shr]) end
     in LIFO order before [SynthInput] ends input-borrowing ones (e.g.
     [Ptr::from_mut]/[Ptr::from_shr]). *)
  let ctx, cc_ret =
    if is_stateful_lifetime_rg then
      let ctx, cc_ret =
        fold_left_apply_continuation
          (fun id ctx -> end_abs config span id 0 ctx)
          target_ret_abs_ids ctx
      in
      comp cc_ret
        (InterpBorrows.simplify_dummy_values_useless_abs config
           ~keep_stateful_lifetime:(fun _ -> true)
           ~filter_avalues:false span ctx)
    else (ctx, fun e -> e)
  in

  (* Actually end them *)
  let ctx, cc =
    comp cc_ret
      (fold_left_apply_continuation
         (fun id ctx -> end_abs config span id 0 ctx)
         target_abs_ids ctx)
  in
  (* Handle any remaining #[verify::stateful_lifetime] abstractions:
     - If this region group carries #[verify::stateful_lifetime], end any remaining
       stateful-lifetime abstractions (e.g., borrowing 'static) so their backward
       effects flow into this backward function.
     - Otherwise, check that ending this region group did not prematurely end
       any active stateful-lifetime abstraction. *)
  let ctx, cc =
    if is_stateful_lifetime_rg then
      if end_unattached_stateful then
        let remaining_alive = stateful_lifetime_abs_ids_in_env ctx.env in
        comp cc
          (fold_left_apply_continuation
             (fun id ctx -> end_abs config span id 0 ctx)
             remaining_alive ctx)
      else (ctx, cc)
    else (
      if
        List.exists
          (fun id -> Option.is_none (ctx_lookup_abs_opt ctx id))
          alive_before
      then
        [%craise] span
          "A non-stateful-lifetime backward function cannot end an active \
           #[verify::stateful_lifetime] region abstraction";
      (ctx, cc))
  in
  let ended_alive =
    AbsId.Set.of_list
      (List.filter
         (fun id -> Option.is_none (ctx_lookup_abs_opt ctx id))
         alive_before)
  in
  (* Generate the Return node *)
  let return_expr = SA.Return (ctx, None) in
  (* Apply *)
  (ended_alive, cc return_expr)

(** Evaluate a function with the symbolic interpreter.

    We return:
    - the list of symbolic values introduced for the input values (this is
      useful for the synthesis)
    - the symbolic AST generated by the symbolic execution

    If [synthesize] is [true]: we synthesize the symbolic AST that is used for
    the translation. Otherwise, we do not (the symbolic execution then simply
    borrow-checks the function). *)
let evaluate_function_symbolic (synthesize : bool) (decls_ctx : decls_ctx)
    (marked_ids : marked_ids) (fdef : fun_decl) :
    symbolic_value list * SA.expr option =
  (* Debug *)
  let span = fdef.item_meta.span in
  let name_to_string () =
    Print.name_to_string
      (Print.Contexts.decls_ctx_to_fmt_env decls_ctx)
      fdef.item_meta.name
  in
  [%ltrace name_to_string ()];

  (* Create the evaluation context *)
  let ctx, input_svs, inst_sg =
    initialize_symbolic_context_for_fun decls_ctx marked_ids fdef
  in
  [%ltrace "initial context:\n" ^ eval_ctx_to_string ctx];

  let regions_hierarchy =
    RegionsHierarchy.compute_regions_hierarchy_for_sig (Some span) ctx.crate
      ctx.type_ctx.type_infos
      (bound_fun_sig_of_decl fdef)
  in

  (* Create the continuation to finish the evaluation *)
  let liveness =
    Option.map
      (fun (body : LlbcAst.expr_body) ->
        InterpLiveness.compute_liveness body.body)
      (LlbcAstUtils.body_as_body fdef.body)
  in
  let config = mk_config ~liveness SymbolicMode in
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
        (* Do not pop the locals if this is a global and [borrow_check_globals]
           is false *)
        let pop_locals =
          if !Config.borrow_check_globals then true
          else not (fun_decl_is_global_initializer fdef)
        in
        (* Whatever the scenario, we need to pop the frame and retrieve the returned value *)
        let ret_value, ctx, cc_pop =
          pop_frame config span ~pop_locals ~pop_return_value:true ctx
        in
        let ret_value = Option.get ret_value in
        (* Clean up any remaining dummy borrows from popped locals/parameters
           (while protecting [ret_value] as a temporary [BVar]). Pass
           [~filter_avalues:false] so [AEndedProjLoans] entries are preserved in
           existing [Loop]/[FunCall]/[SynthInput] abstractions for backward
           synthesis. *)
        let ret_value, ctx, cc_simpl =
          if not pop_locals then (ret_value, ctx, fun e -> e)
          else
            let ret_binder : real_var_binder =
              { index = Expressions.LocalId.zero; name = None }
            in
            let ctx =
              {
                ctx with
                env = EBinding (BVar ret_binder, ret_value) :: ctx.env;
              }
            in
            let ctx, cc_simpl =
              InterpBorrows.simplify_dummy_values_useless_abs config
                ~keep_stateful_lifetime:(fun _ -> true)
                ~filter_avalues:false span ctx
            in
            let ret_value, env =
              env_pop_var (fun _ -> [%internal_error] span) ret_binder ctx.env
            in
            (ret_value, { ctx with env }, cc_simpl)
        in
        let fun_info_opt =
          FunsAnalysis.lookup_fun_decl_info decls_ctx.fun_ctx.fun_infos
            fdef.def_id
        in
        let has_stateful_lifetime =
          match fun_info_opt with
          | Some info -> FunsAnalysis.has_stateful_lifetime info
          | None -> false
        in
        let has_stateful_lifetime_abs env =
          stateful_lifetime_abs_ids_in_env env <> []
        in
        let stateful_lifetime_rgs : RegionGroupId.id list =
          match fun_info_opt with
          | Some info ->
              List.filter_map
                (fun (rg : region_group) ->
                  if
                    Option.is_some
                      (FunsAnalysis.rg_stateful_lifetime (Some span) info rg)
                  then Some rg.id
                  else None)
                regions_hierarchy
          | None -> []
        in
        (* Decide how remaining #[verify::stateful_lifetime] abstractions behave at
           return based on which output region groups carry #[verify::stateful_lifetime]:
           - None ([]): no backward function may consume remaining stateful-lifetime
             abstractions, so end any whose loans are gone at the end of the
             forward function (raising an error if any still remain active).
           - One ([ _sl_gid ]): let remaining stateful-lifetime abstractions stay
             active past forward return so they flow into that backward function
             (including unattached ones such as borrowing `'static`).
           - Multiple (_ :: _ :: _): let remaining stateful-lifetime abstractions
             flow into their corresponding stateful backward functions, checking
             that every active stateful abstraction is ended by at least one of
             them. *)
        let ret_value, ctx, cc_end_stateful =
          match stateful_lifetime_rgs with
          | [] ->
              if has_stateful_lifetime then
                [%craise] span
                  "#[verify::stateful_lifetime] requires at least one lifetime \
                   in the function signature";
              let ret_value, ctx, cc_end_stateful =
                if not (has_stateful_lifetime_abs ctx.env) then
                  (ret_value, ctx, fun e -> e)
                else
                  let ret_binder : real_var_binder =
                    { index = Expressions.LocalId.zero; name = None }
                  in
                  let ctx =
                    {
                      ctx with
                      env = EBinding (BVar ret_binder, ret_value) :: ctx.env;
                    }
                  in
                  (* End zero-loan stateful abstractions in LIFO ([ctx.env])
                     order (and any zero-loan pure abstractions blocking them). *)
                  let rec end_stateful_lifetime_abs_with_no_loans
                      (ctx : eval_ctx) : eval_ctx * (SA.expr -> SA.expr) =
                    if not (has_stateful_lifetime_abs ctx.env) then
                      (ctx, fun e -> e)
                    else
                      let can_end_now (abs : abs) : bool =
                        AbsId.Set.for_all
                          (fun pid ->
                            Option.is_none (ctx_lookup_abs_opt ctx pid))
                          abs.parents
                        && Option.is_none
                             (InterpBorrowsCore
                              .get_first_non_ignored_aloan_in_abs span abs 0
                                (-1))
                        && abs_is_endable ctx abs
                      in
                      let stateful_no_loans =
                        List.filter_map
                          (function
                            | EAbs abs
                              when Option.is_some abs.stateful_lifetime
                                   && can_end_now abs -> Some abs.abs_id
                            | EAbs _ | EBinding _ | EFrame -> None)
                          ctx.env
                      in
                      let no_loans_abs =
                        if stateful_no_loans <> [] then stateful_no_loans
                        else
                          let frozen_abs = ctx_get_frozen_abs_set ctx in
                          List.filter_map
                            (function
                              | EAbs abs
                                when Option.is_none abs.stateful_lifetime
                                     && can_end_now abs
                                     && not
                                          (InterpLiveness
                                           .abs_borrows_loans_in_frozen span ctx
                                             frozen_abs abs) -> Some abs.abs_id
                              | EAbs _ | EBinding _ | EFrame -> None)
                            ctx.env
                      in
                      match no_loans_abs with
                      | [] -> (ctx, fun e -> e)
                      | abs_id :: _ ->
                          let ctx, cc_end =
                            InterpBorrows.end_abs config span abs_id 0 ctx
                          in
                          let ctx, cc_simpl =
                            InterpBorrows.simplify_dummy_values_useless_abs
                              config
                              ~keep_stateful_lifetime:(fun _ -> true)
                              ~filter_avalues:false span ctx
                          in
                          let cc = cc_comp cc_end cc_simpl in
                          comp cc (end_stateful_lifetime_abs_with_no_loans ctx)
                  in
                  let ctx, cc_end_stateful =
                    end_stateful_lifetime_abs_with_no_loans ctx
                  in
                  let ret_value, env =
                    env_pop_var
                      (fun _ -> [%internal_error] span)
                      ret_binder ctx.env
                  in
                  (ret_value, { ctx with env }, cc_end_stateful)
              in
              if has_stateful_lifetime_abs ctx.env then
                [%craise] span
                  "This function returns while a #[verify::stateful_lifetime] \
                   region abstraction is still active (so its backward \
                   function would need to end it); mark this function \
                   #[verify::stateful_lifetime] as well";
              (ret_value, ctx, cc_end_stateful)
          | _ :: _ -> (ret_value, ctx, fun e -> e)
        in
        let ctx_return = ctx in
        let alive_at_return =
          AbsId.Set.of_list (stateful_lifetime_abs_ids_in_env ctx.env)
        in
        [%ltrace
          "after popping the frame:\n- returned value:\n"
          ^ tvalue_to_string ctx_return ret_value
          ^ "\n\n- ctx:\n"
          ^ eval_ctx_to_string ctx_return];

        (* Forward translation: generate the Return node *)
        let fwd_e = SA.Return (ctx, Some ret_value) in
        (* Backward translation: introduce "return"
           abstractions to consume the return value, then end all the
           abstractions up to the one in which we are interested.
        *)
        (* Every active stateful abstraction must be ended by *exactly one*
           stateful backward function (and zero non-stateful ones). *)
        let end_unattached_stateful = List.length regions_hierarchy = 1 in
        let ended_by_stateful_rgs = ref AbsId.Set.empty in
        let finish_back_eval back_id =
          let is_stateful_lifetime_rg =
            List.mem back_id stateful_lifetime_rgs
          in
          let ended_alive, back_expr =
            evaluate_function_symbolic_synthesize_backward_from_return config
              fdef inst_sg back_id ~is_stateful_lifetime_rg
              ~end_unattached_stateful ret_value ctx
          in
          if is_stateful_lifetime_rg then (
            if not (AbsId.Set.disjoint !ended_by_stateful_rgs ended_alive) then
              [%craise] span
                "Dependent #[verify::stateful_lifetime] lifetimes where one \
                 backward function would also end another lifetime's stateful \
                 region abstraction are not supported yet";
            ended_by_stateful_rgs :=
              AbsId.Set.union !ended_by_stateful_rgs ended_alive);
          back_expr
        in
        let back_el =
          RegionGroupId.mapi
            (fun gid _ -> (gid, finish_back_eval gid))
            regions_hierarchy
        in
        if not (AbsId.Set.subset alive_at_return !ended_by_stateful_rgs) then
          [%craise] span
            "Cannot determine which #[verify::stateful_lifetime] backward \
             function should end an active stateful region abstraction (the \
             function has multiple stateful lifetimes, and the abstraction is \
             not tied to any of them)";
        let back_el = RegionGroupId.Map.of_list back_el in
        (* Put everything together *)
        cc_pop
          (cc_simpl
             (cc_end_stateful
                (SA.ForwardEnd
                   (Some (ctx_return, ret_value), ctx0, fwd_e, back_el))))
    | Panic ->
        (* Note that as we explore all the execution branches, one of
         * the executions can lead to a panic *)
        SA.Panic
    | Unit | Break _ | Continue _ ->
        [%craise] span
          ("evaluate_function_symbolic failed on: " ^ name_to_string ()
         ^ "\nUnexpected result: "
          ^ show_statement_eval_res res)
  in

  (* Evaluate the function *)
  let symbolic =
    try
      let body = [%add_loc] body_as_body_exn fdef.body in
      let ctx_resl, cc = eval_function_body config body.body ctx in
      let el = List.map (fun (ctx, res) -> finish res ctx) ctx_resl in
      (* Finish synthesizing *)
      if synthesize then Some (cc el) else None
    with CFailure error ->
      let name = name_to_string () in
      let name_pattern =
        try
          TranslateCore.name_to_pattern_string (Some fdef.item_meta.span)
            decls_ctx fdef.item_meta.name
        with CFailure _ ->
          "(could not compute the name pattern due to a different error)"
      in
      let action = if synthesize then "translate" else "borrow-check" in
      [%warn_opt_span] error.span
        ("Could not " ^ action ^ " the body of function '" ^ name
       ^ " because of previous error\nName pattern: '" ^ name_pattern ^ "'"
       ^ "\nDefinition span: "
        ^ Errors.raw_span_to_string fdef.item_meta.span
        ^ compute_local_uses_error_message decls_ctx (IdFun fdef.def_id));
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
    let body = [%add_loc] body_as_body_exn fdef.body in
    let span = fdef.item_meta.span in

    (* Debug *)
    [%ltrace
      Print.name_to_string
        (Print.Contexts.decls_ctx_to_fmt_env decls_ctx)
        fdef.item_meta.name];

    (* Sanity check - *)
    [%sanity_check] span (fdef.generics = empty_generic_params);
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
          pop_frame config span ~pop_locals:true ~pop_return_value:true ctx
      | _ ->
          [%craise] span
            ("Unit test failed (concrete execution) on: "
            ^ Print.name_to_string
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
    body_is_known def.body
    && def.generics = empty_generic_params
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
