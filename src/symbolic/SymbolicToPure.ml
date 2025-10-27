open Pure
open PureUtils
open SymbolicToPureCore
open SymbolicToPureTypes
open SymbolicToPureExpressions
open Errors

(** The local logger *)
let log = Logging.symbolic_to_pure_log

let translate_fun_decl (ctx : bs_ctx) (body : S.expr option) : fun_decl =
  (* Translate *)
  let def = ctx.fun_decl in
  assert (ctx.bid = None);
  [%ltrace name_to_string ctx def.item_meta.name];

  (* Translate the declaration *)
  let def_id = def.def_id in
  let name = name_to_string ctx def.item_meta.name in
  (* Translate the signature *)
  let signature = translate_fun_sig_from_decomposed ctx.sg in
  (* Translate the body, if there is *)
  let body =
    match body with
    | None -> None
    | Some body ->
        [%ltrace
          name_to_string ctx def.item_meta.name
          ^ "\n- body:\n"
          ^ bs_ctx_expr_to_string ctx body];

        let effect_info =
          get_fun_effect_info ctx (FunId (FRegular def_id)) None
        in
        let mk_return (ctx : bs_ctx) v =
          match v with
          | None ->
              raise
                (Failure
                   "Unexpected: reached a return expression without value in a \
                    function forward expression")
          | Some output ->
              (* Wrap in a result if the function can fail *)
              if effect_info.can_fail then mk_result_ok_texpr ctx.span output
              else output
        in
        let mk_panic =
          (* TODO: we should use a [Fail] function *)
          let mk_output output_ty =
            mk_result_fail_texpr_with_error_id ctx.span error_failure_id
              output_ty
          in
          let back_tys = compute_back_tys ctx.sg.fun_ty in
          let back_tys = List.filter_map (fun x -> x) back_tys in
          let tys =
            if ctx.sg.fun_ty.fwd_info.ignore_output then back_tys
            else ctx.sg.fun_ty.fwd_output :: back_tys
          in
          let output = mk_simpl_tuple_ty tys in
          mk_output output
        in
        let ctx =
          { ctx with mk_return = Some mk_return; mk_panic = Some mk_panic }
        in
        let body = translate_expr body ctx in
        (* Sanity check *)
        type_check_texpr ctx body;
        (* Group the inputs together *)
        let inputs = ctx.forward_inputs in
        (* Sanity check *)
        [%ltrace
          name_to_string ctx def.item_meta.name
          ^ "\n- ctx.forward_inputs: "
          ^ String.concat ", " (List.map show_fvar ctx.forward_inputs)
          ^ "\n- signature.inputs: "
          ^ String.concat ", "
              (List.map (pure_ty_to_string ctx) signature.inputs)
          ^ "\n- inputs: "
          ^ String.concat ", " (List.map (fvar_to_string ctx) inputs)
          ^ "\n- body:\n" ^ texpr_to_string ctx body];
        (* TODO: we need to normalize the types *)
        if !Config.type_check_pure_code then
          [%sanity_check] def.item_meta.span
            (List.for_all
               (fun (var, ty) -> (var : fvar).ty = ty)
               (List.combine inputs signature.inputs));
        let inputs = List.map (mk_tpat_from_fvar None) inputs in
        Some (mk_closed_fun_body def.item_meta.span inputs body)
  in

  (* Note that for now, the loops are still *inside* the function body (and we
     haven't counted them): we will extract them from there later, in {!PureMicroPasses}
     (by "splitting" the definition). *)
  let num_loops = 0 in
  let loop_id = None in

  (* Assemble the declaration *)
  let backend_attributes = { reducible = false } in
  (* Check if the function is builtin *)
  let builtin_info =
    let funs_map = ExtractBuiltin.builtin_funs_map () in
    match_name_find_opt ctx.decls_ctx def.item_meta.name funs_map
  in
  let def : fun_decl =
    {
      def_id;
      item_meta = def.item_meta;
      builtin_info;
      src = def.src;
      backend_attributes;
      num_loops;
      loop_id;
      name;
      signature;
      is_global_decl_body = Option.is_some def.is_global_initializer;
      body;
    }
  in
  (* Debugging *)
  [%ltrace "translated:\n" ^ fun_decl_to_string ctx def];
  (* return *)
  def

let translate_type_decls (ctx : Contexts.decls_ctx) : type_decl list =
  List.filter_map
    (fun d ->
      try Some (translate_type_decl ctx d)
      with CFailure error ->
        let env = PrintPure.decls_ctx_to_fmt_env ctx in
        let name = PrintPure.name_to_string env d.item_meta.name in
        let name_pattern =
          try
            TranslateCore.name_to_pattern_string (Some d.item_meta.span) ctx
              d.item_meta.name
          with CFailure _ ->
            "(could not compute the name pattern due to a different error)"
        in
        [%save_error_opt_span] error.span
          ("Could not translate type decl '" ^ name
         ^ " because of previous error\nName pattern: '" ^ name_pattern ^ "'");
        None)
    (TypeDeclId.Map.values ctx.type_ctx.type_decls)

let translate_binder (span : span option) (translate_inside : 'a -> 'b)
    (x : 'a T.binder) : 'b binder =
  let binder_llbc_generics = x.T.binder_params in
  let binder_generics, binder_preds =
    translate_generic_params span binder_llbc_generics
  in
  let binder_explicit_info = compute_explicit_info binder_generics [] in
  {
    binder_value = translate_inside x.T.binder_value;
    binder_generics;
    binder_preds;
    binder_explicit_info;
    binder_llbc_generics;
  }

let translate_trait_method (span : span option) (translate_ty : T.ty -> ty)
    (bound_method : A.trait_method T.binder) : fun_decl_ref binder =
  translate_binder span
    (fun (m : A.trait_method) ->
      translate_fun_decl_ref span translate_ty m.item)
    bound_method

let translate_trait_decl (ctx : Contexts.decls_ctx) (trait_decl : A.trait_decl)
    : trait_decl =
  let {
    def_id;
    item_meta;
    generics = llbc_generics;
    implied_clauses = llbc_parent_clauses;
    consts;
    types;
    methods;
    vtable = _;
  } : A.trait_decl =
    trait_decl
  in
  let span = Some item_meta.span in
  let type_infos = ctx.type_ctx.type_infos in
  let translate_ty = translate_fwd_ty span type_infos in
  let name =
    Print.Types.name_to_string
      (Print.Contexts.decls_ctx_to_fmt_env ctx)
      item_meta.name
  in
  let generics, preds = translate_generic_params span llbc_generics in
  let explicit_info = compute_explicit_info generics [] in
  let parent_clauses =
    List.map (translate_trait_clause span) llbc_parent_clauses
  in
  if types <> [] then
    (* Most associated types are removed by Charon's `--remove-associated-types`. *)
    [%craise_opt_span] span
      "Found an unhandled trait associated type; this can happen with \
       mutually-recursive traits as well as GATs. Aeneas cannot handle such \
       types today.";
  let types = [] in
  let consts =
    List.map
      (fun (c : A.trait_assoc_const) -> (c.name, translate_ty c.ty))
      consts
  in
  let methods =
    List.map
      (fun (m : A.trait_method T.binder) ->
        (m.binder_value.name, translate_trait_method span translate_ty m))
      methods
  in
  (* Lookup the builtin information, if there is *)
  let builtin_info =
    match_name_find_opt ctx trait_decl.item_meta.name
      (ExtractBuiltin.builtin_trait_decls_map ())
  in
  {
    def_id;
    name;
    item_meta;
    builtin_info;
    generics;
    explicit_info;
    llbc_generics;
    preds;
    parent_clauses;
    llbc_parent_clauses;
    consts;
    types;
    methods;
  }

let translate_trait_impl (ctx : Contexts.decls_ctx) (trait_impl : A.trait_impl)
    : trait_impl =
  [%ltrace
    let ctx = Print.Contexts.decls_ctx_to_fmt_env ctx in
    "- trait impl: implemented trait: "
    ^ Print.Types.trait_decl_ref_to_string ctx trait_impl.impl_trait];
  let {
    A.def_id;
    item_meta;
    impl_trait = llbc_impl_trait;
    generics = llbc_generics;
    implied_trait_refs;
    consts;
    types = _;
    methods;
    vtable = _;
  } =
    trait_impl
  in
  let span = Some item_meta.span in
  let type_infos = ctx.type_ctx.type_infos in
  let translate_ty = translate_fwd_ty span type_infos in
  let impl_trait =
    (translate_trait_decl_ref span translate_ty) llbc_impl_trait
  in
  let name =
    Print.Types.name_to_string
      (Print.Contexts.decls_ctx_to_fmt_env ctx)
      item_meta.name
  in
  let generics, preds = translate_generic_params span llbc_generics in
  let explicit_info = compute_explicit_info generics [] in
  let parent_trait_refs =
    List.map (translate_strait_ref span) implied_trait_refs
  in
  let consts =
    List.map
      (fun (name, gref) ->
        (name, translate_global_decl_ref span translate_ty gref))
      consts
  in
  (* We checked that there were no types in the trait declaration already. *)
  let types = [] in
  let methods =
    List.map
      (fun ((name, m) : string * T.fun_decl_ref T.binder) ->
        ( name,
          translate_binder span (translate_fun_decl_ref span translate_ty) m ))
      methods
  in
  (* Lookup the builtin information, if there is *)
  let builtin_info =
    let decl_id = trait_impl.impl_trait.id in
    let trait_decl =
      [%silent_unwrap_opt_span] span
        (TraitDeclId.Map.find_opt decl_id ctx.crate.trait_decls)
    in
    match_name_with_generics_find_opt ctx trait_decl.item_meta.name
      llbc_impl_trait.generics
      (ExtractBuiltin.builtin_trait_impls_map ())
  in
  {
    def_id;
    name;
    item_meta;
    builtin_info;
    impl_trait;
    llbc_impl_trait;
    generics;
    explicit_info;
    llbc_generics;
    preds;
    parent_trait_refs;
    consts;
    types;
    methods;
  }

let translate_global (ctx : Contexts.decls_ctx) (decl : A.global_decl) :
    global_decl =
  let {
    A.item_meta;
    def_id;
    generics = llbc_generics;
    ty;
    src;
    init = body_id;
    _;
  } =
    decl
  in
  let name =
    Print.Types.name_to_string
      (Print.Contexts.decls_ctx_to_fmt_env ctx)
      item_meta.name
  in
  let generics, preds =
    translate_generic_params (Some decl.item_meta.span) llbc_generics
  in
  let explicit_info = compute_explicit_info generics [] in
  let ty =
    translate_fwd_ty (Some decl.item_meta.span) ctx.type_ctx.type_infos ty
  in
  let builtin_info =
    match_name_find_opt ctx item_meta.name
      (ExtractBuiltin.builtin_globals_map ())
  in
  {
    span = item_meta.span;
    def_id;
    item_meta;
    builtin_info;
    name;
    llbc_generics;
    generics;
    explicit_info;
    preds;
    ty;
    src;
    body_id;
  }
