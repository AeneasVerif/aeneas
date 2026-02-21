open LlbcAstUtils
open Pure
open PureUtils
open FunsAnalysis
open TypesAnalysis
open SymbolicToPureCore

(** The local logger *)
let log = Logging.symbolic_to_pure_types_log

(* We simply ignore the bound regions. Note that this messes up the de bruijn
   ids in variables: variables inside `rb.binder_value` are nested deeper so
   we should shift them before moving them out of their binder. We ignore this
   because we don't yet handle complex binding situations in Aeneas. *)
let translate_region_binder (translate_value : 'a -> 'b)
    (rb : 'a T.region_binder) : 'b =
  translate_value rb.binder_value

let translate_literal (l : V.literal) : literal =
  match l with
  | V.VScalar x -> VScalar x
  | V.VFloat x -> VFloat x
  | V.VBool x -> VBool x
  | V.VChar x -> VChar x
  | V.VByteStr x -> VByteStr x
  | V.VStr x -> VStr x

let translate_constant_expr_kind (span : span option) :
    Types.constant_expr_kind -> const_generic = function
  | CGlobal { id; _ } -> CgGlobal id
  | CVar v -> CgVar v
  | CLiteral l -> CgValue (translate_literal l)
  | _ -> [%craise_opt_span] span "Unsupported constant expression kind"

let translate_literal_type (ty : V.literal_type) : literal_type =
  match ty with
  | V.TInt x -> TInt x
  | V.TUInt x -> TUInt x
  | V.TFloat x -> TFloat x
  | V.TBool -> TBool
  | V.TChar -> TChar

let translate_const_generic_param (span : span option)
    (c : Types.const_generic_param) : const_generic_param =
  match c.ty with
  | TLiteral ty ->
      { index = c.index; name = c.name; ty = translate_literal_type ty }
  | _ -> [%craise_opt_span] span "Unsupported constant expression type"

(* Some generic translation functions (we need to translate different "flavours"
   of types: forward types, backward types, etc.) *)
let rec translate_generic_args (span : Meta.span option)
    (translate_ty : T.ty -> ty) (generics : T.generic_args) : generic_args =
  (* We ignore the regions: if they didn't cause trouble for the symbolic execution,
     then everything's fine *)
  let types = List.map translate_ty generics.types in
  let const_generics =
    List.map
      (fun (c : T.constant_expr) -> translate_constant_expr_kind span c.kind)
      generics.const_generics
  in
  let trait_refs =
    List.map (translate_trait_ref span translate_ty) generics.trait_refs
  in
  { types; const_generics; trait_refs }

and translate_trait_ref (span : Meta.span option) (translate_ty : T.ty -> ty)
    (tr : T.trait_ref) : trait_ref =
  let trait_id = translate_trait_ref_kind span translate_ty tr in
  let trait_decl_ref =
    translate_region_binder
      (translate_trait_decl_ref span translate_ty)
      tr.trait_decl_ref
  in
  { trait_id; trait_decl_ref }

and translate_trait_decl_ref (span : Meta.span option)
    (translate_ty : T.ty -> ty) (tr : T.trait_decl_ref) : trait_decl_ref =
  let decl_generics = translate_generic_args span translate_ty tr.generics in
  { trait_decl_id = tr.id; decl_generics }

and translate_fun_decl_ref (span : Meta.span option) (translate_ty : T.ty -> ty)
    (fr : T.fun_decl_ref) : fun_decl_ref =
  let fun_generics = translate_generic_args span translate_ty fr.generics in
  { fun_id = fr.id; fun_generics }

and translate_global_decl_ref (span : Meta.span option)
    (translate_ty : T.ty -> ty) (gr : T.global_decl_ref) : global_decl_ref =
  let global_generics = translate_generic_args span translate_ty gr.generics in
  { global_id = gr.id; global_generics }

and translate_trait_ref_kind (span : Meta.span option)
    (translate_ty : T.ty -> ty) (tref : T.trait_ref) : trait_instance_id =
  match tref.kind with
  | T.Self -> Self
  | TraitImpl impl_ref ->
      let generics =
        translate_generic_args span translate_ty impl_ref.generics
      in
      TraitImpl (impl_ref.id, generics)
  | BuiltinOrAuto (data, _, _) ->
      let data =
        match data with
        | BuiltinClone -> BuiltinClone
        | BuiltinCopy -> BuiltinCopy
        | BuiltinDiscriminantKind -> BuiltinDiscriminantKind
        | BuiltinFn -> BuiltinFn
        | BuiltinFnMut -> BuiltinFnMut
        | BuiltinFnOnce -> BuiltinFnOnce
        | _ ->
            [%craise_opt_span] span
              ("Unhandled `BuiltinOrAuto` for trait "
              ^ TraitDeclId.to_string tref.trait_decl_ref.binder_value.id
              ^ "; builtin_impl_data: "
              ^ Types.show_builtin_impl_data data)
      in
      BuiltinOrAuto data
  | Clause var ->
      Clause var
      (* Note: the `de_bruijn_id`s are incorrect, see comment on `translate_region_binder` *)
  | ParentClause (tref, clause_id) ->
      let inst_id = translate_trait_ref_kind span translate_ty tref in
      ParentClause (inst_id, tref.trait_decl_ref.binder_value.id, clause_id)
  | ItemClause _ ->
      (* `ItemClause`s are removed by Charon's `--remove-associated-types`, except for GATs *)
      [%craise_opt_span] span "Generic Associated Types are not supported yet"
  | Dyn -> [%craise_opt_span] span "Dynamic trait types are not supported yet"
  | UnknownTrait s -> [%craise_opt_span] span ("Unknown trait found: " ^ s)

(** Translate a signature type - TODO: factor out the different translation
    functions *)
let rec translate_sty (span : Meta.span option) (ty : T.ty) : ty =
  let translate = translate_sty in
  match ty with
  | T.TAdt { id; generics } -> (
      let generics = translate_sgeneric_args span generics in
      match id with
      | T.TAdtId adt_id -> TAdt (TAdtId adt_id, generics)
      | T.TTuple ->
          [%sanity_check_opt_span] span (generics.const_generics = []);
          mk_simpl_tuple_ty generics.types
      | T.TBuiltin aty -> (
          match aty with
          | T.TBox -> (
              (* Eliminate the boxes *)
              match generics.types with
              | [ ty ] -> ty
              | _ ->
                  [%craise_opt_span] span
                    "Box/vec/option type with incorrect number of arguments")
          | T.TStr -> TAdt (TBuiltin TStr, generics)))
  | T.TArray (ty, len) ->
      let ty = translate span ty in
      let len = translate_constant_expr_kind span len.kind in
      TAdt
        ( TBuiltin TArray,
          { types = [ ty ]; const_generics = [ len ]; trait_refs = [] } )
  | T.TSlice ty ->
      let ty = translate span ty in
      TAdt
        ( TBuiltin TSlice,
          { types = [ ty ]; const_generics = []; trait_refs = [] } )
  | TVar var ->
      TVar var
      (* Note: the `de_bruijn_id`s are incorrect, see comment on `translate_region_binder` *)
  | TLiteral ty -> TLiteral (translate_literal_type ty)
  | TNever -> TNever
  | TRef (_, rty, _) -> translate span rty
  | TRawPtr (ty, rkind) ->
      let mut =
        match rkind with
        | RMut -> Mut
        | RShared -> Const
      in
      let ty = translate span ty in
      let generics = { types = [ ty ]; const_generics = []; trait_refs = [] } in
      TAdt (TBuiltin (TRawPtr mut), generics)
  | TTraitType (trait_ref, type_name) ->
      let trait_ref = translate_strait_ref span trait_ref in
      TTraitType (trait_ref, type_name)
  | TFnDef _ | TFnPtr _ ->
      [%craise_opt_span] span "Arrow types are not supported yet"
  | TDynTrait _ ->
      [%craise_opt_span] span "Dynamic trait types are not supported yet"
  | TPtrMetadata _ -> [%craise_opt_span] span "unsupported: PtrMetadata"
  | TError _ ->
      [%craise_opt_span] span "Found type error in the output of charon"

and translate_sgeneric_args (span : Meta.span option)
    (generics : T.generic_args) : generic_args =
  translate_generic_args span (translate_sty span) generics

and translate_strait_ref (span : Meta.span option) (tr : T.trait_ref) :
    trait_ref =
  translate_trait_ref span (translate_sty span) tr

let translate_strait_decl_ref (span : Meta.span option) (tr : T.trait_decl_ref)
    : trait_decl_ref =
  translate_trait_decl_ref span (translate_sty span) tr

let translate_trait_clause (span : Meta.span option) (clause : T.trait_param) :
    trait_param =
  let { T.clause_id; span = _; trait } = clause in
  let trait = translate_region_binder (translate_strait_decl_ref span) trait in
  { clause_id; trait_id = trait.trait_decl_id; generics = trait.decl_generics }

let translate_strait_type_constraint (span : Meta.span option)
    (ttc : T.trait_type_constraint) : trait_type_constraint =
  let { T.trait_ref; type_name; ty } = ttc in
  let trait_ref = translate_strait_ref span trait_ref in
  let ty = translate_sty span ty in
  { trait_ref; type_name; ty }

let translate_type_param (p : T.type_param) : type_param =
  let { index; name } : T.type_param = p in
  { index; name }

let translate_generic_params (span : Meta.span option)
    (generics : T.generic_params) : generic_params * predicates =
  let {
    T.regions = _;
    types;
    const_generics;
    trait_clauses;
    trait_type_constraints;
    _;
  } =
    generics
  in
  let types = List.map translate_type_param types in
  let const_generics =
    List.map (translate_const_generic_param span) const_generics
  in
  let trait_clauses = List.map (translate_trait_clause span) trait_clauses in
  let trait_type_constraints =
    List.map
      (translate_region_binder (translate_strait_type_constraint span))
      trait_type_constraints
  in
  ({ types; const_generics; trait_clauses }, { trait_type_constraints })

let translate_field (span : Meta.span) (f : T.field) : field =
  let field_name = f.field_name in
  let field_ty = translate_sty (Some span) f.field_ty in
  let field_attr_info = f.attr_info in
  { field_name; field_ty; field_attr_info }

let translate_fields (span : Meta.span) (fl : T.field list) : field list =
  List.map (translate_field span) fl

let translate_variant (span : Meta.span) (v : T.variant) : variant =
  let variant_name = v.variant_name in
  let fields = translate_fields span v.fields in
  let variant_attr_info = v.attr_info in
  let discriminant, ty =
    match v.discriminant with
    | VScalar (SignedScalar (ty, v)) -> (Z.to_int v, TInt ty)
    | VScalar (UnsignedScalar (ty, v)) -> (Z.to_int v, TUInt ty)
    | _ ->
        [%craise] span
          "Internal error, please report an issue: found an enumeration \
           variant with an unexpected type"
  in
  { variant_name; fields; variant_attr_info; discriminant; ty }

let translate_variants (span : Meta.span) (vl : T.variant list) : variant list =
  List.map (translate_variant span) vl

(** Translate a type def kind from LLBC *)
let translate_type_decl_kind (span : Meta.span) (kind : T.type_decl_kind) :
    type_decl_kind =
  match kind with
  | T.Struct fields -> Struct (translate_fields span fields)
  | T.Enum variants -> Enum (translate_variants span variants)
  | Alias _ -> [%craise] span "type aliases should have been removed earlier"
  | T.Union _ | T.Opaque | T.TDeclError _ -> Opaque

(** Translate a type definition from LLBC

    Remark: this is not symbolic to pure but LLBC to pure. Still, I don't see
    the point of moving this definition for now. *)
let translate_type_decl (ctx : Contexts.decls_ctx) (def : T.type_decl) :
    type_decl =
  [%ltrace
    let ctx = Print.Contexts.decls_ctx_to_fmt_env ctx in
    "\n" ^ Print.Types.type_decl_to_string ctx def];
  let env = Print.Contexts.decls_ctx_to_fmt_env ctx in
  let def_id = def.T.def_id in
  let name = Print.Types.name_to_string env def.item_meta.name in
  let span = def.item_meta.span in
  (* Can't translate types with nested borrows for now *)
  [%cassert] span
    (not
       (TypesUtils.type_decl_has_nested_mut_borrows (Some span)
          ctx.type_ctx.type_infos def))
    "ADTs containing nested mutable borrows are not supported yet";
  let generics, preds = translate_generic_params (Some span) def.generics in
  [%ldebug
    let ctx = PrintPure.decls_ctx_to_fmt_env ctx in
    "translated generic_params:\n"
    ^ PrintPure.generic_params_to_string ctx generics];
  let explicit_info = compute_explicit_info generics [] in
  [%ldebug "explicit info:\n" ^ show_explicit_info explicit_info];
  let kind = translate_type_decl_kind span def.T.kind in
  let item_meta = def.item_meta in
  (* Lookup the builtin information, if there is *)
  let builtin_info =
    match_name_find_opt ctx def.item_meta.name
      (ExtractBuiltin.builtin_types_map ())
  in
  {
    def_id;
    name;
    item_meta;
    builtin_info;
    generics;
    explicit_info;
    llbc_generics = def.generics;
    kind;
    preds;
  }

let translate_type_id (span : Meta.span option) (id : T.type_id) : type_id =
  match id with
  | TAdtId adt_id -> TAdtId adt_id
  | TBuiltin aty ->
      let aty =
        match aty with
        | T.TStr -> TStr
        | T.TBox ->
            (* Boxes have to be eliminated: this type id shouldn't
               be translated *)
            [%craise_opt_span] span "Unexpected box type"
      in
      TBuiltin aty
  | TTuple -> TTuple

(** Translate a type, seen as an input/output of a forward function (preserve
    all borrows, etc.).

    Remark: it doesn't matter whether the types has regions or erased regions
    (both cases happen, actually).

    TODO: factor out the various translation functions. *)
let rec translate_fwd_ty (span : Meta.span option) (decls_ctx : C.decls_ctx)
    (ty : T.ty) : ty =
  let translate = translate_fwd_ty span decls_ctx in
  match ty with
  | T.TAdt { id; generics } -> (
      let t_generics = translate_fwd_generic_args span decls_ctx generics in
      (* Eliminate boxes and simplify tuples *)
      match id with
      | TAdtId _ | TBuiltin TStr ->
          let id = translate_type_id span id in
          TAdt (id, t_generics)
      | TTuple ->
          (* Note that if there is exactly one type, [mk_simpl_tuple_ty] is the
             identity *)
          mk_simpl_tuple_ty t_generics.types
      | TBuiltin TBox -> (
          (* We eliminate boxes *)
          match t_generics.types with
          | [ bty ] -> bty
          | _ ->
              [%craise_opt_span] span
                "Unreachable: box/vec/option receives exactly one type \
                 parameter"))
  | T.TArray (ty, len) ->
      let ty = translate ty in
      let len = translate_constant_expr_kind span len.kind in
      TAdt
        ( TBuiltin TArray,
          { types = [ ty ]; const_generics = [ len ]; trait_refs = [] } )
  | T.TSlice ty ->
      let ty = translate ty in
      TAdt
        ( TBuiltin TSlice,
          { types = [ ty ]; const_generics = []; trait_refs = [] } )
  | TVar var -> TVar var
  | TNever -> TNever
  | TLiteral lty -> TLiteral (translate_literal_type lty)
  | TRef (_, rty, _) -> translate rty
  | TRawPtr (ty, rkind) ->
      let mut =
        match rkind with
        | RMut -> Mut
        | RShared -> Const
      in
      let ty = translate ty in
      let generics = { types = [ ty ]; const_generics = []; trait_refs = [] } in
      TAdt (TBuiltin (TRawPtr mut), generics)
  | TTraitType (trait_ref, type_name) ->
      let trait_ref = translate_fwd_trait_ref span decls_ctx trait_ref in
      TTraitType (trait_ref, type_name)
  | TFnDef { binder_regions; binder_value = { kind; generics } } -> (
      [%cassert_opt_span] span (binder_regions = []) "Unimplemented";
      let generics = translate_fwd_generic_args span decls_ctx generics in
      match kind with
      | T.FunId (FBuiltin _) -> [%craise_opt_span] span "Unimplemented"
      | T.FunId (FRegular fid) ->
          let fdecl =
            [%unwrap_opt_span] span
              (FunDeclId.Map.find_opt fid decls_ctx.fun_ctx.fun_decls)
              "Could not lookup a function declaration"
          in
          let dsg = translate_fun_sig_from_decl_to_decomposed decls_ctx fdecl in
          let sg = translate_fun_sig_from_decomposed dsg in
          (* Check that the function lives in the expected effect - otherwise we
                 have to lift it *)
          [%cassert_opt_span] span sg.fwd_info.effect_info.can_fail
            "Unimplemented";
          [%cassert_opt_span] span
            (RegionGroupId.Map.for_all
               (fun _ (e : fun_effect_info) -> not e.can_fail)
               sg.back_effect_info)
            "Unimplemented";
          (* Substitute *)
          let subst = make_subst_from_generics sg.generics generics in
          let inputs = List.map (ty_substitute subst) sg.inputs in
          let output = ty_substitute subst sg.output in
          mk_arrows inputs output
      | T.TraitMethod _ -> [%craise_opt_span] span "Unimplemented")
  | TFnPtr _ -> [%craise_opt_span] span "Arrow types are not supported yet"
  | TDynTrait { binder } ->
      let params, _predicates =
        translate_generic_params span binder.binder_params
      in
      TDynTrait { params }
  | TPtrMetadata _ -> [%craise_opt_span] span "unsupported: PtrMetadata"
  | TError _ ->
      [%craise_opt_span] span "Found type error in the output of charon"

and translate_fwd_generic_args (span : Meta.span option)
    (decls_ctx : C.decls_ctx) (generics : T.generic_args) : generic_args =
  translate_generic_args span (translate_fwd_ty span decls_ctx) generics

and translate_fwd_trait_ref (span : Meta.span option) (decls_ctx : C.decls_ctx)
    (tr : T.trait_ref) : trait_ref =
  translate_trait_ref span (translate_fwd_ty span decls_ctx) tr

(** Compute the *number* of levels of sub-abstractions existing for a given
    region type. *)
and compute_back_ty_num_levels (span : Meta.span option)
    (decls_ctx : C.decls_ctx) (get_region_group : T.region -> T.region_group_id)
    (gid : T.region_group_id) (ty : T.ty) : int =
  let type_infos = decls_ctx.type_ctx.type_infos in
  let keep_region r = gid = get_region_group r in
  let max_level = ref 0 in
  let save_count (outer_regions : T.RegionGroupId.Set.t) =
    let n = T.RegionGroupId.Set.cardinal outer_regions in
    if !max_level < n then max_level := n
  in
  (* outer_regions: whenever we dive into a borrow for a given region group, we push
     the region group to remember it - this allows us to track the nesting level. *)
  let rec explore (outer_regions : T.RegionGroupId.Set.t) (ty : T.ty) : unit =
    [%ldebug
      let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
      "Exploring (group id: "
      ^ T.RegionGroupId.to_string gid
      ^ "): "
      ^ Print.Types.ty_to_string ctx ty
      ^ "\n- outer_regions: "
      ^ T.RegionGroupId.Set.to_string None outer_regions];
    match ty with
    | T.TAdt { id; generics } -> (
        match id with
        | TAdtId _ ->
            (* Analyze the type *)
            let info = TypesAnalysis.analyze_ty span type_infos ty in
            (* TODO: we need to extend the type analysis to count the level
               of nesting inside of ADTs with regions. For now we forbid using
               nested mutable borrows inside of ADTs. *)
            [%cassert_opt_span] span
              (not info.contains_nested_mut)
              "Unimplemented";
            (* Check if the region appears somewhere *)
            let outer_regions =
              if
                TypesUtils.ty_has_mut_borrow_for_region_in_pred type_infos
                  keep_region ty
              then T.RegionGroupId.Set.add gid outer_regions
              else outer_regions
            in
            save_count outer_regions
        | TBuiltin TStr -> save_count outer_regions
        | TBuiltin TBox -> (
            (* Eliminate the box *)
            match generics.types with
            | [ bty ] -> explore outer_regions bty
            | _ ->
                [%craise_opt_span] span
                  "Unreachable: boxes receive exactly one type parameter")
        | TTuple -> List.iter (explore outer_regions) generics.types)
    | T.TArray (ty, _) | T.TSlice ty -> explore outer_regions ty
    | TVar _ | TNever | TLiteral _ -> save_count outer_regions
    | TRef (r, rty, rkind) -> (
        match rkind with
        | RShared ->
            (* Stop here *)
            (* We just check there are no mutable references below the shared reference *)
            [%cassert_opt_span] span
              (not
                 (TypesUtils.ty_has_mut_borrow_for_region_in_pred type_infos
                    keep_region rty))
              "Unimplemented";
            save_count outer_regions
        | RMut ->
            [%ldebug "RMut"];
            (* Dive in, remembering the fact that we are inside a mutable borrow.

               Note that we dive in if it is a region to keep, or if it is an ancestor
               region (it is if it contains a type with a region to keep). *)
            let is_ancestor_region =
              TypesUtils.ty_has_mut_borrow_for_region_in_pred type_infos
                keep_region rty
            in
            let keep = keep_region r in
            [%ldebug
              "- is_ancestor_region: "
              ^ string_of_bool is_ancestor_region
              ^ "\n- keep_region: " ^ string_of_bool keep];
            if keep then
              (* Stop there, but save the region *)
              save_count (T.RegionGroupId.Set.add gid outer_regions)
            else if is_ancestor_region then
              (* Continue, but save the region *)
              let outer_regions =
                T.RegionGroupId.Set.add (get_region_group r) outer_regions
              in
              explore outer_regions rty
            else
              (* We can stop there *)
              save_count outer_regions)
    | TRawPtr _ ->
        (* TODO: not sure what to do here *)
        save_count outer_regions
    | TTraitType (trait_ref, _) ->
        [%sanity_check_opt_span] span
          (TypesUtils.trait_ref_kind_is_local_clause_or_builtin trait_ref.kind);
        save_count outer_regions
    | TFnDef _ | TFnPtr _ ->
        [%craise_opt_span] span "Arrow types are not supported yet"
    | TDynTrait _ ->
        [%craise_opt_span] span "Dynamic trait types are not supported yet"
    | TPtrMetadata _ -> [%craise_opt_span] span "unsupported: PtrMetadata"
    | TError _ ->
        [%craise_opt_span] span "Found type error in the output of charon"
  in
  explore T.RegionGroupId.Set.empty ty;
  !max_level

(** Auxiliary function to compute the type consumed or given back by a backward
    function.

    We leverage the fact that we can factor out the logic in one place (the
    consumed type and the given back type derive from the nesting level in more
    or less the same way). *)
and translate_back_ty_aux (span : Meta.span option) (decls_ctx : C.decls_ctx)
    (get_region_group : T.region -> T.region_group_id) (gid : T.region_group_id)
    (level : int) (ty : T.ty) : ty option =
  let type_infos = decls_ctx.type_ctx.type_infos in
  let keep_region r = gid = get_region_group r in
  let keep (outer_regions : T.RegionGroupId.Set.t) : bool =
    T.RegionGroupId.Set.cardinal outer_regions > level
  in
  let stop (outer_regions : T.RegionGroupId.Set.t) (ty : T.ty) : ty option =
    if keep outer_regions then Some (translate_fwd_ty span decls_ctx ty)
    else None
  in
  let keep_adt (outer_regions : T.RegionGroupId.Set.t) (ty : T.ty) : bool =
    (* Analyze the type *)
    let info = TypesAnalysis.analyze_ty span type_infos ty in
    (* TODO: we need to extend the type analysis to count the level
         of nesting inside of ADTs with regions. For now we forbid using
         nested mutable borrows inside of ADTs. *)
    [%cassert_opt_span] span (not info.contains_nested_mut) "Unimplemented";
    (* Check if the region appears somewhere *)
    let outer_regions =
      if
        TypesUtils.ty_has_mut_borrow_for_region_in_pred type_infos keep_region
          ty
      then T.RegionGroupId.Set.add gid outer_regions
      else outer_regions
    in
    (* *)
    keep outer_regions
  in
  (* inside_mut_level: keeps track of the nesting level. We only count the
     ancestor regions and the current regions (not the inner regions) *)
  let rec explore (outer_regions : T.RegionGroupId.Set.t) (ty : T.ty) :
      ty option =
    [%ldebug
      let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
      "Exploring: "
      ^ Print.Types.ty_to_string ctx ty
      ^ "\n- outer_regions: "
      ^ T.RegionGroupId.Set.to_string None outer_regions];
    match ty with
    | T.TAdt { id = TTuple; generics } -> (
        (* Tuples can contain borrows (which we eliminate).

         Note that no borrow gets eliminated if we are already inside a
         mutable borrow, at the proper level. *)
        let tys_t = List.filter_map (explore outer_regions) generics.types in
        match tys_t with
        | [] -> None
        | _ ->
            (* Note that if there is exactly one type, [mk_simpl_tuple_ty]
             * is the identity *)
            Some (mk_simpl_tuple_ty tys_t))
    | T.TAdt { id; generics } when keep_adt outer_regions ty -> (
        match id with
        | TAdtId _ ->
            (* The type should contain a mutable reference for the proper
             level: translate it as a forward type *)
            let type_id = translate_type_id span id in
            let generics = translate_fwd_generic_args span decls_ctx generics in
            Some (TAdt (type_id, generics))
        | TBuiltin TStr -> stop outer_regions ty
        | TBuiltin TBox -> (
            (* Eliminate the box *)
            match generics.types with
            | [ bty ] -> explore outer_regions bty
            | _ ->
                [%craise_opt_span] span
                  "Unreachable: boxes receive exactly one type parameter")
        | TTuple -> [%internal_error_opt_span] span)
    | T.TAdt _ -> None
    | T.TArray _ | T.TSlice _ ->
        if keep_adt outer_regions ty then
          Some (translate_fwd_ty span decls_ctx ty)
        else None
    | TVar _ | TNever | TLiteral _ -> stop outer_regions ty
    | TRef (r, rty, rkind) -> (
        match rkind with
        | RShared ->
            (* Ignore shared references, unless we are below a mutable borrow *)
            (* TODO: check regions like in the mutable case *)
            stop outer_regions ty
        | RMut ->
            [%ldebug "RMut"];
            (* Dive in, remembering the fact that we are inside a mutable borrow.

               Note that we dive in if it is a region to keep, or if it is an ancestor
               region (it is if it contains a type with a region to keep). *)
            let is_ancestor_region =
              TypesUtils.ty_has_mut_borrow_for_region_in_pred type_infos
                keep_region rty
            in
            let keep = keep_region r in
            [%ldebug
              "- is_ancestor_region: "
              ^ string_of_bool is_ancestor_region
              ^ "\n- keep_region: " ^ string_of_bool keep];
            if is_ancestor_region then
              (* Dive *)
              let outer_regions =
                T.RegionGroupId.Set.add (get_region_group r) outer_regions
              in
              explore outer_regions rty
            else if keep then
              (* We stop here *)
              let outer_regions =
                T.RegionGroupId.Set.add (get_region_group r) outer_regions
              in
              stop outer_regions rty
            else None)
    | TRawPtr _ ->
        (* TODO: not sure what to do here *)
        stop outer_regions ty
    | TTraitType (trait_ref, _) ->
        [%sanity_check_opt_span] span
          (TypesUtils.trait_ref_kind_is_local_clause_or_builtin trait_ref.kind);
        stop outer_regions ty
    | TFnDef _ | TFnPtr _ ->
        [%craise_opt_span] span "Arrow types are not supported yet"
    | TDynTrait _ ->
        [%craise_opt_span] span "Dynamic trait types are not supported yet"
    | TPtrMetadata _ -> [%craise_opt_span] span "unsupported: PtrMetadata"
    | TError _ ->
        [%craise_opt_span] span "Found type error in the output of charon"
  in
  explore T.RegionGroupId.Set.empty ty

(** Compute the number of levels required to translate a signature *)
and compute_back_tys_num_levels (span : Meta.span option)
    (decls_ctx : C.decls_ctx) (get_region_group : T.region -> T.region_group_id)
    (gid : T.region_group_id) (inputs : T.ty list) (output : T.ty) : int =
  let max x y = if x > y then x else y in
  let max_inputs = ref 0 in
  List.iter
    (fun ty ->
      let n =
        compute_back_ty_num_levels span decls_ctx get_region_group gid ty
      in
      max_inputs := max n !max_inputs)
    inputs;
  let output =
    compute_back_ty_num_levels span decls_ctx get_region_group gid output
  in
  max !max_inputs output

and translate_back_output_ty (span : Meta.span option) (decls_ctx : C.decls_ctx)
    (get_region_group : T.region -> T.region_group_id) (gid : T.region_group_id)
    (level : int) ~(from_input : bool) (ty : T.ty) : ty option =
  if (not from_input) && level = 0 then None
  else translate_back_ty_aux span decls_ctx get_region_group gid level ty

(** Translate the input type of a backward function, for a given region group.

    We return an option, because the translated type may be empty. *)
and translate_back_input_ty (span : Meta.span option) (decls_ctx : C.decls_ctx)
    (get_region_group : T.region -> T.region_group_id) (gid : T.region_group_id)
    (level : int) ~(from_input : bool) (ty : T.ty) : ty option =
  if from_input && level = 0 then None
  else translate_back_ty_aux span decls_ctx get_region_group gid level ty

(** Small utility. *)
and compute_raw_fun_effect_info (span : Meta.span option)
    (fun_infos : fun_info A.FunDeclId.Map.t) (fun_id : A.fn_ptr_kind)
    (gid : T.RegionGroupId.id option) : fun_effect_info =
  match fun_id with
  | TraitMethod (_, _, fid) | FunId (FRegular fid) ->
      let info =
        [%silent_unwrap_opt_span] span (A.FunDeclId.Map.find_opt fid fun_infos)
      in
      {
        (* Note that backward functions can't fail *)
        can_fail = info.can_fail && gid = None;
        can_diverge = info.can_diverge;
        is_rec = info.is_rec && gid = None;
      }
  | FunId (FBuiltin aid) ->
      {
        (* Note that backward functions can't fail *)
        can_fail = Builtin.builtin_fun_can_fail aid && gid = None;
        can_diverge = false;
        is_rec = false;
      }

(** Translate an instantiated function signature to a decomposed function
    signature.

    Note that the function also takes a list of names for the inputs, and
    computes, for every output for the backward functions, a corresponding name
    (outputs for backward functions come from borrows in the inputs of the
    forward function) which we use as hints to generate pretty names in the
    extracted code.

    Remark: as we take as input an instantiated function signature, we assume
    the types have already been normalized.

    - [generic_args]: the generic arguments with which the uninstantiated
      signature was instantiated, leading to the current [sg] *)
and translate_inst_fun_sig_to_decomposed_fun_type (span : Meta.span option)
    (decls_ctx : C.decls_ctx) (fun_id : A.fn_ptr_kind) (sg : A.inst_fun_sig)
    (input_names : string option list) : decomposed_fun_type =
  [%ltrace
    let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
    "- sg.regions_hierarchy: "
    ^ Print.Values.abs_region_groups_to_string sg.abs_regions_hierarchy
    ^ "\n- inst_sg (inputs, output): "
    ^ Print.Values.inst_fun_sig_to_string ctx sg];

  let fun_infos = decls_ctx.fun_ctx.fun_infos in

  (* We need an evaluation context to normalize the types (to normalize the
     associated types, etc. - for instance it may happen that the types
     refer to the types associated to a trait ref, but where the trait ref
     is a known impl). *)

  (* Is the forward function stateful, and can it fail? *)
  let fwd_effect_info =
    compute_raw_fun_effect_info span fun_infos fun_id None
  in
  (* Compute the forward inputs *)
  let fwd_inputs = List.map (translate_fwd_ty span decls_ctx) sg.inputs in
  (* Compute the backward output, without the effect information *)
  let fwd_output = translate_fwd_ty span decls_ctx sg.output in

  (* Compute the map from region id to region group id *)
  let rg_to_gr_id =
    T.RegionId.Map.of_list
      (List.flatten
         (List.map
            (fun (gr : T.region_var_group) ->
              List.map (fun rid -> (rid, gr.id)) gr.regions)
            sg.regions_hierarchy))
  in
  let get_region_group (r : T.region) : T.RegionGroupId.id =
    match r with
    | T.RStatic -> [%craise_opt_span] span "Unimplemented: static region"
    | RErased -> [%craise_opt_span] span "Unexpected erased region"
    | RVar (Bound _ as var) ->
        [%craise_opt_span] span
          ("Unexpected bound region: "
          ^ Charon.PrintTypes.region_db_var_to_pretty_string var)
    | RBody _ -> [%craise_opt_span] None "unsupported: Body region"
    | RVar (Free rid) -> (
        match T.RegionId.Map.find_opt rid rg_to_gr_id with
        | Some gr -> gr
        | None -> [%internal_error_opt_span] span)
  in

  (* Compute the type information for the backward function *)
  (* Small helper to translate types for backward functions.
     - [to_input] controls whether we compute an input type or an output type.
     - [from_input] should be [true] if we compute from a type of an input argument,
       and [false] if we compute from the output type of the function. *)
  let translate_back_inputs_or_outputs_for_gid ~(to_input : bool)
      (gid : T.RegionGroupId.id) : (abs_level * (string option * ty) list) list
      =
    (* Translate the inputs level by level, starting with the highest level *)
    let num_levels =
      compute_back_tys_num_levels span decls_ctx get_region_group gid sg.inputs
        sg.output
    in
    let translate_ty ~from_input level =
      if to_input then
        translate_back_input_ty span decls_ctx get_region_group gid level
          ~from_input
      else
        translate_back_output_ty span decls_ctx get_region_group gid level
          ~from_input
    in
    let translate_level (level : int) :
        (abs_level * (string option * ty) list) option =
      (* Mutable borrows in input types can only lead to more inputs for the backward function.
         The dual is true: mutable borrows in output types can only lead to more outputs for
         the backward function. *)
      let inputs =
        if to_input || level = 0 then List.combine input_names sg.inputs else []
      in
      let outputs =
        if (not to_input) || level = 0 then [ (None, sg.output, false) ] else []
      in
      let tys =
        List.filter_map
          (fun (name, ty, from_input) ->
            let ty = translate_ty ~from_input level ty in
            match ty with
            | None -> None
            | Some ty -> Some (name, ty))
          (List.map (fun (name, ty) -> (name, ty, true)) inputs @ outputs)
      in
      match tys with
      | [] -> None
      | _ -> Some (level, tys)
    in
    let rec translate (current_level : int) :
        (abs_level * (string option * ty) list) list =
      if current_level < 0 then []
      else
        let inner = translate (current_level - 1) in
        match translate_level current_level with
        | None -> inner
        | Some ty -> ty :: inner
    in
    translate (num_levels - 1)
  in
  (* Memoize the results *)
  let gid_to_back_inputs = ref T.RegionGroupId.Map.empty in
  let rec translate_back_inputs_for_gid_aux (gid : T.RegionGroupId.id) :
      (abs_level * (string option * ty) list) list =
    let inputs = translate_back_inputs_or_outputs_for_gid ~to_input:true gid in

    [%ltrace
      let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
      let pctx = PrintPure.decls_ctx_to_fmt_env decls_ctx in
      let output = Print.Types.ty_to_string ctx sg.output in
      let inputs =
        Print.list_to_string
          (fun (lvl, ty) ->
            string_of_int lvl ^ " -> "
            ^ Print.list_to_string
                (fun (_, ty) -> PrintPure.ty_to_string pctx false ty)
                ty)
          inputs
      in
      "translate_back_inputs_for_gid:" ^ "\n- function:"
      ^ Charon.PrintTypes.fn_ptr_kind_to_string ctx fun_id
      ^ "\n- gid: "
      ^ RegionGroupId.to_string gid
      ^ "\n- output: " ^ output ^ "\n- back inputs: " ^ inputs];
    inputs
  and translate_back_inputs_for_gid (gid : T.RegionGroupId.id) :
      (abs_level * (string option * ty) list) list =
    match T.RegionGroupId.Map.find_opt gid !gid_to_back_inputs with
    | Some tys -> tys
    | None ->
        let tys = translate_back_inputs_for_gid_aux gid in
        gid_to_back_inputs :=
          T.RegionGroupId.Map.add gid tys !gid_to_back_inputs;
        tys
  in
  let compute_back_outputs_for_gid (gid : RegionGroupId.id) :
      (abs_level * (string option * ty) list) list =
    let outputs =
      translate_back_inputs_or_outputs_for_gid ~to_input:false gid
    in
    [%ltrace
      let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
      let pctx = PrintPure.decls_ctx_to_fmt_env decls_ctx in
      let inputs =
        Print.list_to_string (Print.Types.ty_to_string ctx) sg.inputs
      in
      let outputs =
        Print.list_to_string
          (fun (lvl, ty) ->
            string_of_int lvl ^ " -> "
            ^ Print.list_to_string
                (fun (_, ty) -> PrintPure.ty_to_string pctx false ty)
                ty)
          outputs
      in
      "compute_back_outputs_for_gid:" ^ "\n- function:"
      ^ Charon.PrintTypes.fn_ptr_kind_to_string ctx fun_id
      ^ "\n- gid: "
      ^ RegionGroupId.to_string gid
      ^ "\n- inputs: " ^ inputs ^ "\n- back outputs: " ^ outputs];
    outputs
  in
  let compute_back_info_for_group (rg : T.region_var_group) :
      RegionGroupId.id * back_sg_info =
    let gid = rg.id in
    let back_effect_info =
      compute_raw_fun_effect_info span fun_infos fun_id (Some gid)
    in
    let inputs = translate_back_inputs_for_gid gid in
    (* We consider a backward function as stateful and potentially failing
       **only if it has inputs** (for the "potentially failing": if it has
       not inputs, we directly evaluate it in the body of the forward function).

       For instance, we do the following:
       {[
         // Rust
         fn push<T, 'a>(v : &mut Vec<T>, x : T) { ... }

         (* Generated code: before doing unit elimination.
            We return (), as well as the backward function; as the backward
            function doesn't consume any inputs, it is a value that we compute
            directly in the body of [push].
          *)
         let push T (v : Vec T) (x : T) : Result (() * Vec T) = ...

         (* Generated code: after doing unit elimination, if we simplify the merged
            fwd/back functions (see below). *)
         let push T (v : Vec T) (x : T) : Result (Vec T) = ...
       ]}
    *)
    let back_effect_info =
      let b = inputs <> [] in
      { back_effect_info with can_fail = back_effect_info.can_fail && b }
    in
    let outputs = compute_back_outputs_for_gid gid in
    let filter =
      !Config.simplify_merged_fwd_backs && inputs = [] && outputs = []
    in
    let info = { inputs; outputs; effect_info = back_effect_info; filter } in
    (gid, info)
  in
  let back_sg =
    RegionGroupId.Map.of_list
      (List.map compute_back_info_for_group sg.regions_hierarchy)
  in

  (* The additional information about the forward function *)
  let fwd_info : fun_sig_info =
    let ignore_output =
      if !Config.simplify_merged_fwd_backs then
        ty_is_unit fwd_output
        && List.exists
             (fun (info : back_sg_info) -> not info.filter)
             (RegionGroupId.Map.values back_sg)
      else false
    in
    { effect_info = fwd_effect_info; ignore_output }
  in

  (* Return *)
  { fwd_inputs; fwd_output; back_sg; fwd_info }

and translate_fun_sig_with_regions_hierarchy_to_decomposed (span : span option)
    (decls_ctx : C.decls_ctx) (fun_id : A.fn_ptr_kind)
    (regions_hierarchy : T.region_var_groups) (sg : A.bound_fun_sig)
    (input_names : string option list) : decomposed_fun_sig =
  let inst_sg : LlbcAst.inst_fun_sig =
    let ({ T.inputs; output; _ } : T.fun_sig) = sg.item_binder_value in
    [%sanity_check_opt_span] span
      (sg.item_binder_params.trait_type_constraints = []);

    let _, fresh_abs_id = V.AbsId.fresh_stateful_generator () in
    let region_gr_id_abs_id_list =
      List.map
        (fun (rg : T.region_var_group) -> (rg.id, fresh_abs_id ()))
        regions_hierarchy
    in
    let region_gr_id_to_abs =
      RegionGroupId.Map.of_list region_gr_id_abs_id_list
    in
    let region_id_to_abs id = RegionGroupId.Map.find id region_gr_id_to_abs in
    let abs_regions_hierarchy =
      List.map
        (fun (rg : T.region_var_group) ->
          let id = region_id_to_abs rg.id in
          let parents = List.map region_id_to_abs rg.parents in
          { T.id; parents; regions = rg.regions })
        regions_hierarchy
    in
    (* We need to introduce region abstraction ids *)
    {
      regions_hierarchy;
      abs_regions_hierarchy;
      trait_type_constraints = [];
      inputs;
      output;
    }
  in

  (* Generic parameters *)
  let generics, preds = translate_generic_params span sg.item_binder_params in

  let fun_ty =
    translate_inst_fun_sig_to_decomposed_fun_type span decls_ctx fun_id inst_sg
      input_names
  in
  { generics; llbc_generics = sg.item_binder_params; preds; fun_ty }

and translate_fun_sig_to_decomposed (decls_ctx : C.decls_ctx)
    (fun_id : FunDeclId.id) (sg : A.bound_fun_sig)
    (input_names : string option list) : decomposed_fun_sig =
  let span =
    ([%silent_unwrap_opt_span] None
       (FunDeclId.Map.find_opt fun_id decls_ctx.fun_ctx.fun_decls))
      .item_meta
      .span
  in
  (* Retrieve the list of parent backward functions *)
  let regions_hierarchy =
    RegionsHierarchy.compute_regions_hierarchy_for_sig (Some span)
      decls_ctx.crate sg
  in

  translate_fun_sig_with_regions_hierarchy_to_decomposed (Some span) decls_ctx
    (FunId (FRegular fun_id)) regions_hierarchy sg input_names

and translate_fun_sig_from_decl_to_decomposed (decls_ctx : C.decls_ctx)
    (fdef : LlbcAst.fun_decl) : decomposed_fun_sig =
  let input_names =
    match fdef.body with
    | None -> List.map (fun _ -> None) fdef.signature.inputs
    | Some body ->
        List.map
          (fun (v : LlbcAst.local) -> v.name)
          (LlbcAstUtils.fun_body_get_input_vars body)
  in
  let sg =
    translate_fun_sig_to_decomposed decls_ctx fdef.def_id
      (bound_fun_sig_of_decl fdef)
      input_names
  in
  [%ltrace
    "- name: "
    ^ T.show_name fdef.item_meta.name
    ^ "\n- sg:\n"
    ^ PrintPure.decomposed_fun_sig_to_string
        (PrintPure.decls_ctx_to_fmt_env decls_ctx)
        sg];
  sg

and mk_output_ty_from_effect_info (effect_info : fun_effect_info) (ty : ty) : ty
    =
  if effect_info.can_fail then mk_result_ty ty else ty

and mk_back_output_ty_from_effect_info (effect_info : fun_effect_info)
    (inputs : ty list) (ty : ty) : ty =
  if effect_info.can_fail && inputs <> [] then mk_result_ty ty else ty

(** Compute the arrow types for all the backward functions.

    If a backward function has no inputs/outputs we filter it. *)
and compute_back_tys_with_info (dsg : Pure.decomposed_fun_type) :
    (back_sg_info * ty) option list =
  List.map
    (fun (back_sg : back_sg_info) ->
      let effect_info = back_sg.effect_info in
      (* Compute the input/output types *)
      let inputs =
        List.map
          (fun (_, tys) -> mk_simpl_tuple_ty (List.map snd tys))
          back_sg.inputs
      in
      let outputs =
        List.map
          (fun (_, tys) -> mk_simpl_tuple_ty (List.map snd tys))
          back_sg.outputs
      in
      (* Filter if necessary *)
      if !Config.simplify_merged_fwd_backs && inputs = [] && outputs = [] then
        None
      else
        let output = mk_simpl_tuple_ty outputs in
        let output =
          mk_back_output_ty_from_effect_info effect_info inputs output
        in
        let ty = mk_arrows inputs output in
        Some (back_sg, ty))
    (RegionGroupId.Map.values dsg.back_sg)

and compute_back_tys (dsg : Pure.decomposed_fun_type) : ty option list =
  List.map (Option.map snd) (compute_back_tys_with_info dsg)

(** Compute the output type of a function, from a decomposed signature (the
    output type contains the type of the value returned by the forward function
    as well as the types of the returned backward functions). *)
and compute_output_ty_from_decomposed (dsg : Pure.decomposed_fun_type) : ty =
  (* Compute the arrow types for all the backward functions *)
  let back_tys = List.filter_map (fun x -> x) (compute_back_tys dsg) in
  (* Group the forward output and the types of the backward functions *)
  let effect_info = dsg.fwd_info.effect_info in
  let output =
    (* We might need to ignore the output of the forward function
       (if it is unit for instance) *)
    let tys =
      if dsg.fwd_info.ignore_output then back_tys
      else dsg.fwd_output :: back_tys
    in
    mk_simpl_tuple_ty tys
  in
  mk_output_ty_from_effect_info effect_info output

and translate_fun_sig_from_decomposed (dsg : Pure.decomposed_fun_sig) : fun_sig
    =
  let generics = dsg.generics in
  let llbc_generics = dsg.llbc_generics in
  let preds = dsg.preds in
  (* Compute the effects info *)
  let fwd_info = dsg.fun_ty.fwd_info in
  let back_effect_info =
    RegionGroupId.Map.of_list
      (List.map
         (fun ((gid, info) : RegionGroupId.id * back_sg_info) ->
           (gid, info.effect_info))
         (RegionGroupId.Map.bindings dsg.fun_ty.back_sg))
  in
  let inputs, output =
    let output = compute_output_ty_from_decomposed dsg.fun_ty in
    let inputs = dsg.fun_ty.fwd_inputs in
    (inputs, output)
  in
  (* Compute which input type parameters are explicit/implicit *)
  let explicit_info = compute_explicit_info generics inputs in
  let known_from_trait_refs = compute_known_info explicit_info generics in
  (* Put together *)
  {
    generics;
    explicit_info;
    known_from_trait_refs;
    llbc_generics;
    preds;
    inputs;
    output;
    fwd_info;
    back_effect_info;
  }

and translate_fun_sig (decls_ctx : C.decls_ctx) (fun_id : A.fun_id)
    (sg : A.bound_fun_sig) (input_names : string option list) : Pure.fun_sig =
  (* Compute the regions hierarchy *)
  let regions_hierarchy =
    RegionsHierarchy.compute_regions_hierarchy_for_sig None decls_ctx.crate sg
  in
  (* Compute the decomposed fun signature *)
  let sg =
    translate_fun_sig_with_regions_hierarchy_to_decomposed None decls_ctx
      (FunId fun_id) regions_hierarchy sg input_names
  in
  (* Finish the translation *)
  translate_fun_sig_from_decomposed sg

(** TODO: not very clean. *)
and get_fun_effect_info (ctx : bs_ctx) (fun_id : A.fn_ptr_kind)
    (gid : T.RegionGroupId.id option) : fun_effect_info =
  match fun_id with
  | TraitMethod (_, _, fid) | FunId (FRegular fid) ->
      let sg = A.FunDeclId.Map.find fid ctx.fun_sigs in
      let sg = sg.dsg in
      let info =
        match gid with
        | None -> sg.fun_ty.fwd_info.effect_info
        | Some gid -> (RegionGroupId.Map.find gid sg.fun_ty.back_sg).effect_info
      in
      { info with is_rec = info.is_rec && gid = None }
  | FunId (FBuiltin _) ->
      compute_raw_fun_effect_info (Some ctx.span) ctx.fun_ctx.fun_infos fun_id
        gid

(** Simply calls [translate_fwd_ty] *)
let ctx_translate_fwd_ty (ctx : bs_ctx) (ty : T.ty) : ty =
  translate_fwd_ty (Some ctx.span) ctx.decls_ctx ty

(** Simply calls [translate_fwd_generic_args] *)
let ctx_translate_fwd_generic_args (ctx : bs_ctx) (generics : T.generic_args) :
    generic_args =
  translate_fwd_generic_args (Some ctx.span) ctx.decls_ctx generics

(** Simply calls [translate_back_ty] *)
let ctx_translate_back_output_ty (ctx : bs_ctx)
    (get_region_group : T.region -> T.region_group_id) (gid : T.region_group_id)
    (level : int) ~(from_input : bool) (ty : T.ty) : ty option =
  translate_back_output_ty (Some ctx.span) ctx.decls_ctx get_region_group gid
    level ~from_input ty

let mk_type_check_ctx (ctx : bs_ctx) : PureTypeCheck.tc_ctx =
  let const_generics =
    T.ConstGenericVarId.Map.of_list
      (List.map
         (fun (cg : const_generic_param) -> (cg.index, TLiteral cg.ty))
         ctx.sg.generics.const_generics)
  in
  let fenv = ctx.fvars_tys in
  let benv = [] in
  {
    PureTypeCheck.type_decls = ctx.type_ctx.type_decls;
    global_decls = ctx.decls_ctx.crate.global_decls;
    const_generics;
    decls_ctx = ctx.decls_ctx;
    fenv;
    benv;
    pbenv = None;
    bvar_counter = BVarId.zero;
  }

let type_check_pat (ctx : bs_ctx) (v : tpat) : unit =
  let span = ctx.span in
  let ctx = mk_type_check_ctx ctx in
  let _ = PureTypeCheck.check_tpat span ctx v in
  ()

let type_check_texpr (ctx : bs_ctx) (e : texpr) : unit =
  if !Config.type_check_pure_code then
    let span = ctx.span in
    let ctx = mk_type_check_ctx ctx in
    PureTypeCheck.check_texpr span ctx e
