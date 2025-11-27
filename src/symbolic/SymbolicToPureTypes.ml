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

(* Some generic translation functions (we need to translate different "flavours"
   of types: forward types, backward types, etc.) *)
let rec translate_generic_args (span : Meta.span option)
    (translate_ty : T.ty -> ty) (generics : T.generic_args) : generic_args =
  (* We ignore the regions: if they didn't cause trouble for the symbolic execution,
     then everything's fine *)
  let types = List.map translate_ty generics.types in
  let const_generics = generics.const_generics in
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
  | BuiltinOrAuto _ ->
      (* We should have eliminated those in the prepasses *)
      [%craise_opt_span] span
        ("Unhandled `BuiltinOrAuto` for trait "
        ^ TraitDeclId.to_string tref.trait_decl_ref.binder_value.id)
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
          | T.TArray -> TAdt (TBuiltin TArray, generics)
          | T.TSlice -> TAdt (TBuiltin TSlice, generics)
          | T.TStr -> TAdt (TBuiltin TStr, generics)))
  | TVar var ->
      TVar var
      (* Note: the `de_bruijn_id`s are incorrect, see comment on `translate_region_binder` *)
  | TLiteral ty -> TLiteral ty
  | TNever -> [%craise_opt_span] span "Unreachable"
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
  { variant_name; fields; variant_attr_info }

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
       (TypesUtils.type_decl_has_nested_borrows (Some span)
          ctx.type_ctx.type_infos def))
    "ADTs containing borrows are not supported yet";
  let generics, preds = translate_generic_params (Some span) def.generics in
  let explicit_info = compute_explicit_info generics [] in
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
        | T.TArray -> TArray
        | T.TSlice -> TSlice
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
let rec translate_fwd_ty (span : Meta.span option) (type_infos : type_infos)
    (ty : T.ty) : ty =
  let translate = translate_fwd_ty span type_infos in
  match ty with
  | T.TAdt { id; generics } -> (
      let t_generics = translate_fwd_generic_args span type_infos generics in
      (* Eliminate boxes and simplify tuples *)
      match id with
      | TAdtId _ | TBuiltin (TArray | TSlice | TStr) ->
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
  | TVar var -> TVar var
  | TNever -> [%craise_opt_span] span "Unreachable"
  | TLiteral lty -> TLiteral lty
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
      let trait_ref = translate_fwd_trait_ref span type_infos trait_ref in
      TTraitType (trait_ref, type_name)
  | TFnDef _ | TFnPtr _ ->
      [%craise_opt_span] span "Arrow types are not supported yet"
  | TDynTrait _ ->
      [%craise_opt_span] span "Dynamic trait types are not supported yet"
  | TPtrMetadata _ -> [%craise_opt_span] span "unsupported: PtrMetadata"
  | TError _ ->
      [%craise_opt_span] span "Found type error in the output of charon"

and translate_fwd_generic_args (span : Meta.span option)
    (type_infos : type_infos) (generics : T.generic_args) : generic_args =
  translate_generic_args span (translate_fwd_ty span type_infos) generics

and translate_fwd_trait_ref (span : Meta.span option) (type_infos : type_infos)
    (tr : T.trait_ref) : trait_ref =
  translate_trait_ref span (translate_fwd_ty span type_infos) tr

(** Simply calls [translate_fwd_ty] *)
let ctx_translate_fwd_ty (ctx : bs_ctx) (ty : T.ty) : ty =
  let type_infos = ctx.type_ctx.type_infos in
  translate_fwd_ty (Some ctx.span) type_infos ty

(** Simply calls [translate_fwd_generic_args] *)
let ctx_translate_fwd_generic_args (ctx : bs_ctx) (generics : T.generic_args) :
    generic_args =
  let type_infos = ctx.type_ctx.type_infos in
  translate_fwd_generic_args (Some ctx.span) type_infos generics

(** Translate a type, when some regions may have ended.

    We return an option, because the translated type may be empty.

    [inside_mut]: are we inside a mutable borrow? *)
let rec translate_back_ty (span : Meta.span option) (type_infos : type_infos)
    (keep_region : T.region -> bool) (inside_mut : bool) (ty : T.ty) : ty option
    =
  let translate = translate_back_ty span type_infos keep_region inside_mut in
  (* A small helper for "leave" types *)
  let wrap ty = if inside_mut then Some ty else None in
  match ty with
  | T.TAdt { id; generics } -> (
      match id with
      | TAdtId _ | TBuiltin (TArray | TSlice | TStr) ->
          let type_id = translate_type_id span id in
          if inside_mut then
            (* We do not want to filter anything, so we translate the generics
               as "forward" types *)
            let generics =
              translate_fwd_generic_args span type_infos generics
            in
            Some (TAdt (type_id, generics))
          else if
            (* If not inside a mutable reference: check if the type contains
               a mutable reference (through one of its generics, inside
               its definition, etc.).
               If yes, keep the whole type, and translate all the generics as
               "forward" types (the backward function will extract the proper
               information from the ADT value).
            *)
            TypesUtils.ty_has_mut_borrow_for_region_in_pred type_infos
              keep_region ty
          then
            let generics =
              translate_fwd_generic_args span type_infos generics
            in
            Some (TAdt (type_id, generics))
          else None
      | TBuiltin TBox -> (
          (* Eliminate the box *)
          match generics.types with
          | [ bty ] -> translate bty
          | _ ->
              [%craise_opt_span] span
                "Unreachable: boxes receive exactly one type parameter")
      | TTuple -> (
          if inside_mut then
            (* We do not filter anything *)
            let tys_t =
              List.map (translate_fwd_ty span type_infos) generics.types
            in
            Some (mk_simpl_tuple_ty tys_t)
          else
            (* Tuples can contain borrows (which we eliminate) *)
            let tys_t = List.filter_map translate generics.types in
            match tys_t with
            | [] -> None
            | _ ->
                (* Note that if there is exactly one type, [mk_simpl_tuple_ty]
                 * is the identity *)
                Some (mk_simpl_tuple_ty tys_t)))
  | TVar var -> wrap (TVar var)
  | TNever -> [%craise_opt_span] span "Unreachable"
  | TLiteral lty -> wrap (TLiteral lty)
  | TRef (r, rty, rkind) -> (
      match rkind with
      | RShared ->
          (* Ignore shared references, unless we are below a mutable borrow *)
          if inside_mut then translate rty else None
      | RMut ->
          (* Dive in, remembering the fact that we are inside a mutable borrow *)
          let inside_mut = true in
          if keep_region r then
            translate_back_ty span type_infos keep_region inside_mut rty
          else None)
  | TRawPtr _ ->
      (* TODO: not sure what to do here *)
      None
  | TTraitType (trait_ref, type_name) ->
      [%sanity_check_opt_span] span
        (TypesUtils.trait_ref_kind_is_local_clause trait_ref.kind);
      if inside_mut then
        (* Translate the trait ref as a "forward" trait ref -
           we do not want to filter any type *)
        let trait_ref = translate_fwd_trait_ref span type_infos trait_ref in
        Some (TTraitType (trait_ref, type_name))
      else None
  | TFnDef _ | TFnPtr _ ->
      [%craise_opt_span] span "Arrow types are not supported yet"
  | TDynTrait _ ->
      [%craise_opt_span] span "Dynamic trait types are not supported yet"
  | TPtrMetadata _ -> [%craise_opt_span] span "unsupported: PtrMetadata"
  | TError _ ->
      [%craise_opt_span] span "Found type error in the output of charon"

(** Simply calls [translate_back_ty] *)
let ctx_translate_back_ty (ctx : bs_ctx) (keep_region : 'r -> bool)
    (inside_mut : bool) (ty : T.ty) : ty option =
  let type_infos = ctx.type_ctx.type_infos in
  translate_back_ty (Some ctx.span) type_infos keep_region inside_mut ty

let mk_type_check_ctx (ctx : bs_ctx) : PureTypeCheck.tc_ctx =
  let const_generics =
    T.ConstGenericVarId.Map.of_list
      (List.map
         (fun (cg : T.const_generic_param) ->
           (cg.index, ctx_translate_fwd_ty ctx (T.TLiteral cg.ty)))
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

(** Small utility. *)
let compute_raw_fun_effect_info (span : Meta.span option)
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
let translate_inst_fun_sig_to_decomposed_fun_type (span : Meta.span option)
    (decls_ctx : C.decls_ctx) (fun_id : A.fn_ptr_kind) (sg : A.inst_fun_sig)
    (input_names : string option list) : decomposed_fun_type =
  [%ltrace
    let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
    "- sg.regions_hierarchy: "
    ^ Print.Values.abs_region_groups_to_string sg.abs_regions_hierarchy
    ^ "\n- inst_sg (inputs, output): "
    ^ Print.Values.inst_fun_sig_to_string ctx sg];

  let fun_infos = decls_ctx.fun_ctx.fun_infos in
  let type_infos = decls_ctx.type_ctx.type_infos in

  (* We need an evaluation context to normalize the types (to normalize the
     associated types, etc. - for instance it may happen that the types
     refer to the types associated to a trait ref, but where the trait ref
     is a known impl). *)

  (* Is the forward function stateful, and can it fail? *)
  let fwd_effect_info =
    compute_raw_fun_effect_info span fun_infos fun_id None
  in
  (* Compute the forward inputs *)
  let fwd_inputs = List.map (translate_fwd_ty span type_infos) sg.inputs in
  (* Compute the backward output, without the effect information *)
  let fwd_output = translate_fwd_ty span type_infos sg.output in

  (* Compute the type information for the backward function *)
  (* Small helper to translate types for backward functions *)
  let translate_back_ty_for_gid (gid : T.RegionGroupId.id) (ty : T.ty) :
      ty option =
    let rg = T.RegionGroupId.nth sg.regions_hierarchy gid in
    (* Compute the set of regions belonging to this group *)
    let gr_regions = T.RegionId.Set.of_list rg.regions in
    let keep_region r =
      match r with
      | T.RStatic -> [%craise_opt_span] span "Unimplemented: static region"
      | RErased -> [%craise_opt_span] span "Unexpected erased region"
      | RVar (Bound _ as var) ->
          [%craise_opt_span] span
            ("Unexpected bound region: "
            ^ Charon.PrintTypes.region_db_var_to_pretty_string var)
      | RVar (Free rid) -> T.RegionId.Set.mem rid gr_regions
    in
    let inside_mut = false in
    translate_back_ty span type_infos keep_region inside_mut ty
  in
  (* Memoize the results *)
  let gid_to_back_inputs = ref T.RegionGroupId.Map.empty in
  let rec translate_back_inputs_for_gid_aux (gid : T.RegionGroupId.id) : ty list
      =
    (* For now we don't support nested mutable borrows, so we check that if
       there are parent regions they don't consume anything *)
    let parents = list_ancestor_region_groups sg.regions_hierarchy gid in
    T.RegionGroupId.Set.iter
      (fun gid ->
        let tys = translate_back_inputs_for_gid gid in
        [%classert_opt_span] span (tys = [])
          (lazy
            (let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
             "Nested borrows are not supported yet (found in the signature of: "
             ^ Charon.PrintTypes.fn_ptr_kind_to_string ctx fun_id
             ^ ")")))
      parents;
    (* For now, we don't allow nested borrows, so the additional inputs to the
       backward function can only come from borrows that were returned like
       in (for the backward function we introduce for 'a):
       {[
         fn f<'a>(...) -> &'a mut u32;
       ]}
       Upon ending the abstraction for 'a, we need to get back the borrow
       the function returned.
    *)
    let inputs =
      List.filter_map (translate_back_ty_for_gid gid) [ sg.output ]
    in
    [%ltrace
      let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
      let pctx = PrintPure.decls_ctx_to_fmt_env decls_ctx in
      let output = Print.Types.ty_to_string ctx sg.output in
      let inputs =
        Print.list_to_string (PrintPure.ty_to_string pctx false) inputs
      in
      "translate_back_inputs_for_gid:" ^ "\n- function:"
      ^ Charon.PrintTypes.fn_ptr_kind_to_string ctx fun_id
      ^ "\n- gid: "
      ^ RegionGroupId.to_string gid
      ^ "\n- output: " ^ output ^ "\n- back inputs: " ^ inputs];
    inputs
  and translate_back_inputs_for_gid (gid : T.RegionGroupId.id) : ty list =
    match T.RegionGroupId.Map.find_opt gid !gid_to_back_inputs with
    | Some tys -> tys
    | None ->
        let tys = translate_back_inputs_for_gid_aux gid in
        gid_to_back_inputs :=
          T.RegionGroupId.Map.add gid tys !gid_to_back_inputs;
        tys
  in
  let compute_back_outputs_for_gid (gid : RegionGroupId.id) :
      string option list * ty list =
    (* The outputs are the borrows inside the regions of the abstractions
       and which are present in the input values. For instance, see:
       {[
         fn f<'a>(x : &'a mut u32) -> ...;
       ]}
       Upon ending the abstraction for 'a, we give back the borrow which
       was consumed through the [x] parameter.
    *)
    let outputs =
      List.map
        (fun (name, input_ty) -> (name, translate_back_ty_for_gid gid input_ty))
        (List.combine input_names sg.inputs)
    in
    (* Filter *)
    let outputs =
      List.filter (fun (_, opt_ty) -> Option.is_some opt_ty) outputs
    in
    let outputs =
      List.map (fun (name, opt_ty) -> (name, Option.get opt_ty)) outputs
    in
    let names, outputs = List.split outputs in
    [%ltrace
      let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
      let pctx = PrintPure.decls_ctx_to_fmt_env decls_ctx in
      let inputs =
        Print.list_to_string (Print.Types.ty_to_string ctx) sg.inputs
      in
      let outputs =
        Print.list_to_string (PrintPure.ty_to_string pctx false) outputs
      in
      "compute_back_outputs_for_gid:" ^ "\n- function:"
      ^ Charon.PrintTypes.fn_ptr_kind_to_string ctx fun_id
      ^ "\n- gid: "
      ^ RegionGroupId.to_string gid
      ^ "\n- inputs: " ^ inputs ^ "\n- back outputs: " ^ outputs];
    (names, outputs)
  in
  let compute_back_info_for_group (rg : T.region_var_group) :
      RegionGroupId.id * back_sg_info =
    let gid = rg.id in
    let back_effect_info =
      compute_raw_fun_effect_info span fun_infos fun_id (Some gid)
    in
    let inputs = translate_back_inputs_for_gid gid in
    let inputs = List.map (fun ty -> (Some "ret", ty)) inputs in
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
    let output_names, outputs = compute_back_outputs_for_gid gid in
    let filter =
      !Config.simplify_merged_fwd_backs && inputs = [] && outputs = []
    in
    let info =
      { inputs; outputs; output_names; effect_info = back_effect_info; filter }
    in
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

let translate_fun_sig_with_regions_hierarchy_to_decomposed (span : span option)
    (decls_ctx : C.decls_ctx) (fun_id : A.fn_ptr_kind)
    (regions_hierarchy : T.region_var_groups) (sg : A.fun_sig)
    (input_names : string option list) : decomposed_fun_sig =
  let inst_sg : LlbcAst.inst_fun_sig =
    let ({ A.inputs; output; _ } : A.fun_sig) = sg in
    [%sanity_check_opt_span] span (sg.generics.trait_type_constraints = []);

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
  let generics, preds = translate_generic_params span sg.generics in

  let fun_ty =
    translate_inst_fun_sig_to_decomposed_fun_type span decls_ctx fun_id inst_sg
      input_names
  in
  { generics; llbc_generics = sg.generics; preds; fun_ty }

let translate_fun_sig_to_decomposed (decls_ctx : C.decls_ctx)
    (fun_id : FunDeclId.id) (sg : A.fun_sig) (input_names : string option list)
    : decomposed_fun_sig =
  let span =
    ([%silent_unwrap_opt_span] None
       (FunDeclId.Map.find_opt fun_id decls_ctx.fun_ctx.fun_decls))
      .item_meta
      .span
  in
  (* Retrieve the list of parent backward functions *)
  let regions_hierarchy =
    [%silent_unwrap] span
      (FunIdMap.find_opt (FRegular fun_id) decls_ctx.fun_ctx.regions_hierarchies)
  in

  translate_fun_sig_with_regions_hierarchy_to_decomposed (Some span) decls_ctx
    (FunId (FRegular fun_id)) regions_hierarchy sg input_names

let translate_fun_sig_from_decl_to_decomposed (decls_ctx : C.decls_ctx)
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
    translate_fun_sig_to_decomposed decls_ctx fdef.def_id fdef.signature
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

let mk_output_ty_from_effect_info (effect_info : fun_effect_info) (ty : ty) : ty
    =
  if effect_info.can_fail then mk_result_ty ty else ty

let mk_back_output_ty_from_effect_info (effect_info : fun_effect_info)
    (inputs : ty list) (ty : ty) : ty =
  if effect_info.can_fail && inputs <> [] then mk_result_ty ty else ty

(** Compute the arrow types for all the backward functions.

    If a backward function has no inputs/outputs we filter it. *)
let compute_back_tys_with_info (dsg : Pure.decomposed_fun_type) :
    (back_sg_info * ty) option list =
  List.map
    (fun (back_sg : back_sg_info) ->
      let effect_info = back_sg.effect_info in
      (* Compute the input/output types *)
      let inputs = List.map snd back_sg.inputs in
      let outputs = back_sg.outputs in
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

let compute_back_tys (dsg : Pure.decomposed_fun_type) : ty option list =
  List.map (Option.map snd) (compute_back_tys_with_info dsg)

(** Compute the output type of a function, from a decomposed signature (the
    output type contains the type of the value returned by the forward function
    as well as the types of the returned backward functions). *)
let compute_output_ty_from_decomposed (dsg : Pure.decomposed_fun_type) : ty =
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

let translate_fun_sig_from_decomposed (dsg : Pure.decomposed_fun_sig) : fun_sig
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

let translate_fun_sig (decls_ctx : C.decls_ctx) (fun_id : A.fun_id)
    (fun_name : string) (sg : A.fun_sig) (input_names : string option list) :
    Pure.fun_sig =
  (* Compute the regions hierarchy *)
  let regions_hierarchy =
    RegionsHierarchy.compute_regions_hierarchy_for_sig None decls_ctx.crate
      fun_name sg
  in
  (* Compute the decomposed fun signature *)
  let sg =
    translate_fun_sig_with_regions_hierarchy_to_decomposed None decls_ctx
      (FunId fun_id) regions_hierarchy sg input_names
  in
  (* Finish the translation *)
  translate_fun_sig_from_decomposed sg

(** TODO: not very clean. *)
let get_fun_effect_info (ctx : bs_ctx) (fun_id : A.fn_ptr_kind)
    (gid : T.RegionGroupId.id option) : fun_effect_info =
  match fun_id with
  | TraitMethod (_, _, fid) | FunId (FRegular fid) ->
      let dsg = A.FunDeclId.Map.find fid ctx.fun_dsigs in
      let info =
        match gid with
        | None -> dsg.fun_ty.fwd_info.effect_info
        | Some gid ->
            (RegionGroupId.Map.find gid dsg.fun_ty.back_sg).effect_info
      in
      { info with is_rec = info.is_rec && gid = None }
  | FunId (FBuiltin _) ->
      compute_raw_fun_effect_info (Some ctx.span) ctx.fun_ctx.fun_infos fun_id
        gid
