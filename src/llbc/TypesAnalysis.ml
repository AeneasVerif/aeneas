open Types
open LlbcAst
open Substitute
open Charon.TypesUtils
open SCC

let log = Logging.types_analysis_log

type subtype_info = {
  under_borrow : bool;  (** Are we inside a borrow? *)
  under_mut_borrow : bool;  (** Are we inside a mut borrow? *)
}
[@@deriving show]

(** See {!type_decl_info} *)
type type_param_info = subtype_info [@@deriving show]

type expl_info = subtype_info [@@deriving show]

type type_borrows_info = {
  contains_static : bool;
      (** Does the type (transitively) contain a static borrow? *)
  contains_borrow : bool;  (** Does the type (transitively) contain a borrow? *)
  contains_mut_borrow : bool;
      (** Does the type (transitively) contain a mutable borrow? *)
  contains_nested_borrows : bool;
      (** Does the type (transitively) contain nested borrows? *)
  contains_borrow_under_mut : bool;
}
[@@deriving show]

(** Generic definition *)
type 'p g_type_info = {
  borrows_info : type_borrows_info;
      (** Various informations about the borrows *)
  param_infos : 'p;  (** Gives information about the type parameters *)
  is_tuple_struct : bool;
      (** If true, it means the type is a record that we should extract as a
          tuple. This field is only valid for type declarations. *)
  mut_regions : RegionId.Set.t;
      (** The set of regions used in mutable borrows *)
}
[@@deriving show]

(** Information about a type definition. *)
type type_decl_info = type_param_info list g_type_info [@@deriving show]

(** Information about a type. *)
type ty_info = type_borrows_info [@@deriving show]

(** Helper definition.

    Allows us to factorize code: {!analyze_full_ty} is used both to analyze type
    definitions and types. *)
type partial_type_info = type_param_info list option g_type_info
[@@deriving show]

type type_infos = type_decl_info TypeDeclId.Map.t [@@deriving show]

let expl_info_init = { under_borrow = false; under_mut_borrow = false }

let type_borrows_info_init : type_borrows_info =
  {
    contains_static = false;
    contains_borrow = false;
    contains_mut_borrow = false;
    contains_nested_borrows = false;
    contains_borrow_under_mut = false;
  }

(** Return true if a type declaration is a structure with unnamed fields.

    Note that there are two possibilities:
    - either all the fields are named
    - or none of the fields are named *)
let type_decl_is_tuple_struct (x : type_decl) : bool =
  match x.kind with
  | Struct fields -> List.for_all (fun f -> f.field_name = None) fields
  | _ -> false

let initialize_g_type_info (is_tuple_struct : bool) (param_infos : 'p) :
    'p g_type_info =
  {
    borrows_info = type_borrows_info_init;
    is_tuple_struct;
    param_infos;
    mut_regions = RegionId.Set.empty;
  }

let initialize_type_decl_info (is_rec : bool) (def : type_decl) : type_decl_info
    =
  let param_info = { under_borrow = false; under_mut_borrow = false } in
  let param_infos = List.map (fun _ -> param_info) def.generics.types in
  let is_tuple_struct =
    !Config.use_tuple_structs && (not is_rec) && type_decl_is_tuple_struct def
  in
  initialize_g_type_info is_tuple_struct param_infos

let type_decl_info_to_partial_type_info (info : type_decl_info) :
    partial_type_info =
  {
    borrows_info = info.borrows_info;
    is_tuple_struct = info.is_tuple_struct;
    param_infos = Some info.param_infos;
    mut_regions = info.mut_regions;
  }

let partial_type_info_to_type_decl_info (info : partial_type_info) :
    type_decl_info =
  {
    borrows_info = info.borrows_info;
    is_tuple_struct = info.is_tuple_struct;
    param_infos = Option.get info.param_infos;
    mut_regions = info.mut_regions;
  }

let partial_type_info_to_ty_info (info : partial_type_info) : ty_info =
  info.borrows_info

let rec trait_instance_id_reducible (span : Meta.span option)
    (id : trait_ref_kind) : bool =
  match id with
  | BuiltinOrAuto _ | TraitImpl _ -> true
  | Self | Clause _ -> false
  | ParentClause (tref, _) -> trait_instance_id_reducible span tref.kind
  | Dyn -> [%craise_opt_span] span "Unreachable"
  | ItemClause _ | UnknownTrait _ -> false

let analyze_full_ty (span : Meta.span option) (updated : bool ref)
    (infos : type_infos) (ty_info : partial_type_info) (ty : ty) :
    partial_type_info =
  (* Small utility *)
  let check_update_bool (original : bool) (nv : bool) : bool =
    if nv && not original then (
      updated := true;
      nv)
    else original
  in
  let r_is_static (r : region) : bool = r = RStatic in
  let update_mut_regions_with_rid mut_regions rid =
    let rid = RegionId.of_int (RegionId.to_int rid) in
    if RegionId.Set.mem rid mut_regions then ty_info.mut_regions
    else (
      updated := true;
      RegionId.Set.add rid mut_regions)
  in
  let update_mut_regions mut_regions mut_region =
    match mut_region with
    | RStatic | RVar (Bound _) ->
        mut_regions (* We can have bound vars because of arrows *)
    | RErased -> [%internal_error_opt_span] span
    | RVar (Free rid) -> update_mut_regions_with_rid mut_regions rid
  in

  (* Update a partial_type_info, while registering if we actually performed an update *)
  let update_ty_info (ty_info : partial_type_info) (mut_region : region option)
      (ty_b_info : type_borrows_info) : partial_type_info =
    let original = ty_info.borrows_info in
    let contains_static =
      check_update_bool original.contains_static ty_b_info.contains_static
    in
    let contains_borrow =
      check_update_bool original.contains_borrow ty_b_info.contains_borrow
    in
    let contains_mut_borrow =
      check_update_bool original.contains_mut_borrow
        ty_b_info.contains_mut_borrow
    in
    let contains_nested_borrows =
      check_update_bool original.contains_nested_borrows
        ty_b_info.contains_nested_borrows
    in
    let contains_borrow_under_mut =
      check_update_bool original.contains_borrow_under_mut
        ty_b_info.contains_borrow_under_mut
    in
    let updated_borrows_info =
      {
        contains_static;
        contains_borrow;
        contains_mut_borrow;
        contains_nested_borrows;
        contains_borrow_under_mut;
      }
    in
    (* Add the region *)
    let updated_mut_regions =
      match mut_region with
      | None -> ty_info.mut_regions
      | Some mut_region -> update_mut_regions ty_info.mut_regions mut_region
    in
    {
      ty_info with
      borrows_info = updated_borrows_info;
      mut_regions = updated_mut_regions;
    }
  in

  (* The recursive function which explores the type *)
  let rec analyze (span : Meta.span option) (expl_info : expl_info)
      (ty_info : partial_type_info) (ty : ty) : partial_type_info =
    match ty with
    | TLiteral _ | TNever | TDynTrait _ -> ty_info
    | TTraitType (tref, _) ->
        (* TODO: normalize the trait types.
           For now we only emit a warning because it makes some tests fail. *)
        [%cassert_warn_opt_span] span
          (not (trait_instance_id_reducible span tref.kind))
          "Found an unexpected trait impl associated type which was not \
           inlined while analyzing a type. This is a case we currently do not \
           handle in all generality. As a result,the consumed/given back \
           values computed for the generated backward functions may be \
           incorrect.";
        ty_info
    | TVar var_id -> (
        (* Update the information for the proper parameter, if necessary *)
        match ty_info.param_infos with
        | None -> ty_info
        | Some param_infos ->
            let param_info =
              TypeVarId.nth param_infos (expect_free_var span var_id)
            in
            (* Set [under_borrow] *)
            let under_borrow =
              check_update_bool param_info.under_borrow expl_info.under_borrow
            in
            (* Set [under_nested_borrows] *)
            let under_mut_borrow =
              check_update_bool param_info.under_mut_borrow
                expl_info.under_mut_borrow
            in
            (* Update param_info *)
            let param_info = { under_borrow; under_mut_borrow } in
            let param_infos =
              TypeVarId.update_nth param_infos
                (expect_free_var span var_id)
                param_info
            in
            let param_infos = Some param_infos in
            { ty_info with param_infos })
    | TRef (r, rty, rkind) ->
        (* Update the type info *)
        let contains_static = r_is_static r in
        let contains_borrow = true in
        let contains_mut_borrow, region =
          match rkind with
          | RMut -> (true, Some r)
          | RShared -> (false, None)
        in
        let contains_nested_borrows = expl_info.under_borrow in
        let contains_borrow_under_mut = expl_info.under_mut_borrow in
        let ty_b_info =
          {
            contains_static;
            contains_borrow;
            contains_mut_borrow;
            contains_nested_borrows;
            contains_borrow_under_mut;
          }
        in
        let ty_info = update_ty_info ty_info region ty_b_info in
        (* Update the exploration info *)
        let expl_info =
          {
            under_borrow = true;
            under_mut_borrow = expl_info.under_mut_borrow || rkind = RMut;
          }
        in
        (* Continue exploring *)
        analyze span expl_info ty_info rty
    | TRawPtr (rty, _) ->
        (* TODO: not sure what to do here *)
        analyze span expl_info ty_info rty
    | TAdt { id = TTuple | TBuiltin (TBox | TSlice | TArray | TStr); generics }
      ->
        (* Nothing to update: just explore the type parameters *)
        List.fold_left
          (fun ty_info ty -> analyze span expl_info ty_info ty)
          ty_info generics.types
    | TAdt { id = TAdtId adt_id; generics } ->
        (* Lookup the information for this type definition *)
        let adt_info =
          [%silent_unwrap_opt_span] span (TypeDeclId.Map.find_opt adt_id infos)
        in
        (* Update the type info with the information from the adt *)
        let ty_info = update_ty_info ty_info None adt_info.borrows_info in
        (* Check if 'static appears in the region parameters *)
        let found_static = List.exists r_is_static generics.regions in
        let borrows_info = ty_info.borrows_info in
        let borrows_info =
          {
            borrows_info with
            contains_static =
              check_update_bool borrows_info.contains_static found_static;
          }
        in
        let ty_info = { ty_info with borrows_info } in
        (* For every instantiated type parameter: update the exploration info
           then explore the type *)
        let params_tys = List.combine adt_info.param_infos generics.types in
        let ty_info =
          List.fold_left
            (fun ty_info (param_info, ty) ->
              (* Update the type info *)
              (* Below: we use only the information which we learn only
               * by taking the type parameter into account. *)
              let contains_static = false in
              let contains_borrow = param_info.under_borrow in
              let contains_mut_borrow = param_info.under_mut_borrow in
              let contains_nested_borrows =
                expl_info.under_borrow && param_info.under_borrow
              in
              let contains_borrow_under_mut =
                expl_info.under_mut_borrow && param_info.under_borrow
              in
              let ty_b_info =
                {
                  contains_static;
                  contains_borrow;
                  contains_mut_borrow;
                  contains_nested_borrows;
                  contains_borrow_under_mut;
                }
              in
              let ty_info = update_ty_info ty_info None ty_b_info in
              (* Update the exploration info *)
              let expl_info =
                {
                  under_borrow =
                    expl_info.under_borrow || param_info.under_borrow;
                  under_mut_borrow =
                    expl_info.under_mut_borrow || param_info.under_mut_borrow;
                }
              in
              (* Continue exploring *)
              analyze span expl_info ty_info ty)
            ty_info params_tys
        in
        (* For every region parameter: do the same *)
        let mut_regions =
          List.fold_left
            (fun mut_regions (adt_rid, r) ->
              (* Check if the region is a variable and is used for mutable borrows *)
              match r with
              | RStatic | RVar (Bound _) | RErased -> mut_regions
              (* We can have bound vars because of arrows, and erased regions
                 when analyzing types appearing in function bodies *)
              | RVar (Free rid) ->
                  if RegionId.Set.mem adt_rid adt_info.mut_regions then
                    update_mut_regions_with_rid mut_regions rid
                  else mut_regions)
            ty_info.mut_regions
            (RegionId.mapi (fun adt_rid r -> (adt_rid, r)) generics.regions)
        in
        (* Return *)
        { ty_info with mut_regions }
    | TFnPtr fn_sig ->
        let inputs, output = fn_sig.binder_value in
        (* Just dive into the arrow *)
        let ty_info =
          List.fold_left
            (fun ty_info ty -> analyze span expl_info ty_info ty)
            ty_info inputs
        in
        analyze span expl_info ty_info output
    | TFnDef _ -> [%craise_opt_span] span "unsupported: FnDef"
    | TPtrMetadata _ -> [%craise_opt_span] span "unsupported: PtrMetadata"
    | TError _ ->
        [%craise_opt_span] span "Found type error in the output of charon"
  in
  (* Explore *)
  analyze span expl_info_init ty_info ty

let type_decl_is_opaque (d : type_decl) : bool =
  match d.kind with
  | Opaque -> true
  | _ -> false

let analyze_type_decl (updated : bool ref) (infos : type_infos)
    (def : type_decl) : type_infos =
  (* We analyze the type declaration only if it is not opaque (we need to explore
   * the variants of the ADTs *)
  if type_decl_is_opaque def then infos
  else
    (* Retrieve all the types of all the fields of all the variants *)
    let fields_tys : ty list =
      match def.kind with
      | Struct fields -> List.map (fun f -> f.field_ty) fields
      | Enum variants ->
          List.concat
            (List.map
               (fun v -> List.map (fun f -> f.field_ty) v.fields)
               variants)
      | Alias _ ->
          [%craise] def.item_meta.span
            "type aliases should have been removed earlier"
      | Union _ -> [%craise] def.item_meta.span "unions are not supported"
      | Opaque | TDeclError _ -> [%craise] def.item_meta.span "unreachable"
    in
    (* Explore the types and accumulate information *)
    let type_decl_info = TypeDeclId.Map.find def.def_id infos in
    let type_decl_info = type_decl_info_to_partial_type_info type_decl_info in
    (* TODO: substitute the types *)
    let type_decl_info =
      List.fold_left
        (fun type_decl_info ty ->
          analyze_full_ty (Some def.item_meta.span) updated infos type_decl_info
            ty)
        type_decl_info fields_tys
    in
    let type_decl_info = partial_type_info_to_type_decl_info type_decl_info in
    (* Update the information for the type definition we explored *)
    let infos = TypeDeclId.Map.add def.def_id type_decl_info infos in
    (* Return *)
    infos

let analyze_type_declaration_group (type_decls : type_decl TypeDeclId.Map.t)
    (infos : type_infos) (decl : type_declaration_group) : type_infos =
  (* Collect the identifiers used in the declaration group *)
  let is_rec, ids =
    match decl with
    | NonRecGroup id -> (false, [ id ])
    | RecGroup ids -> (true, ids)
  in
  (* Retrieve the type definitions *)
  let decl_defs = List.map (fun id -> TypeDeclId.Map.find id type_decls) ids in
  (* Initialize the type information for the current definitions *)
  let infos =
    List.fold_left
      (fun infos (def : type_decl) ->
        TypeDeclId.Map.add def.def_id
          (initialize_type_decl_info is_rec def)
          infos)
      infos decl_defs
  in
  (* Analyze the types - this function simply computes a fixed-point *)
  let updated : bool ref = ref false in
  let rec analyze (infos : type_infos) : type_infos =
    let infos =
      List.fold_left
        (fun infos def -> analyze_type_decl updated infos def)
        infos decl_defs
    in
    if !updated then (
      updated := false;
      analyze infos)
    else infos
  in
  analyze infos

(** Analyze a type to check whether it contains borrows, etc., provided we have
    already analyzed the type definitions in the context. *)
let analyze_ty (span : Meta.span option) (infos : type_infos) (ty : ty) :
    ty_info =
  [%ltrace "ty:\n" ^ show_ty ty];
  (* We don't use [updated] but need to give it as parameter *)
  let updated = ref false in
  (* We don't need to compute whether the type contains 'static or not *)
  let ty_info = initialize_g_type_info false None in
  let ty_info = analyze_full_ty span updated infos ty_info ty in
  (* Convert the ty_info *)
  partial_type_info_to_ty_info ty_info

(** Small helper *)
type region_kind = RkMarked | RkOutlives | RkStatic | RkDefault

(** Given a projection type and a set of regions [regions], compute the set of
    regions which outlive [regions] in this type.

    Note that we ignore the static regions: static regions outlive all other
    regions so in theory we should include them in the outlive type, but in
    practice for now we handle them differently.

    Ex.: compute_outlive_ty {'a} (&'a mut T) = ∅ (the original projection
    projects the borrow, the set of outlive regions is empty)

    compute_outlive_ty {'b} (&'a mut &'b mut T) = {'b} (the original
    projection projects the *outer* borrow, the set of outlive regions
    contains the region of the *inner* borrow)

    compute_outlive_ty {'a} (&'a (Wrapper<'b, T>)) = {'b}
      where struct Wrapper<'a, T>(&'a mut T)
      (the outlive projection projects the region of the borrows inside the ADT) *)
let compute_outlive_proj_ty (span : Meta.span option)
    (type_decls : type_decl TypeDeclId.Map.t) (regions : RegionId.Set.t)
    (ty : ty) : RegionId.Set.t =
  (* The method is as follows:

     1. We visit the type to  compute an "outlive" graph. From the outlive graph
     we can determine whether a region outlives static or a projected region. Note
     that computing this outlive graph is necessary to properly handle outlive
     constraints that are implied, for instance, by ADTs.

     2. From this graph, we then compute the set of regions which outlive a projected region
     and don't outlive 'static ('static has its own treatment).
  *)
  (* The outlive graph. If r0 maps to r1, it means r0 outlives r1. *)
  let graph = ref RegionMap.empty in

  (* r0 outlives r1 *)
  let add_outlive (r0 : region) (r1 : region) =
    graph :=
      RegionMap.update r0
        (fun s ->
          let s = Option.get s in
          Some (RegionSet.add r1 s))
        !graph
  in

  let add_region (r : region) : unit =
    [%sanity_check_opt_span] span (not (RegionMap.mem r !graph));
    graph :=
      RegionMap.update r
        (fun s ->
          match s with
          | None -> Some RegionSet.empty
          | Some s -> Some s)
        !graph
  in

  (* [r] outlives the regions in [outlived] *)
  let add_outlives r (outlived : region list) =
    List.iter (fun r' -> add_outlive r r') outlived
  in

  (* Visit to compute the constraints *)
  let visitor =
    object (self)
      inherit [_] iter_ty as super

      (* Generate a fresh region, register it, and save the fact that it outlives
         all the regions inside which we had to dive so far *)
      method! visit_region outer r =
        (* Sanity check *)
        let add =
          match r with
          | RErased -> [%craise_opt_span] span "Expected a type with regions"
          | RVar (Free rid) -> RegionId.Set.mem rid regions
          | RVar (Bound _) -> [%craise_opt_span] span "Not handled yet"
          | RStatic -> false
        in
        if add then (
          add_region r;
          add_outlives r outer)

      method! visit_generic_args outer generics =
        (* TODO: we need to handle those *)
        [%sanity_check_opt_span] span (generics.trait_refs = []);
        super#visit_generic_args outer generics

      method! visit_ty outer ty =
        match ty with
        | TAdt adt -> begin
            (* TODO: we need to handle those *)
            [%sanity_check_opt_span] span (adt.generics.trait_refs = []);
            match adt.id with
            | TAdtId id ->
                (* Lookup the declaration and use the region constraints
                   to check which regions outlive the projected regions. *)
                let decl =
                  [%silent_unwrap_opt_span] span
                    (TypeDeclId.Map.find_opt id type_decls)
                in
                let { regions; types; const_generics; trait_refs } =
                  adt.generics
                in
                List.iter (self#visit_region outer) regions;
                List.iter (self#visit_ty outer) types;
                List.iter (self#visit_const_generic outer) const_generics;
                (* TODO: we need to handle those *)
                [%sanity_check_opt_span] span (trait_refs = []);

                (* Substitute in the constraints *)
                let subst =
                  Charon.Substitute.make_subst_from_generics decl.generics
                    adt.generics
                in
                let params =
                  Charon.Substitute.predicates_substitute subst decl.generics
                in

                (* Update the graph following the outlive *)
                let {
                  regions = _;
                  types = _;
                  const_generics = _;
                  trait_clauses = _;
                  regions_outlive;
                  types_outlive;
                  trait_type_constraints = _;
                } =
                  params
                in

                (* [r0] outlives [r1] *)
                let visit_region_register_outlive r0 r1 =
                  match r1 with
                  | RVar (Bound _) ->
                      [%craise_opt_span] span
                        "Bound regions are not handled yet"
                  | RVar (Free _) -> add_outlives r0 [ r1 ]
                  | RStatic | RErased -> [%internal_error_opt_span] span
                in

                let outlive_visitor =
                  object
                    inherit [_] iter_ty

                    (* [r1] outlives [r0] *)
                    method! visit_region r0 r1 =
                      visit_region_register_outlive r1 r0
                  end
                in

                (* Visit the region outlives constraints (the first region outlives the second)  *)
                List.iter
                  (fun (pred : (region, region) outlives_pred region_binder) ->
                    [%cassert_opt_span] span (pred.binder_regions = [])
                      "Bound regions are not supported yet";
                    let r0, r1 = pred.binder_value in
                    visit_region_register_outlive r0 r1)
                  regions_outlive;

                (* Visit the type outlives constraints (the type outlives the region) *)
                List.iter
                  (fun (pred : (ty, region) outlives_pred region_binder) ->
                    [%cassert_opt_span] span (pred.binder_regions = [])
                      "Bound regions are not supported yet";
                    let ty, r = pred.binder_value in
                    outlive_visitor#visit_ty r ty)
                  types_outlive
            | TTuple -> super#visit_ty outer ty
            | TBuiltin builtin_ty -> (
                match builtin_ty with
                | TBox | TArray | TSlice | TStr -> super#visit_ty outer ty)
          end
        | TVar _ | TLiteral _ | TNever -> ()
        | TRef (r, ref_ty, _) ->
            self#visit_region outer r;
            let outer = r :: outer in
            self#visit_ty outer ref_ty
        | TTraitType (tref, _) ->
            (* TODO: normalize the trait types.
               For now we only emit a warning because it makes some tests fail. *)
            [%cassert_warn_opt_span] span
              (not (trait_instance_id_reducible span tref.kind))
              "Found an unexpected trait impl associated type which was not \
               inlined while analyzing a type. This is a case we currently do \
               not handle in all generality. As a result,the consumed/given \
               back values computed for the generated backward functions may \
               be incorrect.";
            ()
        | TRawPtr _
        | TDynTrait _
        | TFnPtr _
        | TFnDef _
        | TPtrMetadata _
        | TError _ ->
            (* Don't know what to do *)
            [%craise_opt_span] span "Not handled yet"
    end
  in
  visitor#visit_ty [] ty;

  (* Compute the strongly connected components, and for each of them,
     determine whether the component:
     - contains a masked region
     - contains a static region

     Then, we map the different regions to a masked region or an erased region
     depending on whether they outlive an SCC containing a masked region, etc.
  *)
  let module Scc = SCC.Make (RegionOrderedType) in
  let sccs = Scc.compute (RegionMap.bindings !graph) in

  (* Compute, for each SCC whether it contains a marked region or a static region *)
  let scc_kind =
    SccId.Map.map
      (fun ls ->
        let has_marked = ref false in
        let has_static = ref false in
        List.iter
          (fun r ->
            match r with
            | RVar (Free _) -> has_marked := true
            | RStatic -> has_static := true
            | _ -> ())
          ls;
        let has_marked = !has_marked in
        let has_static = !has_static in
        [%sanity_check_opt_span] span ((not has_marked) || not has_static);
        if has_marked then RkMarked
        else if has_static then RkStatic
        else RkDefault)
      sccs.sccs
  in

  (* Compute, for each SCC, whether it outlives an SCC containing a projected or static region *)
  let scc_kind_full = ref SccId.Map.empty in
  let rec compute_kind (id : SccId.id) : region_kind =
    let deps_kinds =
      List.map compute_kind
        (SccId.Set.elements (SccId.Map.find id sccs.scc_deps))
    in
    let kind = SccId.Map.find id scc_kind in
    let has_marked = ref false in
    let has_static = ref false in
    let outlives_marked = ref false in
    List.iter
      (fun k ->
        match k with
        | RkMarked | RkOutlives -> outlives_marked := true
        | RkStatic -> has_static := true
        | RkDefault -> ())
      deps_kinds;
    begin
      match kind with
      | RkMarked -> has_marked := true
      | RkOutlives -> [%internal_error_opt_span] span
      | RkStatic -> has_static := true
      | RkDefault -> ()
    end;

    let has_marked = !has_marked in
    let has_static = !has_static in
    let outlives_marked = !outlives_marked in
    [%sanity_check_opt_span] span ((not has_marked) || not has_static);
    let kind =
      if has_marked then RkMarked
      else if outlives_marked then RkOutlives
      else if has_static then RkStatic
      else RkDefault
    in
    scc_kind_full := SccId.Map.add id kind !scc_kind_full;
    kind
  in
  SccId.Map.iter
    (fun id _ ->
      let _ = compute_kind id in
      ())
    scc_kind;
  let scc_kind_full = !scc_kind_full in

  (* Compute the outlive regions *)
  let outlive_regions = ref RegionSet.empty in
  SccId.Map.iter
    (fun id regions ->
      let kind = SccId.Map.find id scc_kind_full in
      match kind with
      | RkOutlives ->
          outlive_regions :=
            RegionSet.union !outlive_regions (RegionSet.of_list regions)
      | RkStatic -> [%craise_opt_span] span "Not handled yet"
      | RkMarked | RkDefault -> ())
    sccs.sccs;
  let outlive_regions =
    RegionId.Set.of_list
      (List.map
         (fun r ->
           match r with
           | RVar (Free rid) -> rid
           | _ -> [%internal_error_opt_span] span)
         (RegionSet.elements !outlive_regions))
  in

  [%sanity_check_opt_span] span
    (RegionId.Set.inter outlive_regions regions = RegionId.Set.empty);

  outlive_regions
