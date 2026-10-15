open Types
open Utils
include Charon.TypesUtils

let constant_expr_as_literal (c : constant_expr) : Values.literal =
  match c.kind with
  | CBool v -> VBool v
  | CInteger v -> VScalar v
  | CChar v -> VChar v
  | CFloat v -> VFloat v
  | CStr v -> VStr v
  | CByteStr v -> VByteStr v
  | _ -> raise (Failure "Expected a primitive constant")

let constant_expr_as_integer (c : constant_expr) : integer_value =
  match c.kind with
  | CInteger v -> v
  | _ -> raise (Failure "Expected an integer constant")

(** Create a tuple type. *)
let mk_tuple_ty (tys : ty list) : ty =
  TAdt
    {
      id = unit_type_decl_id;
      generics = mk_generic_args_from_types tys;
      builtin = Some TTuple;
    }

let concat_generic_args (generics1 : generic_args) (generics2 : generic_args) :
    generic_args =
  {
    regions = generics1.regions @ generics2.regions;
    types = generics1.types @ generics2.types;
    const_generics = generics1.const_generics @ generics2.const_generics;
    trait_refs = generics1.trait_refs @ generics2.trait_refs;
  }

(** Check if a region belongs to a set of regions.

    This shadows {!Charon.TypesUtils.region_in_set}: we use sets of regions
    (which may contain the static region) rather than sets of region ids.

    This function should be used on non-bound regions; it raises an exception if
    this is not the case, or if the region is erased and [allow_erased] is
    [false]. *)
let region_in_set ?(allow_erased = false) (r : region) (rset : region_set) :
    bool =
  match r with
  | RStatic | RVar (Free _) -> RegionSet.mem r rset
  | RErased ->
      if allow_erased then false
      else
        [%craise_opt_span] None
          "region_in_set shouldn't be called on erased regions"
  | RBody _ ->
      [%craise_opt_span] None
        "region_in_set shouldn't be called on body regions"
  | RVar (Bound _) ->
      [%craise_opt_span] None
        "region_in_set shouldn't be called on bound regions"

(** Convert a set of region ids to a set of (free) regions *)
let region_set_of_region_id_set (rids : RegionId.Set.t) : region_set =
  RegionSet.of_list
    (List.map (fun rid -> RVar (Free rid)) (RegionId.Set.elements rids))

(** Return the set of region ids appearing in a set of regions (we ignore the
    static region) *)
let region_set_get_region_ids (rset : region_set) : RegionId.Set.t =
  RegionId.Set.of_list
    (List.filter_map
       (fun r ->
         match r with
         | RVar (Free rid) -> Some rid
         | _ -> None)
       (RegionSet.elements rset))

(** Return [true] if a set of regions contains the static region *)
let region_set_has_static (rset : region_set) : bool =
  RegionSet.mem RStatic rset

(** Return the set of region variables in an type.

    We ignore the static region: this function is used to check whether a type
    contains ended regions, and the static region never ends (several region
    abstractions may own it at the same time - see [Contexts.eval_ctx]).

    This function should be used on non-erased and non-bound regions. For
    sanity, we raise exceptions if this is not the case. *)
let ty_regions (ty : ty) : RegionId.Set.t =
  let s = ref RegionId.Set.empty in
  let add_region (r : region) =
    match r with
    | RStatic -> ()
    | RErased | RBody _ ->
        raise
          (Failure "ty_regions shouldn't be called on erased or body regions")
    | RVar (Bound _) ->
        raise (Failure "region_in_set shouldn't be called on bound regions")
    | RVar (Free id) -> s := RegionId.Set.add id !s
  in
  let obj =
    object
      inherit [_] iter_ty as super
      method! visit_region _env r = add_region r

      method! visit_TDynTrait env tr =
        (* Ignore the dyn traits by default *)
        if Config.type_analysis_ignore_dyn then ()
        else super#visit_TDynTrait env tr
    end
  in
  (* Explore the type *)
  obj#visit_ty () ty;
  (* Return the set of accumulated regions *)
  !s

(* TODO: merge with ty_has_regions_in_set *)
let ty_regions_intersect (ty : ty) (regions : RegionId.Set.t) : bool =
  let ty_regions = ty_regions ty in
  not (RegionId.Set.disjoint ty_regions regions)

(** Lookup the information about an ADT ([None] if it is a builtin type) *)
let lookup_adt_info (infos : TypesAnalysis.type_infos) (tref : type_decl_ref) :
    TypesAnalysis.type_decl_info option =
  match tref.builtin with
  | Some (TTuple | TBox | TStr) -> None
  | None ->
      Some
        ([%unwrap_opt_span] None
           (TypeDeclId.Map.find_opt tref.id infos)
           "Missing type information")

(** Check whether the definition of an ADT contains static borrows.

    Note that in this case the static region doesn't appear in the generics of
    the ADT: the static region is "hidden" (for instance, consider:
    [struct S { x : &'static u32 }]). As a consequence, functions which check
    whether a type contains some regions by simply exploring it must take this
    information into account. *)
let adt_has_hidden_static (infos : TypesAnalysis.type_infos)
    (tref : type_decl_ref) : bool =
  match lookup_adt_info infos tref with
  | None -> false
  | Some info -> info.borrows_info.contains_static

(** Check whether a type contains an ADT in which the static region is hidden
    (see {!adt_has_hidden_static}). *)
let ty_has_hidden_static (infos : TypesAnalysis.type_infos) (ty : ty) : bool =
  let obj =
    object
      inherit [_] iter_ty as super

      method! visit_TAdt env tref =
        if adt_has_hidden_static infos tref then raise Found;
        super#visit_TAdt env tref
    end
  in
  try
    obj#visit_ty () ty;
    false
  with Found -> true

(** Check if a {!type:Charon.Types.ty} contains regions which satisfy a
    predicate.

    If [infos] is provided, we take into account the static regions which are
    hidden in ADTs (see {!adt_has_hidden_static}). *)
let ty_has_regions_in_pred_aux (infos : TypesAnalysis.type_infos option)
    (pred : region -> bool) (ty : ty) : bool =
  let obj =
    object
      inherit [_] iter_ty as super
      method! visit_region _ r = if pred r then raise Found

      method! visit_TAdt env tref =
        (match infos with
        | Some infos ->
            if adt_has_hidden_static infos tref && pred RStatic then raise Found
        | None -> ());
        super#visit_TAdt env tref

      method! visit_TDynTrait env tr =
        (* Ignore the dyn traits by default *)
        if Config.type_analysis_ignore_dyn then ()
        else super#visit_TDynTrait env tr
    end
  in
  try
    obj#visit_ty () ty;
    false
  with Found -> true

(** Check if a {!type:Charon.Types.ty} contains regions which satisfy a
    predicate (we take into account the static regions hidden in ADTs, see
    {!adt_has_hidden_static}). *)
let ty_has_regions_in_pred (infos : TypesAnalysis.type_infos)
    (pred : region -> bool) (ty : ty) : bool =
  ty_has_regions_in_pred_aux (Some infos) pred ty

(** Check if a {!type:Charon.Types.ty} contains regions from a given set (we
    take into account the static regions hidden in ADTs, see
    {!adt_has_hidden_static}). *)
let ty_has_regions_in_set (infos : TypesAnalysis.type_infos) (rset : region_set)
    (ty : ty) : bool =
  ty_has_regions_in_pred infos (fun r -> region_in_set r rset) ty

(** Check if a type has free (i.e., non erased) regions.

    This is useful in particular when using normalized projection types (types
    where all the regions of interest are free regions, and the other regions
    are erased, that we use for instance to project the borrows belonging to a
    symbolic value into different region abstractions): the projection over a
    symbolic value intersects a region abstraction if its projection type has
    some free regions (or in other words, if not all the regions appearing in
    the type are erased). *)
let ty_has_free_regions (ty : ty) : bool =
  ty_has_regions_in_pred_aux None region_is_free ty

let ty_has_erased_regions (ty : ty) : bool =
  ty_has_regions_in_pred_aux None region_is_erased ty

let expect_free_var = Substitute.expect_free_var

(** Retuns true if the type contains borrows.

    Note that we can't simply explore the type and look for regions: sometimes
    we erase the lists of regions (by replacing them with [[]] when using
    {!type:Types.ty}, and when a type uses 'static this region doesn't appear in
    the region parameters. *)
let ty_has_borrows (span : Meta.span option) (infos : TypesAnalysis.type_infos)
    (ty : ty) : bool =
  let info = TypesAnalysis.analyze_ty span infos ty in
  info.TypesAnalysis.contains_borrow

(** Checks that a type is copyable. * * This used to recursively traverse the
    type to ensure all its fields were * `Copy`. Instead we trust rustc's
    typechecking like we do for other marker * traits. *)
let ty_is_copyable (_ty : ty) : bool = true

let ty_has_adt_with_borrows span (infos : TypesAnalysis.type_infos) (ty : ty) :
    bool =
  let visitor =
    object
      inherit [_] iter_ty as super

      method! visit_ty env ty =
        match ty with
        | TAdt { builtin; _ } when builtin <> Some TTuple ->
            let info = TypesAnalysis.analyze_ty span infos ty in
            if info.TypesAnalysis.contains_borrow then raise Found
            else super#visit_ty env ty
        | _ -> super#visit_ty env ty
    end
  in
  try
    visitor#visit_ty () ty;
    false
  with Found -> true

(** Retuns true if the type contains nested borrows.

    Note that we can't simply explore the type and look for regions: sometimes
    we erase the lists of regions (by replacing them with [[]] when using
    {!type:Types.ty}), and when a type uses 'static this region doesn't appear
    in the region parameters. *)
let ty_has_nested_borrows (span : Meta.span option)
    (infos : TypesAnalysis.type_infos) (ty : ty) : bool =
  let info = TypesAnalysis.analyze_ty span infos ty in
  info.TypesAnalysis.contains_nested_borrows

let ty_has_nested_mut_borrows (span : Meta.span option)
    (infos : TypesAnalysis.type_infos) (ty : ty) : bool =
  let info = TypesAnalysis.analyze_ty span infos ty in
  info.TypesAnalysis.contains_nested_mut

(** Check whether a type is supported.

    TODO: implement the check. *)
let ty_is_supported (_span : Meta.span option)
    (_infos : TypesAnalysis.type_infos) (_ty : ty) : bool =
  true

(* Refresh the regions appearing inside a type, and introduce
   fresh regions for its erased regions.

   If [live_regions] is provided we only refresh the live regions (i.e., the
   regions appearing in the set).
*)
let ty_refresh_regions (span : Meta.span option)
    ?(region_is_live : (region_id -> bool) option = None)
    (fresh_region : unit -> region_id) (ty : ty) : region_id list * ty =
  let fresh_regions = ref [] in
  let fresh_region () =
    let rid = fresh_region () in
    fresh_regions := rid :: !fresh_regions;
    rid
  in
  let region_is_live =
    match region_is_live with
    | None -> fun _ -> true
    | Some region_is_live -> region_is_live
  in
  let regions_map = ref RegionId.Map.empty in
  let get_region rid =
    if region_is_live rid then (
      match RegionId.Map.find_opt rid !regions_map with
      | Some id -> id
      | None ->
          let nid = fresh_region () in
          regions_map := RegionId.Map.add rid nid !regions_map;
          nid)
    else rid
  in
  let visitor =
    object
      inherit [_] map_ty

      method! visit_region_id _ _ =
        (* We shouldn't get there and should rather catch all the call sites *)
        [%internal_error_opt_span] span

      (* The region ids in [binder_regions] (e.g. higher-ranked trait bounds or
         arrow types) are *binding* occurrences, not uses: leave them untouched.
         Their uses are [RVar (Bound _)], handled by [visit_RVar] below. *)
      method! visit_region_param _ rp = rp

      method! visit_RVar _ var =
        match var with
        | Free rid -> RVar (Free (get_region rid))
        | Bound _ -> RVar var

      method! visit_RErased _ = RVar (Free (fresh_region ()))
    end
  in
  let ty = visitor#visit_ty () ty in
  (List.rev !fresh_regions, ty)

let ety_has_nested_borrows (span : Meta.span option)
    (infos : TypesAnalysis.type_infos) (ty : ty) : bool =
  (* FIXME: The analysis currently only works on types with regions - erased types are
     not allowed. For now, we update the type to insert fresh regions.
     In order to avoid collisions (which as of today wouldn't be a problem actually,
     but it's cleaner if we avoid the problem), we also refresh the existing non-erased
     regions.
  *)
  let _, fresh_region = RegionId.fresh_stateful_generator () in
  let _, ty = ty_refresh_regions span fresh_region ty in
  let info = TypesAnalysis.analyze_ty span infos ty in
  info.TypesAnalysis.contains_nested_borrows

(** Retuns true if the type decl contains nested borrows. *)
let type_decl_has_nested_borrows (span : Meta.span option)
    (infos : TypesAnalysis.type_infos) (type_decl : type_decl) : bool =
  let generics =
    Substitute.generic_args_of_params_erase_regions span type_decl.generics
  in
  let ty = TAdt { id = type_decl.def_id; generics; builtin = None } in
  ty_has_nested_borrows span infos ty

let type_decl_has_nested_mut_borrows (span : Meta.span option)
    (infos : TypesAnalysis.type_infos) (type_decl : type_decl) : bool =
  let generics =
    Substitute.generic_args_of_params_erase_regions span type_decl.generics
  in
  let ty = TAdt { id = type_decl.def_id; generics; builtin = None } in
  ty_has_nested_mut_borrows span infos ty

(** Retuns true if the type contains a borrow under a mutable borrow *)
let ty_has_borrow_under_mut span (infos : TypesAnalysis.type_infos) (ty : ty) :
    bool =
  let info = TypesAnalysis.analyze_ty span infos ty in
  info.TypesAnalysis.contains_borrow_under_mut

(** Check if a {!type:Charon.Types.ty} contains a mutable borrow which uses a
    region from a given set.

    We take into account the static mutable borrows hidden in ADTs (see
    {!adt_has_hidden_static}). *)
let ty_has_mut_borrow_for_region_in_pred (infos : TypesAnalysis.type_infos)
    (pred : region -> bool) (ty : ty) : bool =
  let obj =
    object
      inherit [_] iter_ty as super

      method! visit_TRef env r ty rkind =
        begin
          match rkind with
          | RMut -> if pred r then raise Found
          | RShared -> ()
        end;
        super#visit_TRef env r ty rkind

      method! visit_TAdt env tref =
        (* Lookup the information for this ADT *)
        begin
          match tref.builtin with
          | Some (TTuple | TBox | TStr) -> ()
          | None ->
              let info = TypeDeclId.Map.find tref.id infos in
              if info.borrows_info.contains_static_mut && pred RStatic then
                raise Found;
              RegionId.iteri
                (fun adt_rid r ->
                  if RegionId.Set.mem adt_rid info.mut_regions && pred r then
                    raise Found
                  else ())
                tref.generics.regions
        end;
        super#visit_TAdt env tref
    end
  in
  try
    obj#visit_ty () ty;
    false
  with Found -> true

(** Compute which regions from a set are effectively used as mutable borrows in
    a type. Note that a mutable borrow below a shared borrow is effectively
    shared.

    We take into account the static mutable borrows hidden in ADTs (see
    {!adt_has_hidden_static}). *)
let ty_get_mutable_regions (infos : TypesAnalysis.type_infos)
    (owned_regions : region_set) (ty : rty) : region_set =
  let result = ref RegionSet.empty in
  let add_region (r : region) =
    match r with
    | RVar (Free _) | RStatic ->
        if RegionSet.mem r owned_regions then result := RegionSet.add r !result
    | _ -> ()
  in

  let obj =
    object
      inherit [_] iter_ty as super

      method! visit_TRef env r ty rkind =
        match rkind with
        | RMut ->
            add_region r;
            super#visit_TRef env r ty rkind
        | RShared ->
            (* Stop there: borrows below shared borrows are effectively shared *)
            ()

      method! visit_TAdt env tref =
        (* Lookup the information for this ADT *)
        begin
          match tref.builtin with
          | Some (TTuple | TBox | TStr) -> ()
          | None ->
              (* Check which region parameters are mutable *)
              let info = TypeDeclId.Map.find tref.id infos in
              if info.borrows_info.contains_static_mut then add_region RStatic;
              RegionId.iteri
                (fun adt_rid r ->
                  if RegionId.Set.mem adt_rid info.mut_regions then add_region r)
                tref.generics.regions
        end;
        super#visit_TAdt env tref
    end
  in
  obj#visit_ty () ty;
  !result

let ty_has_mut_borrow_for_region_in_set (infos : TypesAnalysis.type_infos)
    (regions : region_set) (ty : ty) : bool =
  ty_has_mut_borrow_for_region_in_pred infos
    (function
      | (RVar (Free _) | RStatic) as r -> RegionSet.mem r regions
      | _ -> false)
    ty

let ty_has_mut_borrows (infos : TypesAnalysis.type_infos) (ty : ty) : bool =
  ty_has_mut_borrow_for_region_in_pred infos (fun _ -> true) ty

(** Small helper *)
let raise_if_not_rty_visitor =
  object
    inherit [_] iter_ty as super

    method! visit_region _ r =
      match r with
      | RVar (Bound _) | RErased -> raise Found
      | RStatic | RVar (Free _) -> ()
      | RBody _ -> [%craise_opt_span] None "unsupported: Body region"

    method! visit_TDynTrait env tr =
      (* Ignore dyn traits by default *)
      if Config.type_analysis_ignore_dyn then ()
      else super#visit_TDynTrait env tr
  end

(** Return [true] if the type is a region type (i.e., it doesn't contain erased
    regions), and only contains free regions) *)
let ty_is_rty (ty : ty) : bool =
  try
    raise_if_not_rty_visitor#visit_ty () ty;
    true
  with Found -> false

(** Small helper *)
let raise_if_not_erased_ty_visitor =
  object
    inherit [_] iter_ty

    method! visit_region _ r =
      match r with
      | RStatic | RVar _ -> raise Found
      | RErased -> ()
      | RBody _ -> [%craise_opt_span] None "unsupported: Body region"
  end

(** Return [true] if the type is a region type (i.e., it doesn't contain erased
    regions) *)
let ty_is_ety (ty : ty) : bool =
  try
    raise_if_not_erased_ty_visitor#visit_ty () ty;
    true
  with Found -> false

let ty_erase_body_regions ty =
  let visitor =
    object
      inherit [_] map_ty

      method! visit_region _ r =
        match r with
        | RStatic | RVar _ | RErased -> r
        | RBody _ -> RErased
    end
  in
  visitor#visit_ty () ty

let ty_erase_regions ty =
  let visitor =
    object
      inherit [_] map_ty
      method! visit_region _ _ = RErased
    end
  in
  visitor#visit_ty () ty

let generic_args_only_erased_regions (x : generic_args) : bool =
  try
    raise_if_not_erased_ty_visitor#visit_generic_args () x;
    true
  with Found -> false

(** Small helper *)
let raise_if_region_ty_visitor =
  object
    inherit [_] iter_ty as super
    method! visit_region _ _ = raise Found

    method! visit_TDynTrait env tr =
      (* Ignore the dyn traits by default *)
      if Config.type_analysis_ignore_dyn then ()
      else super#visit_TDynTrait env tr
  end

(** Return [true] if the type doesn't contain regions (including erased regions)
*)
let ty_no_regions (ty : ty) : bool =
  try
    raise_if_region_ty_visitor#visit_ty () ty;
    true
  with Found -> false

(** Return [true] if the type doesn't contain regions (including erased regions)
*)
let ty_has_regions (ty : ty) : bool =
  try
    raise_if_region_ty_visitor#visit_ty () ty;
    false
  with Found -> true

(** Return [true] if the trait ref doesn't contain regions (including erased
    regions) *)
let trait_ref_no_regions (x : trait_ref) : bool =
  try
    raise_if_region_ty_visitor#visit_trait_ref () x;
    true
  with Found -> false

(** Return [true] if the trait instance id doesn't contain regions (including
    erased regions) *)
let trait_instance_id_no_regions (x : trait_ref_kind) : bool =
  try
    raise_if_region_ty_visitor#visit_trait_ref_kind () x;
    true
  with Found -> false

(** Return [true] if the generic args don't contain regions (including erased
    regions) *)
let generic_args_no_regions (x : generic_args) : bool =
  try
    raise_if_region_ty_visitor#visit_generic_args () x;
    true
  with Found -> false

(** Return [true] if the trait type constraint doesn't contain regions
    (including erased regions) *)
let trait_type_constraint_no_regions (x : trait_type_constraint) : bool =
  try
    let { trait_ref; type_id = _; ty } = x in
    raise_if_region_ty_visitor#visit_trait_ref () trait_ref;
    raise_if_region_ty_visitor#visit_ty () ty;
    true
  with Found -> false

(** Return true if a type declaration should be extracted as a tuple, because it
    is a non-recursive structure with unnamed fields. *)
let type_decl_from_decl_id_is_tuple_struct (ctx : TypesAnalysis.type_infos)
    (id : TypeDeclId.id) : bool =
  let info = TypeDeclId.Map.find id ctx in
  info.is_tuple_struct

(** A trait instance id refers to a local clause if it only uses the variants:
    [Self], [Clause], [ParentClause] *)
let rec trait_ref_kind_is_local_clause (id : trait_ref_kind) : bool =
  match id with
  | Self | Clause _ -> true
  | ParentClause (tref, _, _) | ItemClause (tref, _, _, _, _) ->
      trait_ref_kind_is_local_clause tref.kind
  | TraitImpl _ | BuiltinOrAuto _ | UnknownTrait _ | Dyn -> false

(** A trait instance id refers to a local clause if it only uses the variants:
    [Self], [Clause], [ParentClause] *)
let trait_ref_kind_is_local_clause_or_builtin (id : trait_ref_kind) : bool =
  trait_ref_kind_is_local_clause id
  ||
  match id with
  | BuiltinOrAuto _ -> true
  | _ -> false

(** Check that it is ok for a trait instance id not to be normalizable.

    We use this in sanity checks. If we can't normalize a trait instance id (and
    in particular one of its associated types) there are two possibilities:
    - either it is a local clause
    - or it is a builtin trait (in particular, [core::marker::DiscriminantKind]
      can never be reduced) *)
let check_non_normalizable_trait_ref_kind (trait_id : trait_ref_kind) : bool =
  trait_ref_kind_is_local_clause trait_id
  ||
  match trait_id with
  | BuiltinOrAuto _ -> true
  | _ -> false
