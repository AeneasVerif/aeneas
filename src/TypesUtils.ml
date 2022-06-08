open Types
open Utils
module TA = TypesAnalysis

let type_decl_is_opaque (d : type_decl) : bool =
  match d.kind with Struct _ | Enum _ -> false | Opaque -> true

(** Retrieve the list of fields for the given variant of a [type_decl].

    Raises [Invalid_argument] if the arguments are incorrect.
 *)
let type_decl_get_fields (def : type_decl)
    (opt_variant_id : VariantId.id option) : field list =
  match (def.kind, opt_variant_id) with
  | Enum variants, Some variant_id -> (VariantId.nth variants variant_id).fields
  | Struct fields, None -> fields
  | _ ->
      let opt_variant_id =
        match opt_variant_id with None -> "None" | Some _ -> "Some"
      in
      raise
        (Invalid_argument
           ("The variant id should be [Some] if and only if the definition is \
             an enumeration:\n\
             - def: " ^ show_type_decl def ^ "\n- opt_variant_id: "
          ^ opt_variant_id))

(** Return [true] if a [ty] is actually `unit` *)
let ty_is_unit (ty : 'r ty) : bool =
  match ty with Adt (Tuple, [], []) -> true | _ -> false

let ty_is_adt (ty : 'r ty) : bool =
  match ty with Adt (_, _, _) -> true | _ -> false

let ty_as_adt (ty : 'r ty) : type_id * 'r list * 'r ty list =
  match ty with
  | Adt (id, regions, tys) -> (id, regions, tys)
  | _ -> failwith "Unreachable"

let ty_is_custom_adt (ty : 'r ty) : bool =
  match ty with Adt (AdtId _, _, _) -> true | _ -> false

let ty_as_custom_adt (ty : 'r ty) : TypeDeclId.id * 'r list * 'r ty list =
  match ty with
  | Adt (AdtId id, regions, tys) -> (id, regions, tys)
  | _ -> failwith "Unreachable"

(** The unit type *)
let mk_unit_ty : 'r ty = Adt (Tuple, [], [])

(** The usize type *)
let mk_usize_ty : 'r ty = Integer Usize

(** Deconstruct a type of the form `Box<T>` to retrieve the `T` inside *)
let ty_get_box (box_ty : ety) : ety =
  match box_ty with
  | Adt (Assumed Box, [], [ boxed_ty ]) -> boxed_ty
  | _ -> failwith "Not a boxed type"

(** Deconstruct a type of the form `&T` or `&mut T` to retrieve the `T` (and
    the borrow kind, etc.)
 *)
let ty_get_ref (ty : 'r ty) : 'r * 'r ty * ref_kind =
  match ty with
  | Ref (r, ty, ref_kind) -> (r, ty, ref_kind)
  | _ -> failwith "Not a ref type"

let mk_ref_ty (r : 'r) (ty : 'r ty) (ref_kind : ref_kind) : 'r ty =
  Ref (r, ty, ref_kind)

(** Make a box type *)
let mk_box_ty (ty : 'r ty) : 'r ty = Adt (Assumed Box, [], [ ty ])

(** Make a vec type *)
let mk_vec_ty (ty : 'r ty) : 'r ty = Adt (Assumed Vec, [], [ ty ])

(** Check if a region is in a set of regions *)
let region_in_set (r : RegionId.id region) (rset : RegionId.Set.t) : bool =
  match r with Static -> false | Var id -> RegionId.Set.mem id rset

(** Return the set of regions in an rty *)
let rty_regions (ty : rty) : RegionId.Set.t =
  let s = ref RegionId.Set.empty in
  let add_region (r : RegionId.id region) =
    match r with Static -> () | Var rid -> s := RegionId.Set.add rid !s
  in
  let obj =
    object
      inherit [_] iter_ty

      method! visit_'r _env r = add_region r
    end
  in
  (* Explore the type *)
  obj#visit_ty () ty;
  (* Return the set of accumulated regions *)
  !s

let rty_regions_intersect (ty : rty) (regions : RegionId.Set.t) : bool =
  let ty_regions = rty_regions ty in
  not (RegionId.Set.disjoint ty_regions regions)

(** Convert an [ety], containing no region variables, to an [rty] or [sty].

    In practice, it is the identity.
 *)
let rec ety_no_regions_to_gr_ty (ty : ety) : 'a gr_ty =
  match ty with
  | Adt (type_id, regions, tys) ->
      assert (regions = []);
      Adt (type_id, [], List.map ety_no_regions_to_gr_ty tys)
  | TypeVar v -> TypeVar v
  | Bool -> Bool
  | Char -> Char
  | Never -> Never
  | Integer int_ty -> Integer int_ty
  | Str -> Str
  | Array ty -> Array (ety_no_regions_to_gr_ty ty)
  | Slice ty -> Slice (ety_no_regions_to_gr_ty ty)
  | Ref (_, _, _) ->
      failwith
        "Can't convert a ref with erased regions to a ref with non-erased \
         regions"

let ety_no_regions_to_rty (ty : ety) : rty = ety_no_regions_to_gr_ty ty
let ety_no_regions_to_sty (ty : ety) : sty = ety_no_regions_to_gr_ty ty

(** Retuns true if the type contains borrows.

    Note that we can't simply explore the type and look for regions: sometimes
    we erase the lists of regions (by replacing them with `[]` when using `ety`,
    and when a type uses 'static this region doesn't appear in the region parameters.
 *)
let ty_has_borrows (infos : TA.type_infos) (ty : 'r ty) : bool =
  let info = TA.analyze_ty infos ty in
  info.TA.contains_borrow

(** Retuns true if the type contains nested borrows.

    Note that we can't simply explore the type and look for regions: sometimes
    we erase the lists of regions (by replacing them with `[]` when using `ety`,
    and when a type uses 'static this region doesn't appear in the region parameters.
 *)
let ty_has_nested_borrows (infos : TA.type_infos) (ty : 'r ty) : bool =
  let info = TA.analyze_ty infos ty in
  info.TA.contains_nested_borrows

(** Retuns true if the type contains a borrow under a mutable borrow *)
let ty_has_borrow_under_mut (infos : TA.type_infos) (ty : 'r ty) : bool =
  let info = TA.analyze_ty infos ty in
  info.TA.contains_borrow_under_mut

(** Check if a [ty] contains regions from a given set *)
let ty_has_regions_in_set (rset : RegionId.Set.t) (ty : rty) : bool =
  let obj =
    object
      inherit [_] iter_ty as super

      method! visit_Adt env type_id regions tys =
        List.iter (fun r -> if region_in_set r rset then raise Found) regions;
        super#visit_Adt env type_id regions tys

      method! visit_Ref env r ty rkind =
        if region_in_set r rset then raise Found
        else super#visit_Ref env r ty rkind
    end
  in
  try
    obj#visit_ty () ty;
    false
  with Found -> true

(** Return true if a type is "primitively copyable".
  *
  * "primitively copyable" means that copying instances of this type doesn't
  * require calling dedicated functions defined through the Copy trait. It
  * is the case for types like integers, shared borrows, etc.
  *
  * Generally, ADTs are not copyable. However, some of the primitive ADTs are
  * like `Option`.
  *)
let rec ty_is_primitively_copyable (ty : 'r ty) : bool =
  match ty with
  | Adt (Assumed Option, _, tys) -> List.for_all ty_is_primitively_copyable tys
  | Adt ((AdtId _ | Assumed (Box | Vec)), _, _) -> false
  | Adt (Tuple, _, tys) -> List.for_all ty_is_primitively_copyable tys
  | TypeVar _ | Never | Str | Array _ | Slice _ -> false
  | Bool | Char | Integer _ -> true
  | Ref (_, _, Mut) -> false
  | Ref (_, _, Shared) -> true
