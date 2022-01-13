open Types
open Utils

(** Retrieve the list of fields for the given variant of a [type_def].

    Raises [Invalid_argument] if the arguments are incorrect.
 *)
let type_def_get_fields (def : type_def) (opt_variant_id : VariantId.id option)
    : field list =
  match (def.kind, opt_variant_id) with
  | Enum variants, Some variant_id -> (VariantId.nth variants variant_id).fields
  | Struct fields, None -> fields
  | _ ->
      raise
        (Invalid_argument
           "The variant id should be [Some] if and only if the definition is \
            an enumeration")

(** Return [true] if a [ty] is actually `unit` *)
let ty_is_unit (ty : 'r ty) : bool =
  match ty with Adt (Tuple, [], []) -> true | _ -> false

(** The unit type *)
let mk_unit_ty : ety = Adt (Tuple, [], [])

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

(** Check if a region is in a set of regions *)
let region_in_set (r : RegionId.id region) (rset : RegionId.set_t) : bool =
  match r with Static -> false | Var id -> RegionId.Set.mem id rset

(** Return the set of regions in an rty *)
let rty_regions (ty : rty) : RegionId.set_t =
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

let rty_regions_intersect (ty : rty) (regions : RegionId.set_t) : bool =
  let ty_regions = rty_regions ty in
  not (RegionId.Set.disjoint ty_regions regions)

(** Convert an [ety], containing no region variables, to an [rty].

    In practice, it is the identity.
 *)
let rec ety_no_regions_to_rty (ty : ety) : rty =
  match ty with
  | Adt (type_id, regions, tys) ->
      assert (regions = []);
      Adt (type_id, [], List.map ety_no_regions_to_rty tys)
  | TypeVar v -> TypeVar v
  | Bool -> Bool
  | Char -> Char
  | Never -> Never
  | Integer int_ty -> Integer int_ty
  | Str -> Str
  | Array ty -> Array (ety_no_regions_to_rty ty)
  | Slice ty -> Slice (ety_no_regions_to_rty ty)
  | Ref (_, _, _) ->
      failwith
        "Can't convert a ref with erased regions to a ref with non-erased \
         regions"

(** Check if a [ty] contains regions *)
let ty_has_regions (ty : ety) : bool =
  let obj =
    object
      inherit [_] iter_ty as super

      method! visit_Adt env type_id regions tys =
        if regions = [] then super#visit_Adt env type_id regions tys
        else raise Found

      method! visit_Ref _ _ _ _ = raise Found
    end
  in
  try
    obj#visit_ty () ty;
    false
  with Found -> true

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
  *)
let rec type_is_primitively_copyable (ty : ety) : bool =
  match ty with
  | Adt ((AdtId _ | Assumed _), _, _) -> false
  | Adt (Tuple, _, tys) -> List.for_all type_is_primitively_copyable tys
  | TypeVar _ | Never | Str | Array _ | Slice _ -> false
  | Bool | Char | Integer _ -> true
  | Ref (_, _, Mut) -> false
  | Ref (_, _, Shared) -> true
