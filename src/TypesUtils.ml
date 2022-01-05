open Types

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
