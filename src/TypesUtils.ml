open Types

(** Convert an [rty] to an [ety] by erasing the region variables
    
    TODO: this can be done through a substitution
*)
let rec erase_regions (ty : rty) : ety =
  match ty with
  | Adt (def_id, regions, tys) ->
      let regions = List.map (fun _ -> Erased) regions in
      let tys = List.map erase_regions tys in
      Adt (def_id, regions, tys)
  | Tuple tys -> Tuple (List.map erase_regions tys)
  | TypeVar vid -> TypeVar vid
  | Bool -> Bool
  | Char -> Char
  | Never -> Never
  | Integer int_ty -> Integer int_ty
  | Str -> Str
  | Array ty -> Array (erase_regions ty)
  | Slice ty -> Slice (erase_regions ty)
  | Ref (_, ty, ref_kind) -> Ref (Erased, erase_regions ty, ref_kind)
  | Assumed (aty, regions, tys) ->
      let regions = List.map (fun _ -> Erased) regions in
      let tys = List.map erase_regions tys in
      Assumed (aty, regions, tys)

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
  match ty with Tuple tys -> List.length tys = 0 | _ -> false

(** The unit type *)
let mk_unit_ty : ety = Tuple []
