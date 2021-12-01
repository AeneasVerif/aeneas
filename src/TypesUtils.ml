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
  match ty with Tuple tys -> List.length tys = 0 | _ -> false

(** The unit type *)
let mk_unit_ty : ety = Tuple []
