(** Use the [[%pure_type_check]] PPX instead, which expands to
    [pure_type_check __FILE__ __LINE] *)
let pure_type_check file line b span =
  Errors.cassert file line b span
    "Internal error: found a type-checking error in the generated model"
