module T = Types
open TypesUtils
open Values

let mk_unit_value : typed_value =
  { value = Adt { variant_id = None; field_values = [] }; ty = mk_unit_ty }

let mk_typed_value (ty : T.ety) (value : value) : typed_value = { value; ty }
