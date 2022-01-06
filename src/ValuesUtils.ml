open TypesUtils
open Types
open Values

let mk_unit_value : typed_value =
  { value = Adt { variant_id = None; field_values = [] }; ty = mk_unit_ty }

let mk_typed_value (ty : ety) (value : value) : typed_value = { value; ty }

(** Box a value *)
let mk_box_value (v : typed_value) : typed_value =
  let box_ty = mk_box_ty v.ty in
  let box_v = Adt { variant_id = None; field_values = [ v ] } in
  mk_typed_value box_ty box_v
