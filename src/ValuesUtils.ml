open Utils
open TypesUtils
open Types
open Values

let mk_unit_value : typed_value =
  { value = Adt { variant_id = None; field_values = [] }; ty = mk_unit_ty }

let mk_typed_value (ty : ety) (value : value) : typed_value = { value; ty }

let mk_bottom (ty : ety) : typed_value = { value = Bottom; ty }

(** Box a value *)
let mk_box_value (v : typed_value) : typed_value =
  let box_ty = mk_box_ty v.ty in
  let box_v = Adt { variant_id = None; field_values = [ v ] } in
  mk_typed_value box_ty box_v

(** Check if a value contains a borrow *)
let borrows_in_value (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value

      method! visit_borrow_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains inactivated mutable borrows *)
let inactivated_in_value (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value

      method! visit_InactivatedMutBorrow _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains a loan *)
let loans_in_value (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value

      method! visit_loan_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true
