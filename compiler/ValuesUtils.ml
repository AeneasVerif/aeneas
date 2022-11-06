open Utils
open TypesUtils
open Types
open Values
module TA = TypesAnalysis

(** Utility exception *)
exception FoundSymbolicValue of symbolic_value

let mk_unit_value : typed_value =
  { value = Adt { variant_id = None; field_values = [] }; ty = mk_unit_ty }

let mk_typed_value (ty : ety) (value : value) : typed_value = { value; ty }
let mk_bottom (ty : ety) : typed_value = { value = Bottom; ty }

(** Box a value *)
let mk_box_value (v : typed_value) : typed_value =
  let box_ty = mk_box_ty v.ty in
  let box_v = Adt { variant_id = None; field_values = [ v ] } in
  mk_typed_value box_ty box_v

let is_bottom (v : value) : bool = match v with Bottom -> true | _ -> false

let is_symbolic (v : value) : bool =
  match v with Symbolic _ -> true | _ -> false

let as_symbolic (v : value) : symbolic_value =
  match v with Symbolic s -> s | _ -> raise (Failure "Unexpected")

let as_mut_borrow (v : typed_value) : BorrowId.id * typed_value =
  match v.value with
  | Borrow (MutBorrow (bid, bv)) -> (bid, bv)
  | _ -> raise (Failure "Unexpected")

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

(** Check if a value contains outer loans (i.e., loans which are not in borrwed
    values. *)
let outer_loans_in_value (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_loan_content _env _ = raise Found
      method! visit_borrow_content _ _ = ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

let find_first_primitively_copyable_sv_with_borrows (type_infos : TA.type_infos)
    (v : typed_value) : symbolic_value option =
  (* The visitor *)
  let obj =
    object
      inherit [_] iter_typed_value

      method! visit_Symbolic _ sv =
        let ty = sv.sv_ty in
        if ty_is_primitively_copyable ty && ty_has_borrows type_infos ty then
          raise (FoundSymbolicValue sv)
        else ()
    end
  in
  (* Small helper *)
  try
    obj#visit_typed_value () v;
    None
  with FoundSymbolicValue sv -> Some sv

(** Strip the outer shared loans in a value.
    Ex.:
    [shared_loan {l0, l1} (3 : u32, shared_loan {l2} (4 : u32))] ~~>
    [(3 : u32, shared_loan {l2} (4 : u32))]
 *)
let rec value_strip_shared_loans (v : typed_value) : typed_value =
  match v.value with
  | Loan (SharedLoan (_, v')) -> value_strip_shared_loans v'
  | _ -> v
