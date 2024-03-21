open Utils
open TypesUtils
open Types
open Values
open Errors
include Charon.ValuesUtils

(** Utility exception *)
exception FoundSymbolicValue of symbolic_value

let mk_unit_value : typed_value =
  { value = VAdt { variant_id = None; field_values = [] }; ty = mk_unit_ty }

let mk_typed_value (meta : Meta.meta) (ty : ty) (value : value) : typed_value =
  cassert (ty_is_ety ty) meta "TODO: error message";
  { value; ty }

let mk_typed_avalue (meta : Meta.meta) (ty : ty) (value : avalue) : typed_avalue =
  cassert (ty_is_rty ty) meta "TODO: error message";
  { value; ty }

let mk_bottom (meta : Meta.meta) (ty : ty) : typed_value =
  cassert (ty_is_ety ty) meta "TODO: error message";
  { value = VBottom; ty }

let mk_abottom (meta : Meta.meta) (ty : ty) : typed_avalue =
  cassert (ty_is_rty ty) meta "TODO: error message";
  { value = ABottom; ty }

let mk_aignored (meta : Meta.meta) (ty : ty) : typed_avalue =
  cassert (ty_is_rty ty) meta "TODO: error message";
  { value = AIgnored; ty }

let value_as_symbolic (meta : Meta.meta) (v : value) : symbolic_value =
  match v with VSymbolic v -> v | _ -> craise meta "Unexpected"

(** Box a value *)
let mk_box_value (meta : Meta.meta) (v : typed_value) : typed_value =
  let box_ty = mk_box_ty v.ty in
  let box_v = VAdt { variant_id = None; field_values = [ v ] } in
  mk_typed_value meta box_ty box_v

let is_bottom (v : value) : bool = match v with VBottom -> true | _ -> false

let is_aignored (v : avalue) : bool =
  match v with AIgnored -> true | _ -> false

let is_symbolic (v : value) : bool =
  match v with VSymbolic _ -> true | _ -> false

let as_symbolic (meta : Meta.meta) (v : value) : symbolic_value =
  match v with VSymbolic s -> s | _ -> craise meta "Unexpected"

let as_mut_borrow (meta : Meta.meta) (v : typed_value) : BorrowId.id * typed_value =
  match v.value with
  | VBorrow (VMutBorrow (bid, bv)) -> (bid, bv)
  | _ -> craise meta "Unexpected"

let is_unit (v : typed_value) : bool =
  ty_is_unit v.ty
  &&
  match v.value with
  | VAdt av -> av.variant_id = None && av.field_values = []
  | _ -> false

(** Check if a value contains a *concrete* borrow (i.e., a [Borrow] value -
    we don't check if there are borrows hidden in symbolic values).
 *)
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

(** Check if a value contains reserved mutable borrows (which are necessarily
    *concrete*: a symbolic value can't "hide" reserved borrows).
 *)
let reserved_in_value (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_VReservedMutBorrow _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains a loan (which is necessarily *concrete*: symbolic
    values can't "hide" loans).
 *)
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

(** Check if a value contains concrete borrows or loans *)
let concrete_borrows_loans_in_value (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_borrow_content _env _ = raise Found
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

      method! visit_borrow_content _ _ =
        (* Do nothing so as *not to dive* in borrowed values *) ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

let find_first_primitively_copyable_sv_with_borrows
    (type_infos : TypesAnalysis.type_infos) (v : typed_value) :
    symbolic_value option =
  (* The visitor *)
  let obj =
    object
      inherit [_] iter_typed_value

      method! visit_VSymbolic _ sv =
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
  | VLoan (VSharedLoan (_, v')) -> value_strip_shared_loans v'
  | _ -> v

(** Check if a symbolic value has borrows *)
let symbolic_value_has_borrows (infos : TypesAnalysis.type_infos)
    (sv : symbolic_value) : bool =
  ty_has_borrows infos sv.sv_ty

(** Check if a value has borrows in **a general sense**.

    It checks if:
    - there are concrete borrows
    - there are symbolic values which may contain borrows
 *)
let value_has_borrows (infos : TypesAnalysis.type_infos) (v : value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_borrow_content _env _ = raise Found

      method! visit_symbolic_value _ sv =
        if symbolic_value_has_borrows infos sv then raise Found else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_value () v;
    false
  with Found -> true

(** Check if a value has loans.

    Note that loans are necessarily concrete (there can't be loans hidden
    inside symbolic values).
 *)
let value_has_loans (v : value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_loan_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_value () v;
    false
  with Found -> true

(** Check if a value has loans or borrows in **a general sense**.

    It checks if:
    - there are concrete loans or concrete borrows
    - there are symbolic values which may contain borrows (symbolic values
      can't contain loans).
 *)
let value_has_loans_or_borrows (infos : TypesAnalysis.type_infos) (v : value) :
    bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_borrow_content _env _ = raise Found
      method! visit_loan_content _env _ = raise Found

      method! visit_symbolic_value _ sv =
        if ty_has_borrow_under_mut infos sv.sv_ty then raise Found else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_value () v;
    false
  with Found -> true

(** Remove the shared loans in a value *)
let value_remove_shared_loans (v : typed_value) : typed_value =
  let visitor =
    object (self : 'self)
      inherit [_] map_typed_value as super

      method! visit_typed_value env v =
        match v.value with
        | VLoan (VSharedLoan (_, sv)) -> self#visit_typed_value env sv
        | _ -> super#visit_typed_value env v
    end
  in
  visitor#visit_typed_value () v
