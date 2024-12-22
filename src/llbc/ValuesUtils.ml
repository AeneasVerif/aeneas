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

let mk_bool_value (b : bool) : typed_value =
  { value = VLiteral (VBool b); ty = TLiteral TBool }

let mk_true : typed_value = mk_bool_value true
let mk_false : typed_value = mk_bool_value false

let mk_typed_value (span : Meta.span) (ty : ty) (value : value) : typed_value =
  sanity_check __FILE__ __LINE__ (ty_is_ety ty) span;
  { value; ty }

let mk_typed_avalue (span : Meta.span) (ty : ty) (value : avalue) : typed_avalue
    =
  sanity_check __FILE__ __LINE__ (ty_is_rty ty) span;
  { value; ty }

let mk_bottom (span : Meta.span) (ty : ty) : typed_value =
  sanity_check __FILE__ __LINE__ (ty_is_ety ty) span;
  { value = VBottom; ty }

let mk_abottom (span : Meta.span) (ty : ty) : typed_avalue =
  sanity_check __FILE__ __LINE__ (ty_is_rty ty) span;
  { value = ABottom; ty }

let mk_aignored (span : Meta.span) (ty : ty) (v : typed_value option) :
    typed_avalue =
  sanity_check __FILE__ __LINE__ (ty_is_rty ty) span;
  { value = AIgnored v; ty }

let value_as_symbolic (span : Meta.span) (v : value) : symbolic_value =
  match v with
  | VSymbolic v -> v
  | _ -> craise __FILE__ __LINE__ span "Unexpected"

(** Box a value *)
let mk_box_value (span : Meta.span) (v : typed_value) : typed_value =
  let box_ty = mk_box_ty v.ty in
  let box_v = VAdt { variant_id = None; field_values = [ v ] } in
  mk_typed_value span box_ty box_v

let is_bottom (v : value) : bool =
  match v with
  | VBottom -> true
  | _ -> false

let is_aignored (v : avalue) : bool =
  match v with
  | AIgnored _ -> true
  | _ -> false

let is_symbolic (v : value) : bool =
  match v with
  | VSymbolic _ -> true
  | _ -> false

let as_symbolic (span : Meta.span) (v : value) : symbolic_value =
  match v with
  | VSymbolic s -> s
  | _ -> craise __FILE__ __LINE__ span "Unexpected"

let as_mut_borrow (span : Meta.span) (v : typed_value) :
    BorrowId.id * typed_value =
  match v.value with
  | VBorrow (VMutBorrow (bid, bv)) -> (bid, bv)
  | _ -> craise __FILE__ __LINE__ span "Unexpected"

let is_unit (v : typed_value) : bool =
  ty_is_unit v.ty
  &&
  match v.value with
  | VAdt av -> av.variant_id = None && av.field_values = []
  | _ -> false

let mk_aproj_borrows (pm : proj_marker) (sv : symbolic_value) (proj_ty : ty) =
  { value = ASymbolic (pm, AProjBorrows (sv, proj_ty, [])); ty = proj_ty }

let mk_aproj_loans (pm : proj_marker) (sv : symbolic_value) (proj_ty : ty) =
  { value = ASymbolic (pm, AProjLoans (sv, proj_ty, [])); ty = proj_ty }

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

let symbolic_value_is_greedily_expandable (span : Meta.span option)
    (type_decls : type_decl TypeDeclId.Map.t)
    (type_infos : TypesAnalysis.type_infos) (sv : symbolic_value) : bool =
  if ty_has_borrows span type_infos sv.sv_ty then
    (* Ignore arrays and slices, as we can't expand them *)
    match sv.sv_ty with
    | TAdt (TBuiltin (TArray | TSlice), _) -> false
    | TAdt (TAdtId id, _) ->
        (* Lookup the type of the ADT to check if we can expand it *)
        let def = TypeDeclId.Map.find id type_decls in
        begin
          match def.kind with
          | Struct _ | Enum ([] | [ _ ]) ->
              (* Structure or enumeration with <= 1 variant *)
              true
          | Enum (_ :: _) | Alias _ | Opaque | TError _ | Union _ ->
              (* Enumeration with > 1 variants *)
              false
        end
    | _ -> true
  else false

let find_first_expandable_sv_with_borrows (span : Meta.span option)
    (type_decls : type_decl TypeDeclId.Map.t)
    (type_infos : TypesAnalysis.type_infos) (v : typed_value) :
    symbolic_value option =
  (* The visitor *)
  let obj =
    object
      inherit [_] iter_typed_value

      method! visit_VSymbolic _ sv =
        if symbolic_value_is_greedily_expandable span type_decls type_infos sv
        then raise (FoundSymbolicValue sv)
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
let symbolic_value_has_borrows span (infos : TypesAnalysis.type_infos)
    (sv : symbolic_value) : bool =
  ty_has_borrows span infos sv.sv_ty

(** Check if a value has borrows in **a general sense**.

    It checks if:
    - there are concrete borrows
    - there are symbolic values which may contain borrows
 *)
let value_has_borrows span (infos : TypesAnalysis.type_infos) (v : value) : bool
    =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_borrow_content _env _ = raise Found

      method! visit_symbolic_value _ sv =
        if symbolic_value_has_borrows span infos sv then raise Found else ()
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
let value_has_loans_or_borrows span (infos : TypesAnalysis.type_infos)
    (v : value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_borrow_content _env _ = raise Found
      method! visit_loan_content _env _ = raise Found

      method! visit_symbolic_value _ sv =
        if ty_has_borrow_under_mut span infos sv.sv_ty then raise Found else ()
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
