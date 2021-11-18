open Identifiers
open Types

module VarId = IdGen ()

module BorrowId = IdGen ()

type var = {
  index : VarId.id;  (** Unique variable identifier *)
  name : string option;
  ty : ety;
      (** The variable type - erased type, because variables are not used
       ** in function signatures *)
}

(** A variable *)

type big_int = Z.t

let big_int_of_yojson (json : Yojson.Safe.t) : (big_int, string) result =
  match json with
  | `Int i -> Ok (Z.of_int i)
  | `Intlit is -> Ok (Z.of_string is)
  | _ -> Error "not an integer or an integer literal"

let big_int_to_yojson (i : big_int) = `Intlit (Z.to_string i)

(** A scalar value

    Note that we use unbounded integers everywhere.
    We then harcode the boundaries for the different types.
 *)
type scalar_value =
  | Isize of big_int
  | I8 of big_int
  | I16 of big_int
  | I32 of big_int
  | I64 of big_int
  | I128 of big_int
  | Usize of big_int
  | U8 of big_int
  | U16 of big_int
  | U32 of big_int
  | U64 of big_int
  | U128 of big_int

(** A constant value *)
type constant_value =
  | Scalar of scalar_value
  | Bool of bool
  | Char of char
  | String of string

type symbolic_value = unit
(** Symbolic value - TODO *)

(** An untyped value, used in the environments *)
type value =
  | Adt of adt_value  (** Enumerations and structures *)
  | Symbolic of symbolic_value  (** Unknown value *)
  | Concrete of constant_value  (** Concrete (non-symbolic) value *)
  | Tuple of value FieldId.vector
      (** Tuple - note that units are encoded as 0-tuples *)
  | Borrow of borrow_content  (** A borrowed value *)
  | Loan of loan_content  (** A loaned value *)
  | Bottom  (** No value (uninitialized or moved value) *)
  | Assumed of assumed_value  (** Assumed types (Box, Vec, Cell...) *)

and adt_value = {
  def_id : TypeDefId.id;
  variant_id : VariantId.id option;
  regions : erased_region list;
  types : rty list;
  field_values : value FieldId.vector;
}

and borrow_content =
  | SharedBorrow of BorrowId.id  (** A shared value *)
  | MutBorrow of BorrowId.id * value  (** A mutably borrowed value *)
  | InactivatedMutBorrow of BorrowId.id
      (** An inactivated mut borrow.

          This is used to model two-phase borrows. When evaluating a two-phase
          mutable borrow, we first introduce an inactivated borrow which behaves
          like a shared borrow, until the moment we actually *use* the borrow:
          at this point, we end all the other shared borrows (or inactivated borrows
          - though there shouldn't be any other inactivated borrows if the program
          is well typed) of this value and replace the inactivated borrow with a
          mutable borrow.
       *)

and loan_content =
  | SharedLoan of BorrowId.Set.t * value
  | MutLoan of BorrowId.id

and assumed_value = Box of value
