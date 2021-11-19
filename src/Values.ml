open Identifiers
open Types

module VarId = IdGen ()

module BorrowId = IdGen ()

module SymbolicValueId = IdGen ()

module AbstractionId = IdGen ()

module RegionId = IdGen ()

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

type symbolic_value = { sv_id : SymbolicValueId.id; sv_ty : rty }
(** Symbolic value *)

type symbolic_proj_comp = {
  svalue : symbolic_value;  (** The symbolic value itself *)
  rset_ended : RegionId.Set.t;
      (** The regions used in the symbolic value which have already ended *)
}
(** A complementary projector over a symbolic value.
    
    "Complementary" stands for the fact that it is a projector over all the
    regions *but* the ones which are listed in the projector.
 *)

(** An untyped value, used in the environments *)
type value =
  | Concrete of constant_value  (** Concrete (non-symbolic) value *)
  | Adt of adt_value  (** Enumerations and structures *)
  | Tuple of typed_value FieldId.vector
      (** Tuple - note that units are encoded as 0-tuples *)
  | Bottom  (** No value (uninitialized or moved value) *)
  | Assumed of assumed_value  (** Assumed types (Box, Vec, Cell...) *)
  | Borrow of borrow_content  (** A borrowed value *)
  | Loan of loan_content  (** A loaned value *)
  | Symbolic of symbolic_proj_comp  (** Unknown value *)

and adt_value = {
  def_id : TypeDefId.id;
  variant_id : VariantId.id option;
  regions : erased_region list;
  types : ety list;
  field_values : typed_value FieldId.vector;
}

and borrow_content =
  | SharedBorrow of BorrowId.id  (** A shared value *)
  | MutBorrow of BorrowId.id * typed_value  (** A mutably borrowed value *)
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
  | SharedLoan of BorrowId.Set.t * typed_value
  | MutLoan of BorrowId.id

and assumed_value = Box of typed_value

and typed_value = { value : value; ty : ety }

type abstract_shared_borrow =
  | AsvSet of BorrowId.Set.t
  | AsvProjReborrows of symbolic_value * rty
  | AsvUntion of abstract_shared_borrow * abstract_shared_borrow
      (** TODO: explanations *)

(** Abstraction values are used inside of abstractions to properly model
    borrowing relations introduced by function calls.

    When calling a function, we lose information about the borrow graph:
    part of it is thus "abstracted" away.
*)
type avalue =
  | AConcrete of constant_value
  | AAdt of aadt_value
  | ATuple of typed_avalue FieldId.vector
  | ABottom
  | AAssumed of aassumed_value
  | AMutBorrow of BorrowId.id * typed_avalue
  | ASharedBorrow of BorrowId.id
  | AMutLoan of BorrowId.id * typed_avalue
  | ASharedLoan of BorrowId.Set.t * value * typed_avalue
  | AEndedMutLoan of value * typed_avalue (* TODO: given_back, child *)
  | AEndedSharedLoan of value * typed_avalue
  | AIgnoredMutLoan of BorrowId.id * typed_avalue
  | AIgnoredMutBorrow of typed_avalue
  | AEndedIgnoredMutLoan of typed_avalue * typed_avalue (* TODO: given back, child *)
  | AIgnoredSharedBorrow of abstract_shared_borrow
  | AIgnoredSharedLoan of abstract_shared_borrow
  | AProjLoans of symbolic_value
  | AProjBorrows of symbolic_value * rty

and aadt_value = {
  adef_id : TypeDefId.id;
  avariant_id : VariantId.id option;
  aregions : erased_region list;
  atypes : rty list;
  afield_values : typed_avalue FieldId.vector;
}

and aassumed_value = ABox of typed_avalue

and typed_avalue = { avalue : avalue; aty : rty }

type abs = {
  parents : AbstractionId.Set.t;  (** The parent abstraction *)
  acc_regions : RegionId.Set.t;
      (** Union of the regions owned by the (transitive) parent abstractions and
          by the current abstraction *)
  regions : RegionId.Set.t;  (** Regions owned by this abstraction *)
  values : typed_avalue list;  (** The values in this abstraction *)
}
(** Abstractions model the parts in the borrow graph where the borrowing relations
    have been abstracted because of a function call.
    
    In order to model the relations between the borrows, we use "abstraction values",
    which are a special kind of value.
*)
