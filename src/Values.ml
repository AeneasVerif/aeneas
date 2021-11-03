open Identifiers
open Types

module VarId = IdGen ()

module FunDefId = IdGen ()

type var = {
  index : VarId.id;  (** Unique variable identifier *)
  name : string option;
  ty : ety;
      (** The variable type - erased type, because variables are not used
       ** in function signatures *)
}
(** A variable *)

(** A scalar value

    Note that we use unbounded integers everywhere.
    We then harcode the boundaries for the different types.
 *)
type scalar_value =
  | Isize of Big_int.big_int
  | I8 of Big_int.big_int
  | I16 of Big_int.big_int
  | I32 of Big_int.big_int
  | I64 of Big_int.big_int
  | I128 of Big_int.big_int
  | Usize of Big_int.big_int
  | U8 of Big_int.big_int
  | U16 of Big_int.big_int
  | U32 of Big_int.big_int
  | U64 of Big_int.big_int
  | U128 of Big_int.big_int

type constant_value =
  | Scalar of scalar_value
  | Bool of bool
  | Char of char
  | String of string
