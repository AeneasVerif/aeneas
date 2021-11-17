open Identifiers
open Types

module VarId = IdGen ()

type var = {
  index : VarId.id;  (** Unique variable identifier *)
  name : string option;
  ty : ety;
      (** The variable type - erased type, because variables are not used
       ** in function signatures *)
}
[@@deriving yojson]
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
[@@deriving yojson]

type constant_value =
  | Scalar of scalar_value
  | Bool of bool
  | Char of char
  | String of string
[@@deriving yojson]
