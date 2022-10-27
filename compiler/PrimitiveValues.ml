(** The primitive values. *)

open Types

(** We use big integers to store the integer values (this way we don't have
    to think about the bounds, nor architecture issues - Rust allows to
    manipulate 128-bit integers for instance).
 *)
type big_int = Z.t

let big_int_of_yojson (json : Yojson.Safe.t) : (big_int, string) result =
  match json with
  | `Int i -> Ok (Z.of_int i)
  | `Intlit is -> Ok (Z.of_string is)
  | _ -> Error "not an integer or an integer literal"

let big_int_to_yojson (i : big_int) = `Intlit (Z.to_string i)

let pp_big_int (fmt : Format.formatter) (bi : big_int) : unit =
  Format.pp_print_string fmt (Z.to_string bi)

let show_big_int (bi : big_int) : string = Z.to_string bi

(** A scalar value

    Note that we use unbounded integers everywhere.
    We then harcode the boundaries for the different types.
 *)
type scalar_value = { value : big_int; int_ty : integer_type } [@@deriving show]

(** A primitive value.

    Can be used by operands (in which case it represents a constant) or by
    the interpreter to represent a concrete, primitive value.
 *)
type primitive_value =
  | Scalar of scalar_value
  | Bool of bool
  | Char of char
  | String of string
[@@deriving show]
