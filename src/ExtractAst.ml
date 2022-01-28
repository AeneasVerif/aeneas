(** This module defines the AST which is to be extracted to generate code.
    This AST is voluntarily as simple as possible, so that the extraction
    can focus on pretty-printing and on the syntax specific to the different
    provers.
 *)

type constant_value = Pure.constant_value

type pattern =
  | PatVar of string
  | PatDummy
  | PatEnum of string * pattern list
      (** Enum: the constructor name (tuple if `None`) and the fields.
          Note that we never use structures as patters: we access the fields one
          by one.
       *)
  | PatTuple of pattern list

(** We want to keep terms a little bit structured, for pretty printing.
    See the `FieldProj` and the `Record` cases, for instance.
 *)
type term =
  | Constant of constant_value
  | Var of string
  | FieldProj of term * term
      (** `x.y`

           Of course, we can always use projectors like `record_get_y x`:
           this variant is for pretty-printing.
           
           Note that `FieldProj` are generated when translating `place` from
           the "pure" AST.
       *)
  | App of term * term
  | Let of bool * pattern * term * term
  | If of term * term * term
  | Switch of term * (pattern * term) list
  | Ascribed of term * term  (** `x <: ty` *)
  | Tuple of term list
  | Record of (string * term) list
      (** In case a record has named fields, we try to use them, to generate
          code like: `{ x = 3; y = true; }`
          Otherwise, we can use `App` (with the record constructor).
       *)

type fun_def = {
  name : string;
  inputs : pattern list;
      (** We can match over the inputs, hence the use of [pattern]. In practice,
          we use [PatVar] and [PatDummy].
       *)
  input_tys : term list;
  output_ty : term;
  body : term;
}
