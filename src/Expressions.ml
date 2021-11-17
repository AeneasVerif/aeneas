open Types
open Values

type field_proj_kind =
  | Adt of TypeDefId.id * VariantId.id option
  | Tuple of int
[@@deriving of_yojson]

type projection_elem =
  | Deref
  | DerefBox
  | Field of field_proj_kind * FieldId.id
  | Downcast of VariantId.id
[@@deriving of_yojson]

type projection = projection_elem list [@@deriving of_yojson]

type place = { var_id : VarId.id; projection : projection }
[@@deriving of_yojson]

type borrow_kind = Shared | Mut | TwoPhaseMut [@@deriving of_yojson]

type unop = Not | Neg [@@deriving of_yojson]

(** A binary operation

    Note that we merge checked binops and unchecked binops: we perform a
    micro-pass on the MIR AST to remove the assertions introduced by rustc,
    and use monadic functions for the binops which can fail (addition,
    substraction, etc.) or have preconditions (division, remainder...)
 *)
type binop =
  | BitXor
  | BitAnd
  | BitOr
  | Eq
  | Lt
  | Le
  | Ne
  | Ge
  | Gt
  | Div
  | Rem
  | Add
  | Sub
  | Mul
  | Shl
  | Shr
[@@deriving of_yojson]

(** Constant value for an operand

    It is a bit annoying, but Rust treats some ADT and tuple instances as
    constants.
    For instance, an enumeration with one variant and no fields is a constant.
    A structure with no field is a constant.

    For our translation, we use the following enumeration to encode those
    special cases in assignments. They are converted to "normal" values
    when evaluating the assignment (which is why we don't put them in the
    [ConstantValue] enumeration.

 *)
type operand_constant_value =
  | ConstantValue of constant_value
  | Adt of TypeDefId.id
  | Unit
[@@deriving of_yojson]

type operand =
  | Copy of place
  | Move of place
  | Constant of ety * operand_constant_value
[@@deriving of_yojson]

type aggregate_kind = Tuple | Adt of TypeDefId.id * VariantId.id list
[@@deriving of_yojson]

type rvalue =
  | Use of operand
  | Ref of place * borrow_kind
  | UnaryOp of unop * operand
  | BinaryOp of binop * operand * operand
  | Discriminant of place
  | Aggregate of aggregate_kind * operand list
[@@deriving of_yojson]
