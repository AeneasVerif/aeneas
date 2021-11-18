open Types
open Values

type field_proj_kind =
  | ProjAdt of TypeDefId.id * VariantId.id option
  | ProjTuple of int

type projection_elem =
  | Deref
  | DerefBox
  | Field of field_proj_kind * FieldId.id
  | Downcast of VariantId.id

type projection = projection_elem list

type place = { var_id : VarId.id; projection : projection }

type borrow_kind = Shared | Mut | TwoPhaseMut

type unop = Not | Neg

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
  | ConstantAdt of TypeDefId.id
  | Unit

type operand =
  | Copy of place
  | Move of place
  | Constant of ety * operand_constant_value

type aggregate_kind =
  | AggregatedTuple
  | AggregatedAdt of TypeDefId.id * VariantId.id option

type rvalue =
  | Use of operand
  | Ref of place * borrow_kind
  | UnaryOp of unop * operand
  | BinaryOp of binop * operand * operand
  | Discriminant of place
  | Aggregate of aggregate_kind * operand list
