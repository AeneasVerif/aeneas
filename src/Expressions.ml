open Types
open Values

type field_proj_kind =
  | ProjAdt of TypeDeclId.id * VariantId.id option
  | ProjOption of VariantId.id
      (** Option is an assumed type, coming from the standard library *)
  | ProjTuple of int
[@@deriving show]
(* arity of the tuple *)

type projection_elem =
  | Deref
  | DerefBox
  | Field of field_proj_kind * FieldId.id
[@@deriving show]

type projection = projection_elem list [@@deriving show]
type place = { var_id : VarId.id; projection : projection } [@@deriving show]
type borrow_kind = Shared | Mut | TwoPhaseMut [@@deriving show]

type unop =
  | Not
  | Neg
  | Cast of integer_type * integer_type
      (** Cast an integer from a source type to a target type *)
[@@deriving show, ord]

(** A binary operation

    Note that we merge checked binops and unchecked binops: we perform a
    micro-pass on the MIR AST to remove the assertions introduced by rustc,
    and later extract the binops which can fail (addition, substraction, etc.)
    or have preconditions (division, remainder...) to monadic functions.
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
[@@deriving show, ord]

let all_binops =
  [
    BitXor;
    BitAnd;
    BitOr;
    Eq;
    Lt;
    Le;
    Ne;
    Ge;
    Gt;
    Div;
    Rem;
    Add;
    Sub;
    Mul;
    Shl;
    Shr;
  ]

(** Constant value for an operand

    It is a bit annoying, but rustc treats some ADT and tuple instances as
    constants when generating MIR:
    - an enumeration with one variant and no fields is a constant.
    - a structure with no field is a constant.
    - sometimes, Rust stores the initialization of an ADT as a constant
      (if all the fields are constant) rather than as an aggregated value

    For our translation, we use the following enumeration to encode those
    special cases in assignments. They are converted to "normal" values
    when evaluating the assignment (which is why we don't put them in the
    [ConstantValue] enumeration).
 *)
type operand_constant_value =
  | ConstantValue of constant_value
  | ConstantAdt of VariantId.id option * operand_constant_value list
[@@deriving show]

(* TODO: symplify the operand constant values *)
type operand =
  | Copy of place
  | Move of place
  | Constant of ety * operand_constant_value
[@@deriving show]

(** An aggregated ADT.

    Note that ADTs are desaggregated at some point in MIR. For instance, if
    we have in Rust:
    ```
    let ls = Cons(hd, tl);
    ```
    
    In MIR we have (yes, the discriminant update happens *at the end* for some
    reason):
    ```
    (ls as Cons).0 = move hd;
    (ls as Cons).1 = move tl;
    discriminant(ls) = 0; // assuming `Cons` is the variant of index 0
    ```
    
    Note that in our semantics, we handle both cases (in case of desaggregated
    initialization, `ls` is initialized to `⊥`, then this `⊥` is expanded to
    `Cons (⊥, ⊥)` upon the first assignment, at which point we can initialize
    the field 0, etc.).
 *)
type aggregate_kind =
  | AggregatedTuple
  | AggregatedOption of VariantId.id * ety
  (* TODO: AggregatedOption should be merged with AggregatedAdt *)
  | AggregatedAdt of
      TypeDeclId.id * VariantId.id option * erased_region list * ety list
[@@deriving show]

(* TODO: move the aggregate kind to operands *)
type rvalue =
  | Use of operand
  | Ref of place * borrow_kind
  | UnaryOp of unop * operand
  | BinaryOp of binop * operand * operand
  | Discriminant of place
  | Aggregate of aggregate_kind * operand list
[@@deriving show]
