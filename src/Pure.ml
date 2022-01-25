open Identifiers
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
module TypeDefId = T.TypeDefId
module TypeVarId = T.TypeVarId
module RegionId = T.RegionId
module VariantId = T.VariantId
module FieldId = T.FieldId
module SymbolicValueId = V.SymbolicValueId
module FunDefId = A.FunDefId

module SynthPhaseId = IdGen ()
(** We give an identifier to every phase of the synthesis (forward, backward
    for group of regions 0, etc.) *)

module BackwardFunId = IdGen ()
(** Every backward function has its identifier *)

module VarId = IdGen ()
(** Pay attention to the fact that we also define a [VarId] module in Values *)

type ty =
  | Adt of T.type_id * ty list
      (** [Adt] encodes ADTs, tuples and assumed types.
       
          TODO: what about the ended regions?
       *)
  | TypeVar of TypeVarId.id
  | Bool
  | Char
  | Integer of T.integer_type
  | Str
  | Array of ty (* TODO: there should be a constant with the array *)
  | Slice of ty
[@@deriving show]

type field = { field_name : string; field_ty : ty } [@@deriving show]

type variant = { variant_name : string; fields : field list } [@@deriving show]

type type_def_kind = Struct of field list | Enum of variant list
[@@deriving show]

type type_var = T.type_var [@@deriving show]

type type_def = {
  def_id : TypeDefId.id;
  name : name;
  type_params : type_var list;
  kind : type_def_kind;
}
[@@deriving show]

type scalar_value = V.scalar_value

type constant_value = V.constant_value

type symbolic_value = {
  sv_id : SymbolicValueId.id;
  sv_ty : ty;
  sv_rty : T.rty;
  sv_ended_regions : RegionId.Set.t;
      (** We need to remember what was the set of ended regions at the time the
          symbolic value was introduced.
       *)
}

type value = Concrete of constant_value | Adt of adt_value

and adt_value = {
  variant_id : (VariantId.id option[@opaque]);
  field_values : typed_value list;
}

and typed_value = { value : value; ty : ty }

type var = { id : VarId.id; ty : ty }
(** Because we introduce a lot of temporary variables, the list of variables
    is not fixed: we thus must carry all its information with the variable
    itself
 *)

(** Sometimes, when introducing several variables in an assignment (because
    deconstructing a tuple) we can ignore some of the values: in such situation
    we introduce dummy variables (extracted to "_").
 *)
type var_or_dummy = Var of var | Dummy

type projection_elem = { pkind : E.field_proj_kind; field_id : FieldId.id }

type projection = projection_elem list

type place = { var : VarId.id; projection : projection }

type operand = Value of typed_value | Place of place

(* type assertion = { cond : operand; expected : bool } *)

type fun_id =
  | Local of A.FunDefId.id * BackwardFunId.id option
      (** Backward id: `Some` if the function is a backward function, `None`
          if it is a forward function *)
  | Assumed of A.assumed_fun_id
  | Unop of E.unop
  | Binop of E.binop

type call = { func : fun_id; type_params : ty list; args : operand list }

type left_value = unit
(** TODO: assignment left value *)

type let_bindings =
  | Call of var_or_dummy list * call
      (** The called function and the tuple of returned values *)
  | Assignment of var * place
      (** Variable assignment: the introduced variable and the place we read *)
  | ExpandEnum of var_or_dummy list * TypeDefId.id * VariantId.id * place
      (** When expanding an enumeration with exactly one variant, we first
          introduce something like this (with [ExpandEnum]):
          ```
          let Cons x tl = ls in
          ...
          ```
          
          Later, depending on the language we extract to, we can eventually
          update it to something like this (for F*, for instance):
          ```
          let x = Cons?.v ls in
          let tl = Cons?.tl ls in
          ...
          ```
          
          Note that we prefer not handling this case through a match.
          TODO: actually why not encoding it as a match internally, then
          generating the `let Cons ... = ... in ...` if we check there
          is exactly one variant?...
       *)

(** **Rk.:** here, [expression] is not at all equivalent to the expressions
    used in CFIM. They are lambda-calculus expressions, and are thus actually
    more general than the CFIM statements, in a sense.
 *)
type expression =
  | Return of operand
  | Panic
  | Let of let_bindings * expression
      (** Let bindings include the let-bindings introduced because of function calls *)
  | Switch of operand * switch_body

and switch_body =
  | If of expression * expression
  | SwitchInt of T.integer_type * (scalar_value * expression) list * expression
  | Match of match_branch list

and match_branch = {
  variant_id : VariantId.id;
  vars : symbolic_value list;
  branch : expression;
}

type fun_sig = {
  type_params : type_var list;
  inputs : ty list;
  outputs : ty list;
      (** The list of outputs.

          In case of a forward function, the list will have length = 1.
          However, in case of backward function, the list may have length > 1.
          If the length is > 1, it gets extracted to a tuple type. Followingly,
          we could not use a list because we can encode tuples, but here we
          want to account for the fact that we immediately deconstruct the tuple
          upon calling the backward function (because the backward function is
          called to update a set of values in the environment).
       *)
}

type fun_def = {
  def_id : FunDefId.id;
  name : name;
  signature : fun_sig;
  body : expression;
}
