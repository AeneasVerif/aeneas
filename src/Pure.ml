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

module SynthPhaseId = IdGen ()
(** We give an identifier to every phase of the synthesis (forward, backward
    for group of regions 0, etc.) *)

module BackwardFunId = IdGen ()
(** Every backward function has its identifier *)

type ty =
  | Adt of T.type_id * ty list
      (** [Adt] encodes ADTs, tuples and assumed types.
       
          TODO: what about the ended regions?
       *)
  | TypeVar of TypeVarId.id
  | Bool
  | Char
  | Never
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

type value =
  | Concrete of constant_value
  | Adt of adt_value
  | Symbolic of symbolic_value

and adt_value = {
  variant_id : (VariantId.id option[@opaque]);
  field_values : typed_value list;
}

and typed_value = { value : value; ty : ty }

type projection_elem = { pkind : E.field_proj_kind; field_id : FieldId.id }

type projection = projection_elem list

type operand = typed_value

type assertion = { cond : operand; expected : bool }

type fun_id =
  | Local of A.FunDefId.id * BackwardFunId.id option
      (** Backward id: `Some` if the function is a backward function, `None`
          if it is a forward function *)
  | Assumed of A.assumed_fun_id
  | Unop of E.unop
  | Binop of E.binop

type call = { func : fun_id; type_params : ty list; args : operand list }

type let_bindings = { call : call; bindings : symbolic_value list }

(** **Rk.:** here, [expression] is not at all equivalent to the expressions
    used in CFIM. They are lambda-calculus expressions, and are thus actually
    more general than the CFIM statements, in a sense.
 *)
type expression =
  | Let of let_bindings * expression
      (** Let bindings include the let-bindings introduced because of function calls *)
  | Assert of assertion
  | Return of typed_value
  | Panic of SynthPhaseId.id
  | Nop
  | Sequence of expression * expression
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
