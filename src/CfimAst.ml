open Identifiers
open Types
open Values
open Expressions

type assumed_fun_id = BoxNew | BoxDeref | BoxDerefMut | BoxFree
[@@deriving of_yojson]

type fun_id = Local of FunDefId.id | Assumed of assumed_fun_id
[@@deriving of_yojson]

type assertion = { cond : operand; expected : bool } [@@deriving of_yojson]

type fun_sig = {
  region_params : region_var RegionVarId.vector;
  num_early_bound_regions : int;
  type_params : type_var TypeVarId.vector;
  inputs : rty VarId.vector;
  output : rty;
}
[@@deriving of_yojson]

type call = {
  func : fun_id;
  region_params : erased_region list;
  type_params : ety list;
  args : operand list;
  dest : place;
}
[@@deriving of_yojson]

type statement =
  | Assign of place * rvalue
  | FakeRead of place
  | SetDiscriminant of place * VariantId.id
  | Drop of place
  | Assert of assertion
  | Call of call
  | Panic
  | Returna
  | Break of int
      (** Break to (outer) loop. The [int] identifies the loop to break to:
          * 0: break to the first outer loop (the current loop)
          * 1: break to the second outer loop
          * ...
          *)
  | Continue of int
      (** Continue to (outer) loop. The loop identifier works
          the same way as for [Break] *)
  | Nop
[@@deriving of_yojson]

type expression =
  | Statement of statement
  | Sequence of expression * expression
  | Switch of operand * switch_targets
  | Loop of expression
[@@deriving of_yojson]

and switch_targets =
  | If of expression * expression  (** Gives the "if" and "else" blocks *)
  | SwitchInt of integer_type * (scalar_value * expression) list * expression
      (** The targets for a switch over an integer are:
          - the list `(matched value, expression to execute)`
          - the "otherwise" expression.
          Also note that we precise the type of the integer (uint32, int64, etc.)
          which we switch on. *)
[@@deriving of_yojson]

type fun_def = {
  def_id : FunDefId.id;
  name : name;
  signature : fun_sig;
  divergent : bool;
  arg_count : int;
  locals : var VarId.vector;
  body : expression;
}
[@@deriving of_yojson]
