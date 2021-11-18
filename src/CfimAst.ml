open Identifiers
open Types
open Values
open Expressions

module FunDefId = IdGen ()

type assumed_fun_id = BoxNew | BoxDeref | BoxDerefMut | BoxFree

type fun_id = Local of FunDefId.id | Assumed of assumed_fun_id

type assertion = { cond : operand; expected : bool }

type fun_sig = {
  region_params : region_var RegionVarId.vector;
  num_early_bound_regions : int;
  type_params : type_var TypeVarId.vector;
  inputs : rty VarId.vector;
  output : rty;
}

type call = {
  func : fun_id;
  region_params : erased_region list;
  type_params : ety list;
  args : operand list;
  dest : place;
}

type statement =
  | Assign of place * rvalue
  | FakeRead of place
  | SetDiscriminant of place * VariantId.id
  | Drop of place
  | Assert of assertion
  | Call of call
  | Panic
  | Return
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

type expression =
  | Statement of statement
  | Sequence of expression * expression
  | Switch of operand * switch_targets
  | Loop of expression

and switch_targets =
  | If of expression * expression  (** Gives the "if" and "else" blocks *)
  | SwitchInt of integer_type * (scalar_value * expression) list * expression
      (** The targets for a switch over an integer are:
          - the list `(matched value, expression to execute)`
          - the "otherwise" expression.
          Also note that we precise the type of the integer (uint32, int64, etc.)
          which we switch on. *)

type fun_def = {
  def_id : FunDefId.id;
  name : name;
  signature : fun_sig;
  divergent : bool;
  arg_count : int;
  locals : var VarId.vector;
  body : expression;
}
