open Identifiers
open Types
open Values
open Expressions

module FunDefId = IdGen ()

module RegionGroupId = IdGen ()

type var = {
  index : VarId.id;  (** Unique variable identifier *)
  name : string option;
  var_ty : ety;
      (** The variable type - erased type, because variables are not used
       ** in function signatures: they are only used to declare the list of
       ** variables manipulated by a function body *)
}
[@@deriving show]
(** A variable, as used in a function definition *)

type assumed_fun_id = BoxNew | BoxDeref | BoxDerefMut | BoxFree
[@@deriving show]

type fun_id = Local of FunDefId.id | Assumed of assumed_fun_id
[@@deriving show]

type assertion = { cond : operand; expected : bool } [@@deriving show]

type region_group = {
  id : RegionGroupId.id;
  regions : RegionVarId.id list;
  parents : RegionGroupId.id list;
}
[@@deriving show]
(** A group of regions.

    Results from a lifetime analysis: we group the regions with the same
    lifetime together, and compute the hierarchy between the regions.
    This is necessary to introduce the proper abstraction with the
    proper constraints, when evaluating a function call in symbolic mode.
*)

type region_groups = region_group list [@@deriving show]

type fun_sig = {
  region_params : region_var list;
  num_early_bound_regions : int;
  regions_hierarchy : region_groups;
  type_params : type_var list;
  inputs : sty list;
  output : sty;
}
[@@deriving show]

type call = {
  func : fun_id;
  region_params : erased_region list;
  type_params : ety list;
  args : operand list;
  dest : place;
}
[@@deriving show]

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
  | Sequence of statement * statement
  | Switch of operand * switch_targets
  | Loop of statement
[@@deriving show]

and switch_targets =
  | If of statement * statement  (** Gives the "if" and "else" blocks *)
  | SwitchInt of integer_type * (scalar_value * statement) list * statement
      (** The targets for a switch over an integer are:
          - the list `(matched value, statement to execute)`
          - the "otherwise" statement.
          Also note that we precise the type of the integer (uint32, int64, etc.)
          which we switch on. *)
[@@deriving show]

type fun_def = {
  def_id : FunDefId.id;
  name : name;
  signature : fun_sig;
  divergent : bool;
  arg_count : int;
  locals : var list;
  body : statement;
}
[@@deriving show]
(** TODO: function definitions (and maybe type definitions in the future)
  * contain information like `divergent`. I wonder if this information should
  * be stored directly inside the definitions or inside separate maps/sets.
  * Of course, if everything is stored in separate maps/sets, nothing
  * prevents us from computing this info in Charon (and thus exporting directly
  * it with the type/function defs), in which case we just have to implement special
  * treatment when deserializing, to move the info to a separate map. *)
