open Names
open Types
open Values
open Expressions
open Identifiers

module FunDeclId = IdGen ()
module GlobalDeclId = IdGen ()

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

type assumed_fun_id =
  | Replace  (** `core::mem::replace` *)
  | BoxNew
  | BoxDeref  (** `core::ops::deref::Deref::<alloc::boxed::Box<T>>::deref` *)
  | BoxDerefMut
      (** `core::ops::deref::DerefMut::<alloc::boxed::Box<T>>::deref_mut` *)
  | BoxFree
  | VecNew
  | VecPush
  | VecInsert
  | VecLen
  | VecIndex  (** `core::ops::index::Index::index<alloc::vec::Vec<T>, usize>` *)
  | VecIndexMut
      (** `core::ops::index::IndexMut::index_mut<alloc::vec::Vec<T>, usize>` *)
[@@deriving show, ord]

type fun_id = Regular of FunDeclId.id | Assumed of assumed_fun_id
[@@deriving show, ord]

type assign_global = {
  dst : VarId.id;
  global : GlobalDeclId.id;
}
[@@deriving show]

type assertion = { cond : operand; expected : bool } [@@deriving show]

type abs_region_group = (AbstractionId.id, RegionId.id) g_region_group
[@@deriving show]

type abs_region_groups = (AbstractionId.id, RegionId.id) g_region_groups
[@@deriving show]

type fun_sig = {
  region_params : region_var list;
  num_early_bound_regions : int;
  regions_hierarchy : region_var_groups;
  type_params : type_var list;
  inputs : sty list;
  output : sty;
}
[@@deriving show]
(** A function signature, as used when declaring functions *)

type inst_fun_sig = {
  regions_hierarchy : abs_region_groups;
  inputs : rty list;
  output : rty;
}
[@@deriving show]
(** A function signature, after instantiation *)

type call = {
  func : fun_id;
  region_args : erased_region list;
  type_args : ety list;
  args : operand list;
  dest : place;
}
[@@deriving show]

(** Ancestor for [typed_value] iter visitor *)
class ['self] iter_statement_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter

    method visit_assign_global : 'env -> assign_global -> unit = fun _ _ -> ()

    method visit_place : 'env -> place -> unit = fun _ _ -> ()

    method visit_rvalue : 'env -> rvalue -> unit = fun _ _ -> ()

    method visit_id : 'env -> VariantId.id -> unit = fun _ _ -> ()

    method visit_assertion : 'env -> assertion -> unit = fun _ _ -> ()

    method visit_operand : 'env -> operand -> unit = fun _ _ -> ()

    method visit_call : 'env -> call -> unit = fun _ _ -> ()

    method visit_integer_type : 'env -> integer_type -> unit = fun _ _ -> ()

    method visit_scalar_value : 'env -> scalar_value -> unit = fun _ _ -> ()
  end

(** Ancestor for [typed_value] map visitor *)
class ['self] map_statement_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_assign_global : 'env -> assign_global -> assign_global = fun _ x -> x

    method visit_place : 'env -> place -> place = fun _ x -> x

    method visit_rvalue : 'env -> rvalue -> rvalue = fun _ x -> x

    method visit_id : 'env -> VariantId.id -> VariantId.id = fun _ x -> x

    method visit_assertion : 'env -> assertion -> assertion = fun _ x -> x

    method visit_operand : 'env -> operand -> operand = fun _ x -> x

    method visit_call : 'env -> call -> call = fun _ x -> x

    method visit_integer_type : 'env -> integer_type -> integer_type =
      fun _ x -> x

    method visit_scalar_value : 'env -> scalar_value -> scalar_value =
      fun _ x -> x
  end

type statement =
  | Assign of place * rvalue
  | AssignGlobal of assign_global
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

and switch_targets =
  | If of statement * statement  (** Gives the "if" and "else" blocks *)
  | SwitchInt of integer_type * (scalar_value list * statement) list * statement
      (** The targets for a switch over an integer are:
          - the list `(matched values, statement to execute)`
            We need a list for the matched values in case we do something like this:
            `switch n { 0 | 1 => ..., _ => ... }
          - the "otherwise" statement
          Also note that we precise the type of the integer (uint32, int64, etc.)
          which we switch on. *)
[@@deriving
  show,
    visitors
      {
        name = "iter_statement";
        variety = "iter";
        ancestors = [ "iter_statement_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      },
    visitors
      {
        name = "map_statement";
        variety = "map";
        ancestors = [ "map_statement_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      }]

type fun_body = { arg_count : int; locals : var list; body : statement }
[@@deriving show]

type fun_decl = {
  def_id : FunDeclId.id;
  name : fun_name;
  signature : fun_sig;
  body : fun_body option;
  is_global_body : bool;
}
[@@deriving show]

type global_decl = {
  def_id : GlobalDeclId.id;
  body_id: FunDeclId.id;
  name : global_name;
  ty: ety;
}
[@@deriving show]
