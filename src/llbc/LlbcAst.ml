open Types
open Values
include Charon.LlbcAst

type abs_region_group = (RegionId.id, AbstractionId.id) g_region_group
[@@deriving show]

type abs_region_groups = abs_region_group list [@@deriving show]

(** A function signature, after instantiation *)
type inst_fun_sig = {
  regions_hierarchy : abs_region_groups;
  trait_type_constraints : trait_type_constraint region_binder list;
  inputs : rty list;
  output : rty;
}
[@@deriving show]
