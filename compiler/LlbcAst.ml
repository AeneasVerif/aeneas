open Types
open Values
include Charon.LlbcAst

type abs_region_group = (AbstractionId.id, RegionId.id) g_region_group
[@@deriving show]

type abs_region_groups = (AbstractionId.id, RegionId.id) g_region_groups
[@@deriving show]

(** A function signature, after instantiation *)
type inst_fun_sig = {
  regions_hierarchy : abs_region_groups;
  inputs : rty list;
  output : rty;
}
[@@deriving show]
