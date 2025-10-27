open Types
open Values
include Charon.LlbcAst

type abs_region_group = (RegionId.id, AbsId.id) g_region_group [@@deriving show]
type abs_region_groups = abs_region_group list [@@deriving show]

(** A function signature, after instantiation *)
type inst_fun_sig = {
  regions_hierarchy : region_var_groups;
      (** **WARNING**: the region ids in those groups should have been
          substituted with fresh regions. *)
  abs_regions_hierarchy : abs_region_groups;
  trait_type_constraints : trait_type_constraint region_binder list;
  inputs : rty list;
  output : rty;
}
[@@deriving show]
