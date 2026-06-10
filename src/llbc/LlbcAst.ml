open Types
open Values
include Charon.LlbcAst

module FunOrMethodId = struct
  type id = Fun of FunDeclId.id | Method of TraitDeclId.id * TraitMethodId.id
  [@@deriving show, ord]

  type t = id

  let compare = compare_id
  let to_string = show_id
  let pp_t = pp_id
  let show_t = show_id
  let of_regular_fun_decl_id (id : FunDeclId.id) : id = Fun id

  let of_trait_method (trait_ref : trait_ref) (method_id : TraitMethodId.id) :
      id =
    Method (trait_ref.trait_decl_ref.binder_value.id, method_id)

  module Ord : Collections.OrderedType with type t = id = struct
    type t = id

    let compare = compare_id
    let to_string = show_id
    let pp_t = pp_id
    let show_t = show_id
  end

  module Map = Collections.MakeMap (Ord)
  module Set = Collections.MakeSet (Ord)
end

type bound_fun_sig = Charon.TypesUtils.bound_fun_sig
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
