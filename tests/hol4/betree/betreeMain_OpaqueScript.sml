(** [betree_main]: external function declarations *)
open primitivesLib divDefLib
open betreeMain_TypesTheory

val _ = new_theory "betreeMain_Opaque"


(** [betree_main::betree_utils::load_internal_node]: forward function *)val _ = new_constant ("betree_utils_load_internal_node_fwd",
  “:u64 -> state -> (state # (u64 # betree_message_t) betree_list_t)
  result”)

(** [betree_main::betree_utils::store_internal_node]: forward function *)val _ = new_constant ("betree_utils_store_internal_node_fwd",
  “:u64 -> (u64 # betree_message_t) betree_list_t -> state -> (state # unit)
  result”)

(** [betree_main::betree_utils::load_leaf_node]: forward function *)val _ = new_constant ("betree_utils_load_leaf_node_fwd",
  “:u64 -> state -> (state # (u64 # u64) betree_list_t) result”)

(** [betree_main::betree_utils::store_leaf_node]: forward function *)val _ = new_constant ("betree_utils_store_leaf_node_fwd",
  “:u64 -> (u64 # u64) betree_list_t -> state -> (state # unit) result”)

(** [core::option::Option::{0}::unwrap]: forward function *)val _ = new_constant ("core_option_option_unwrap_fwd",
  “:'t option -> state -> (state # 't) result”)

val _ = export_theory ()
