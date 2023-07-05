-- [betree_main]: external functions.
import Base
import BetreeMain.Types
open Primitives
open betree_main

-- TODO: fill those bodies

/- [betree_main::betree_utils::load_internal_node] -/
def betree_utils.load_internal_node_fwd
  :
  U64 → State → Result (State × (betree_list_t (U64 × betree_message_t))) :=
  fun _ _ => .fail .panic

/- [betree_main::betree_utils::store_internal_node] -/
def betree_utils.store_internal_node_fwd
  :
  U64 → betree_list_t (U64 × betree_message_t) → State → Result (State
    × Unit) :=
  fun _ _ _ => .fail .panic

/- [betree_main::betree_utils::load_leaf_node] -/
def betree_utils.load_leaf_node_fwd
  : U64 → State → Result (State × (betree_list_t (U64 × U64))) :=
  fun _ _ => .fail .panic

/- [betree_main::betree_utils::store_leaf_node] -/
def betree_utils.store_leaf_node_fwd
  : U64 → betree_list_t (U64 × U64) → State → Result (State × Unit) :=
  fun _ _ _ => .fail .panic

/- [core::option::Option::{0}::unwrap] -/
def core.option.Option.unwrap_fwd
  (T : Type) : Option T → State → Result (State × T) :=
  fun _ _ => .fail .panic
