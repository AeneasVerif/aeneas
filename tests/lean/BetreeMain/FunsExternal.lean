-- [betree_main]: external functions.
import Base
import BetreeMain.Types
open Primitives
open betree_main

-- TODO: fill those bodies

/- [betree_main::betree_utils::load_internal_node] -/
def betree_utils.load_internal_node
  :
  U64 → State → Result (State × (betree.List (U64 × betree.Message))) :=
  fun _ _ => .fail .panic

/- [betree_main::betree_utils::store_internal_node] -/
def betree_utils.store_internal_node
  :
  U64 → betree.List (U64 × betree.Message) → State → Result (State
    × Unit) :=
  fun _ _ _ => .fail .panic

/- [betree_main::betree_utils::load_leaf_node] -/
def betree_utils.load_leaf_node
  : U64 → State → Result (State × (betree.List (U64 × U64))) :=
  fun _ _ => .fail .panic

/- [betree_main::betree_utils::store_leaf_node] -/
def betree_utils.store_leaf_node
  : U64 → betree.List (U64 × U64) → State → Result (State × Unit) :=
  fun _ _ _ => .fail .panic

/- [core::option::Option::{0}::unwrap] -/
def core.option.Option.unwrap
  (T : Type) : Option T → State → Result (State × T) :=
  fun _ _ => .fail .panic
