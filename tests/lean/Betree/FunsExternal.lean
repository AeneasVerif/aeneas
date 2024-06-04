-- [betree]: external functions.
import Base
import Betree.Types
open Primitives
open betree

-- TODO: fill those bodies

/- [betree::betree_utils::load_internal_node] -/
def betree_utils.load_internal_node
  :
  U64 → State → Result (State × (betree.List (U64 × betree.Message))) :=
  fun _ _ => .fail .panic

/- [betree::betree_utils::store_internal_node] -/
def betree_utils.store_internal_node
  :
  U64 → betree.List (U64 × betree.Message) → State → Result (State
    × Unit) :=
  fun _ _ _ => .fail .panic

/- [betree::betree_utils::load_leaf_node] -/
def betree_utils.load_leaf_node
  : U64 → State → Result (State × (betree.List (U64 × U64))) :=
  fun _ _ => .fail .panic

/- [betree::betree_utils::store_leaf_node] -/
def betree_utils.store_leaf_node
  : U64 → betree.List (U64 × U64) → State → Result (State × Unit) :=
  fun _ _ _ => .fail .panic
