-- [hashmap_main]: templates for the external functions.
import Base
import HashmapMain.Types
open Primitives
open hashmap_main

-- TODO: fill those bodies

/- [hashmap_main::hashmap_utils::deserialize] -/
def hashmap_utils.deserialize
  : State → Result (State × (hashmap.HashMap U64)) :=
  fun _ => .fail .panic

/- [hashmap_main::hashmap_utils::serialize] -/
def hashmap_utils.serialize
  : hashmap.HashMap U64 → State → Result (State × Unit) :=
  fun _ _ => .fail .panic
