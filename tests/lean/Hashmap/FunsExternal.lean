-- [hashmap]: external functions.
import Aeneas
import Hashmap.Types
open Aeneas.Std
open hashmap

-- TODO: fill those bodies

/- [hashmap::utils::deserialize]:
   Source: 'tests/src/hashmap.rs', lines 330:4-330:47 -/
def utils.deserialize
  : State → Result (State × (HashMap U64)) :=
  fun _ => .fail .panic

/- [hashmap::utils::serialize]:
   Source: 'tests/src/hashmap.rs', lines 325:4-325:46 -/
def utils.serialize
  : HashMap U64 → State → Result (State × Unit) :=
  fun _ _ => .fail .panic
