-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [hashmap]: external functions.
-- This is a template file: rename it to "FunsExternal.lean" and fill the holes.
import Base
import Hashmap.Types
open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
open hashmap

/- [hashmap::utils::deserialize]:
   Source: 'tests/src/hashmap.rs', lines 336:4-336:47 -/
axiom utils.deserialize : State → Result (State × (HashMap U64))

/- [hashmap::utils::serialize]:
   Source: 'tests/src/hashmap.rs', lines 331:4-331:46 -/
axiom utils.serialize : HashMap U64 → State → Result (State × Unit)

