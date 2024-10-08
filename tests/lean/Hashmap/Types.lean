-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [hashmap]: type definitions
import Base
import Hashmap.TypesExternal
open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace hashmap

/- [hashmap::AList]
   Source: 'tests/src/hashmap.rs', lines 30:0-33:1 -/
inductive AList (T : Type) :=
| Cons : Usize → T → AList T → AList T
| Nil : AList T

/- [hashmap::HashMap]
   Source: 'tests/src/hashmap.rs', lines 46:0-58:1 -/
structure HashMap (T : Type) where
  num_entries : Usize
  max_load_factor : (Usize × Usize)
  max_load : Usize
  saturated : Bool
  slots : alloc.vec.Vec (AList T)

end hashmap
