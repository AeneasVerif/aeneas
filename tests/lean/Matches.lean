-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [matches]
import Base
open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace matches

/- [matches::match_u32]:
   Source: 'tests/src/matches.rs', lines 4:0-10:1 -/
def match_u32 (x : U32) : Result U32 :=
  match x with
  | 0#scalar => Result.ok 0#u32
  | 1#scalar => Result.ok 1#u32
  | _ => Result.ok 2#u32

end matches
