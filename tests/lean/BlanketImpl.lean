-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [blanket_impl]
import Aeneas
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace blanket_impl

/- Trait declaration: [blanket_impl::Trait1]
   Source: 'tests/src/blanket_impl.rs', lines 3:0-3:15 -/
structure Trait1 (Self : Type) where

/- Trait declaration: [blanket_impl::Trait2]
   Source: 'tests/src/blanket_impl.rs', lines 4:0-4:15 -/
structure Trait2 (Self : Type) where

/- Trait implementation: [blanket_impl::{blanket_impl::Trait2 for T}]
   Source: 'tests/src/blanket_impl.rs', lines 7:0-7:31 -/
@[reducible]
def Trait2.Blanket {T : Type} (Trait1Inst : Trait1 T) : Trait2 T := {
}

end blanket_impl
