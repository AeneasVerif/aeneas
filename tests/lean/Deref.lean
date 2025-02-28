-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [deref]
import Aeneas
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace deref

/- [deref::use_deref_box]:
   Source: 'tests/src/deref.rs', lines 6:0-8:1 -/
def use_deref_box {T : Type} (x : T) : Result T :=
  ok (alloc.boxed.Box.deref x)

/- [deref::use_deref_mut_box]:
   Source: 'tests/src/deref.rs', lines 10:0-12:1 -/
def use_deref_mut_box {T : Type} (x : T) : Result (T × (T → T)) :=
  ok (alloc.boxed.Box.deref_mut x)

/- [deref::test_deref_box]:
   Source: 'tests/src/deref.rs', lines 14:0-22:1 -/
def test_deref_box : Result Unit :=
  do
  let ((_, deref_mut_back) : (I32 × (I32 → I32))) ←
    ↑(alloc.boxed.Box.deref_mut 0#i32)
  let b := deref_mut_back 1#i32
  let (x : I32) ← ↑(alloc.boxed.Box.deref b)
  massert (x = 1#i32)

/- [deref::use_deref_vec]:
   Source: 'tests/src/deref.rs', lines 24:0-26:1 -/
def use_deref_vec {T : Type} (x : alloc.vec.Vec T) : Result (Slice T) :=
  ok (alloc.vec.Vec.deref x)

/- [deref::use_deref_mut_vec]:
   Source: 'tests/src/deref.rs', lines 28:0-30:1 -/
def use_deref_mut_vec
  {T : Type} (x : alloc.vec.Vec T) :
  Result ((Slice T) × (Slice T → alloc.vec.Vec T))
  :=
  ok (alloc.vec.Vec.deref_mut x)

end deref
