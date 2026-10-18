module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public import Mathlib.Data.Nat.Log
import all Mathlib.Data.Nat.Log
public section

namespace Aeneas.Std

open ScalarElab

/-!
# Leading zeros
-/

@[expose]
def BitVec.leadingZeros {w : Nat} (x : BitVec w) : Nat :=
  if x = 0 then w else w - (Nat.log 2 x.toNat) - 1

#guard BitVec.leadingZeros 0#16 = 16
#guard BitVec.leadingZeros 1#16 = 15
#guard BitVec.leadingZeros 3#16 = 14
#guard BitVec.leadingZeros 1#32 = 31
#guard BitVec.leadingZeros 255#32 = 24

scalar @[expose, step_pure_def] def core.num.«%S».leading_zeros (x : «%S») : U32 :=
  ⟨ BitVec.leadingZeros x.bv ⟩

end Aeneas.Std
