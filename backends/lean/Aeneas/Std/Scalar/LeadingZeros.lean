import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab
import Mathlib.Data.Nat.Log

namespace Aeneas.Std

open ScalarElab

/-!
# Leading zeros
-/

def BitVec.leadingZeros {w : Nat} (x : BitVec w) : Nat :=
  if x = 0 then w else w - (Nat.log 2 x.toNat) - 1

#assert BitVec.leadingZeros 0#16 = 16
#assert BitVec.leadingZeros 1#16 = 15
#assert BitVec.leadingZeros 3#16 = 14
#assert BitVec.leadingZeros 1#32 = 31
#assert BitVec.leadingZeros 255#32 = 24

scalar @[step_pure_def] def core.num.«%S».leading_zeros (x : «%S») : U32 := ⟨ BitVec.leadingZeros x.toBitVec ⟩

end Aeneas.Std
