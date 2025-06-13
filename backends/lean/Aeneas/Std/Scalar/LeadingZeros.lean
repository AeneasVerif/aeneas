import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
# Leading zeros
-/

/- TODO: move to Mathlib?
   Also not sure this is the best way of defining this quantity -/
def BitVec.leadingZerosAux {w : Nat} (x : BitVec w) (i : Nat) : Nat :=
  if i < w then
    if ¬ x.getMsbD i then leadingZerosAux x (i + 1)
    else i
  else 0

def BitVec.leadingZeros {w : Nat} (x : BitVec w) : Nat :=
  leadingZerosAux x 0

#assert BitVec.leadingZeros 1#16 = 15
#assert BitVec.leadingZeros 1#32 = 31
#assert BitVec.leadingZeros 255#32 = 24

scalar @[progress_pure_def] def core.num.«%S».leading_zeros (x : «%S») : U32 := ⟨ BitVec.leadingZeros x.bv ⟩

end Aeneas.Std
