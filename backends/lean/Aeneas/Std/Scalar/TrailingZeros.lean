module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public section

namespace Aeneas.Std

open ScalarElab

/-!
# Trailing zeros
-/

/-- The number of trailing zero bits of `x`, which is `w` when `x = 0`.
    We reuse `BitVec.ctz` from the Lean core library so that its lemmas apply. -/
@[expose]
def BitVec.trailingZeros {w : Nat} (x : BitVec w) : Nat :=
  x.ctz.toNat

#guard BitVec.trailingZeros 0#16 = 16
#guard BitVec.trailingZeros 1#16 = 0
#guard BitVec.trailingZeros 2#16 = 1
#guard BitVec.trailingZeros 12#16 = 2
#guard BitVec.trailingZeros 0x8000#16 = 15
#guard BitVec.trailingZeros 0#64 = 64
#guard BitVec.trailingZeros (1#64 <<< 52) = 52
#guard BitVec.trailingZeros 0xFFFFFFFF#32 = 0

scalar @[expose, step_pure_def] def core.num.«%S».trailing_zeros (x : «%S») : U32 :=
  ⟨ BitVec.trailingZeros x.bv ⟩

end Aeneas.Std
