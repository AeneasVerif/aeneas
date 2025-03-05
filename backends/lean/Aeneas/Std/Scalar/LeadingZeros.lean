import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

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

@[progress_pure_def] def core.num.Usize.leading_zeros (x : Usize) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩
@[progress_pure_def] def core.num.U8.leading_zeros (x : U8) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩
@[progress_pure_def] def core.num.U16.leading_zeros (x : U16) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩
@[progress_pure_def] def core.num.U32.leading_zeros (x : U32) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩
@[progress_pure_def] def core.num.U64.leading_zeros (x : U64) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩
@[progress_pure_def] def core.num.U128.leading_zeros (x : U128) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩

@[progress_pure_def] def core.num.Isize.leading_zeros (x : Isize) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩
@[progress_pure_def] def core.num.I8.leading_zeros (x : I8) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩
@[progress_pure_def] def core.num.I16.leading_zeros (x : I16) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩
@[progress_pure_def] def core.num.I32.leading_zeros (x : I32) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩
@[progress_pure_def] def core.num.I64.leading_zeros (x : I64) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩
@[progress_pure_def] def core.num.I128.leading_zeros (x : I128) : U32 := ⟨ BitVec.leadingZeros x.bv ⟩

end Aeneas.Std
