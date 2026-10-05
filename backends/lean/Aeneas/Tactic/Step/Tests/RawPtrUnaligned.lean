module
public import Aeneas.Tactic.Step
public section

open Aeneas Aeneas.Std Aeneas.SepLogic WP Result

namespace Aeneas.Tactic.Step.Tests.RawPtrUnaligned

def writeReadOdd (p : MutRawPtr U8) (v : U16) : Result U16 := do
  core.ptr.write_unaligned ((p.add 1).retype : MutRawPtr U16) v
  core.ptr.read_unaligned ((p.add 1).retype : ConstRawPtr U16)

/-- A `u16` written at an odd (unaligned) address can be read back. -/
example (p : MutRawPtr U8) (b0 b1 b2 : U8) (v : U16) :
    ⦃ p ↦* [b0, b1, b2] ⦄ writeReadOdd p v
    ⦃⇓ r => ⌜r = v⌝ ∗ p ↦* (b0 :: (ByteRepr.encode v).map (UScalar.mk (ty := .U8))) ⦄ := by
  unfold writeReadOdd
  change ⦃ p ↦ b0 ∗ (p.add 1) ↦* [b1, b2] ⦄ _ ⦃⇓ r => ⌜r = v⌝ ∗ (p ↦ b0 ∗ (p.add 1) ↦* _) ⦄
  step with MutRawPtr.writeUnaligned.spec ((p.add 1).retype : MutRawPtr U16) [b1, b2] v (by simp)
  simp only [RawPtr.bytesPtr_retype, RawPtr.pointsToRange_retype_eq]
  step with RawPtr.readUnaligned.spec ((p.add 1).retype : ConstRawPtr U16) v
  simp only [RawPtr.bytesPtr_retype, RawPtr.pointsToRange_retype_eq]
  iframe

end Aeneas.Tactic.Step.Tests.RawPtrUnaligned
