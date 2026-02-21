import Curve25519.Curve25519

open Aeneas Std Result

namespace curve25519

/-- Interpret a Scalar52 (five u64 limbs used to represent 52 bits each) as a natural number -/
def Scalar52.asNat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(52 * i) * (limbs[i]!).val

/-- Interpret a 9-element u128 array (each limb representing 52 bits) as a natural number -/
def Scalar52.wideAsNat (limbs : Array U128 9#usize) : Nat :=
  ∑ i ∈ Finset.range 9, 2^(52 * i) * (limbs[i]!).val

attribute [-simp] Int.reducePow Nat.reducePow

@[progress]
theorem m_spec (x y : U64) :
    m x y ⦃ result => result.val = x.val * y.val ⦄ := by
  unfold m
  progress*

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 500 in
@[progress]
theorem mul_internal_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 62) (hb : ∀ i < 5, b[i]!.val < 2 ^ 62) :
    mul_internal a b ⦃ result =>
      Scalar52.wideAsNat result = Scalar52.asNat a * Scalar52.asNat b ⦄ := by
  unfold mul_internal
  simp [Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index]
  progress*
  -- Post-condition
  simp [*, Scalar52.wideAsNat, Scalar52.asNat, Finset.sum_range_succ]
  ring_nf

end curve25519
