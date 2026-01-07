import Aeneas.Bvify.Bvify
import Aeneas.SimpScalar

@[bvify_simps]
theorem BitVec.ofNat_mod (n a k : Nat) (h : k < n) :
  BitVec.ofNat n (a % 2^k) = (BitVec.ofNat n a) % (2^k) := by
  natify; simp
  have : 2 ^ k < 2 ^ n := by simp_scalar
  simp_scalar
  cases k
  · simp [Nat.mod_one]
    simp_scalar
  · rename_i k
    have : 2 < 2 ^ n := by simp_scalar
    simp_scalar


/-- Same as `BitVec.ofNat_mod'` but with a precondition expressed in terms of `isPowerOfTwo'`.

TODO: how to make this trigger only on concrete values for `b` (e.g., `2`, `3`, `256`, etc.)? -/
@[bvify_simps]
theorem BitVec.ofNat_mod' (n a b : Nat) (h : b.isPowerOfTwo' ∧ b.log2 < n) :
  BitVec.ofNat n (a % b) = (BitVec.ofNat n a) % b := by
  simp only [Nat.isPowerOfTwo'_iff] at h
  replace ⟨ ⟨ k, h ⟩, h' ⟩ := h
  have := BitVec.ofNat_mod n a k (by simp only [h, Nat.log2_two_pow] at h'; omega)
  simp only [ofNat_eq_ofNat, Nat.cast_pow, Nat.cast_ofNat, h, this]

@[bvify_simps]
theorem BitVec.ofNat_shiftLeft (a b : ℕ) (hb : b < 2 ^ n) :
  BitVec.ofNat n (a <<< b) = BitVec.ofNat n a <<< BitVec.ofNat n b := by
  natify
  simp only [Nat.shiftLeft_eq, shiftLeft_eq', toNat_ofNat, toNat_shiftLeft, Nat.mod_mul_mod]
  simp_scalar

@[bvify_simps]
theorem BitVec.ofNat_shiftRight (a b : ℕ) (h : a < 2 ^n ∧ b < 2 ^ n) :
  BitVec.ofNat n (a >>> b) = BitVec.ofNat n a >>> BitVec.ofNat n b := by
  natify
  simp only [ushiftRight_eq', toNat_ofNat, toNat_ushiftRight]
  simp_scalar
  simp [Nat.shiftRight_eq_div_pow]
  have : a / 2 ^b ≤ a / 2 ^ 0 := by
    apply Nat.div_le_div_left <;> simp only [pow_zero, Nat.ofNat_pos, Aeneas.SimpScalar.one_le_pow, pow_zero, zero_lt_one]
  simp_scalar

example (limb0 limb1 : Nat) (h0 : limb0 ≤ 2 ^ 64 - 1) (h1 : limb1 ≤ 2 ^ 64 - 1) (h : limb0 < 2 ^ 51) :
  ((limb0 >>> 48 ||| limb1 <<< 4) % 2 ^ 8) = (limb0 >>> 48 % 2 ^ 8) + ((limb1 <<< 4) % 2 ^ 8)
  := by
  bvify 64 at *
  simp only [BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.cast_ofNat,
    BitVec.ofNat_eq_ofNat]
  bv_decide
