import Aeneas.Tactic.Solver.BvTac.BvTac

/-!
# Bitwise identity lemmas for scalar types

`x &&& maxVal = x` and `maxVal &&& x = x` at the scalar, `.val` (Nat), and `.bv` (BitVec) levels
for each unsigned scalar type.
-/

namespace Aeneas.Std

open Aeneas.Std

-- ============================================================================
-- x &&& maxVal = x  (scalar level)
-- ============================================================================

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.and_maxVal (x : U8) : x &&& 255#u8 = x := by bv_tac 8
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.and_maxVal (x : U16) : x &&& 65535#u16 = x := by bv_tac 16
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.and_maxVal (x : U32) : x &&& 4294967295#u32 = x := by bv_tac 32
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.and_maxVal (x : U64) : x &&& 18446744073709551615#u64 = x := by bv_tac 64
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.and_maxVal (x : U128) : x &&& 340282366920938463463374607431768211455#u128 = x := by bv_tac 128

-- ============================================================================
-- maxVal &&& x = x  (scalar level)
-- ============================================================================

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.maxVal_and (x : U8) : 255#u8 &&& x = x := by bv_tac 8
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.maxVal_and (x : U16) : 65535#u16 &&& x = x := by bv_tac 16
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.maxVal_and (x : U32) : 4294967295#u32 &&& x = x := by bv_tac 32
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.maxVal_and (x : U64) : 18446744073709551615#u64 &&& x = x := by bv_tac 64
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.maxVal_and (x : U128) : 340282366920938463463374607431768211455#u128 &&& x = x := by bv_tac 128

-- ============================================================================
-- x.bv &&& maxVal = x.bv  (BitVec level)
-- ============================================================================

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.bv_and_maxVal (x : U8) : x.bv &&& 255#8 = x.bv := by bv_tac 8
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.bv_and_maxVal (x : U16) : x.bv &&& 65535#16 = x.bv := by bv_tac 16
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.bv_and_maxVal (x : U32) : x.bv &&& 4294967295#32 = x.bv := by bv_tac 32
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.bv_and_maxVal (x : U64) : x.bv &&& 18446744073709551615#64 = x.bv := by bv_tac 64
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.bv_and_maxVal (x : U128) : x.bv &&& 340282366920938463463374607431768211455#128 = x.bv := by bv_tac 128

-- ============================================================================
-- maxVal &&& x.bv = x.bv  (BitVec level)
-- ============================================================================

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.bv_maxVal_and (x : U8) : 255#8 &&& x.bv = x.bv := by bv_tac 8
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.bv_maxVal_and (x : U16) : 65535#16 &&& x.bv = x.bv := by bv_tac 16
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.bv_maxVal_and (x : U32) : 4294967295#32 &&& x.bv = x.bv := by bv_tac 32
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.bv_maxVal_and (x : U64) : 18446744073709551615#64 &&& x.bv = x.bv := by bv_tac 64
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.bv_maxVal_and (x : U128) : 340282366920938463463374607431768211455#128 &&& x.bv = x.bv := by bv_tac 128

-- ============================================================================
-- x.val &&& maxVal = x.val  (Nat level)
-- ============================================================================

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.val_and_maxVal (x : U8) : x.val &&& 255 = x.val := by
  have h := congrArg UScalar.val (U8.and_maxVal x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.val_and_maxVal (x : U16) : x.val &&& 65535 = x.val := by
  have h := congrArg UScalar.val (U16.and_maxVal x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.val_and_maxVal (x : U32) : x.val &&& 4294967295 = x.val := by
  have h := congrArg UScalar.val (U32.and_maxVal x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.val_and_maxVal (x : U64) : x.val &&& 18446744073709551615 = x.val := by
  have h := congrArg UScalar.val (U64.and_maxVal x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.val_and_maxVal (x : U128) : x.val &&& 340282366920938463463374607431768211455 = x.val := by
  have h := congrArg UScalar.val (U128.and_maxVal x); simp only [UScalar.val_and] at h; exact h

-- ============================================================================
-- maxVal &&& x.val = x.val  (Nat level)
-- ============================================================================

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.maxVal_and_val (x : U8) : 255 &&& x.val = x.val := by
  have h := congrArg UScalar.val (U8.maxVal_and x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.maxVal_and_val (x : U16) : 65535 &&& x.val = x.val := by
  have h := congrArg UScalar.val (U16.maxVal_and x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.maxVal_and_val (x : U32) : 4294967295 &&& x.val = x.val := by
  have h := congrArg UScalar.val (U32.maxVal_and x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.maxVal_and_val (x : U64) : 18446744073709551615 &&& x.val = x.val := by
  have h := congrArg UScalar.val (U64.maxVal_and x); simp only [UScalar.val_and] at h; exact h
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.maxVal_and_val (x : U128) : 340282366920938463463374607431768211455 &&& x.val = x.val := by
  have h := congrArg UScalar.val (U128.maxVal_and x); simp only [UScalar.val_and] at h; exact h

-- ============================================================================
-- x.bv % (2^n)#n = x.bv  (BitVec level)
-- ============================================================================

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.bv_mod_size (x : U8) : x.bv % 256#8 = x.bv := by bv_tac 8
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.bv_mod_size (x : U16) : x.bv % 65536#16 = x.bv := by bv_tac 16
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.bv_mod_size (x : U32) : x.bv % 4294967296#32 = x.bv := by bv_tac 32
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.bv_mod_size (x : U64) : x.bv % 18446744073709551616#64 = x.bv := by bv_tac 64
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.bv_mod_size (x : U128) : x.bv % 340282366920938463463374607431768211456#128 = x.bv := by bv_tac 128

-- ============================================================================
-- x.val % (2^n) = x.val  (Nat level)
-- ============================================================================

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.val_mod_size (x : U8) : x.val % 256 = x.val := Nat.mod_eq_of_lt (by scalar_tac)
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.val_mod_size (x : U16) : x.val % 65536 = x.val := Nat.mod_eq_of_lt (by scalar_tac)
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.val_mod_size (x : U32) : x.val % 4294967296 = x.val := Nat.mod_eq_of_lt (by scalar_tac)
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.val_mod_size (x : U64) : x.val % 18446744073709551616 = x.val := Nat.mod_eq_of_lt (by scalar_tac)
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.val_mod_size (x : U128) : x.val % 340282366920938463463374607431768211456 = x.val := Nat.mod_eq_of_lt (by scalar_tac)

-- ============================================================================
-- x &&& 0 = 0  (scalar level)
-- ============================================================================

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.and_zero (x : U8) : x &&& 0#u8 = 0#u8 := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.and_zero (x : U16) : x &&& 0#u16 = 0#u16 := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.and_zero (x : U32) : x &&& 0#u32 = 0#u32 := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.and_zero (x : U64) : x &&& 0#u64 = 0#u64 := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.and_zero (x : U128) : x &&& 0#u128 = 0#u128 := by rw [UScalar.eq_equiv_bv_eq]; simp

-- 0 &&& x = 0
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.zero_and (x : U8) : 0#u8 &&& x = 0#u8 := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.zero_and (x : U16) : 0#u16 &&& x = 0#u16 := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.zero_and (x : U32) : 0#u32 &&& x = 0#u32 := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.zero_and (x : U64) : 0#u64 &&& x = 0#u64 := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.zero_and (x : U128) : 0#u128 &&& x = 0#u128 := by rw [UScalar.eq_equiv_bv_eq]; simp

-- ============================================================================
-- x ||| 0 = x  (scalar level)
-- ============================================================================

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.or_zero (x : U8) : x ||| 0#u8 = x := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.or_zero (x : U16) : x ||| 0#u16 = x := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.or_zero (x : U32) : x ||| 0#u32 = x := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.or_zero (x : U64) : x ||| 0#u64 = x := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.or_zero (x : U128) : x ||| 0#u128 = x := by rw [UScalar.eq_equiv_bv_eq]; simp

-- 0 ||| x = x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U8.zero_or (x : U8) : 0#u8 ||| x = x := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U16.zero_or (x : U16) : 0#u16 ||| x = x := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U32.zero_or (x : U32) : 0#u32 ||| x = x := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U64.zero_or (x : U64) : 0#u64 ||| x = x := by rw [UScalar.eq_equiv_bv_eq]; simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem U128.zero_or (x : U128) : 0#u128 ||| x = x := by rw [UScalar.eq_equiv_bv_eq]; simp

-- ============================================================================
-- a ^^^ b = 0 ↔ a = b  (scalar level)
-- ============================================================================

@[simp, simp_scalar_simps, grind =, agrind =]
theorem U8.xor_eq_zero_iff (a b : U8) : a ^^^ b = 0#u8 ↔ a = b := by bv_tac 8
@[simp, simp_scalar_simps, grind =, agrind =]
theorem U16.xor_eq_zero_iff (a b : U16) : a ^^^ b = 0#u16 ↔ a = b := by bv_tac 16
@[simp, simp_scalar_simps, grind =, agrind =]
theorem U32.xor_eq_zero_iff (a b : U32) : a ^^^ b = 0#u32 ↔ a = b := by bv_tac 32
@[simp, simp_scalar_simps, grind =, agrind =]
theorem U64.xor_eq_zero_iff (a b : U64) : a ^^^ b = 0#u64 ↔ a = b := by bv_tac 64
@[simp, simp_scalar_simps, grind =, agrind =]
theorem U128.xor_eq_zero_iff (a b : U128) : a ^^^ b = 0#u128 ↔ a = b := by bv_tac 128

-- ============================================================================
-- a ||| b = 0 ↔ a = 0 ∧ b = 0  (scalar level)
-- ============================================================================

@[simp, simp_scalar_simps, grind =, agrind =]
theorem U8.or_eq_zero_iff (a b : U8) : a ||| b = 0#u8 ↔ a = 0#u8 ∧ b = 0#u8 := by
  simp only [U8.eq_equiv_bv_eq, U8.ofNat_bv]; exact BitVec.or_eq_zero_iff
@[simp, simp_scalar_simps, grind =, agrind =]
theorem U16.or_eq_zero_iff (a b : U16) : a ||| b = 0#u16 ↔ a = 0#u16 ∧ b = 0#u16 := by
  simp only [U16.eq_equiv_bv_eq, U16.ofNat_bv]; exact BitVec.or_eq_zero_iff
@[simp, simp_scalar_simps, grind =, agrind =]
theorem U32.or_eq_zero_iff (a b : U32) : a ||| b = 0#u32 ↔ a = 0#u32 ∧ b = 0#u32 := by
  simp only [U32.eq_equiv_bv_eq, U32.ofNat_bv]; exact BitVec.or_eq_zero_iff
@[simp, simp_scalar_simps, grind =, agrind =]
theorem U64.or_eq_zero_iff (a b : U64) : a ||| b = 0#u64 ↔ a = 0#u64 ∧ b = 0#u64 := by
  simp only [U64.eq_equiv_bv_eq, U64.ofNat_bv]; exact BitVec.or_eq_zero_iff
@[simp, simp_scalar_simps, grind =, agrind =]
theorem U128.or_eq_zero_iff (a b : U128) : a ||| b = 0#u128 ↔ a = 0#u128 ∧ b = 0#u128 := by
  simp only [U128.eq_equiv_bv_eq, U128.ofNat_bv]; exact BitVec.or_eq_zero_iff

end Aeneas.Std
