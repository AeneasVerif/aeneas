import Aeneas.Std.Scalar.Core
import Aeneas.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith


/-!
# Casts: Definitions

The reference semantics are here: https://doc.rust-lang.org/reference/expressions/operator-expr.html#semantics
-/

/-- When casting between unsigned integers, we truncate or **zero**-extend the integer. -/
@[progress_pure_def]
def UScalar.cast {src_ty : UScalarTy} (tgt_ty : UScalarTy) (x : UScalar src_ty) : UScalar tgt_ty :=
  -- This truncates the integer if the numBits is smaller
  ⟨ x.bv.zeroExtend tgt_ty.numBits ⟩

/- Heterogeneous cast

   When casting from an unsigned integer to a signed integer, we truncate or **zero**-extend.
-/
@[progress_pure_def]
def UScalar.hcast {src_ty : UScalarTy} (tgt_ty : IScalarTy) (x : UScalar src_ty) : IScalar tgt_ty :=
  -- This truncates the integer if the numBits is smaller
  ⟨ x.bv.zeroExtend tgt_ty.numBits ⟩

/-- When casting between signed integers, we truncate or **sign**-extend. -/
@[progress_pure_def]
def IScalar.cast {src_ty : IScalarTy} (tgt_ty : IScalarTy) (x : IScalar src_ty) : IScalar tgt_ty :=
  ⟨ x.bv.signExtend tgt_ty.numBits ⟩

/- Heterogeneous cast

   When casting from a signed integer to a unsigned integer, we truncate or **sign**-extend.
-/
@[progress_pure_def]
def IScalar.hcast {src_ty : IScalarTy} (tgt_ty : UScalarTy) (x : IScalar src_ty) : UScalar tgt_ty :=
  ⟨ x.bv.signExtend tgt_ty.numBits ⟩

section
    /-! Checking that the semantics of casts are correct by using the examples given by the Rust reference. -/

  private def check_cast_i_to_u (src : Int) (src_ty : IScalarTy) (tgt : Nat) (tgt_ty : UScalarTy)
    (hSrc : IScalar.cMin src_ty ≤ src ∧ src ≤ IScalar.cMax src_ty := by decide)
    (hTgt : tgt ≤ UScalar.cMax tgt_ty := by decide): Bool :=
    IScalar.hcast tgt_ty (@IScalar.ofInt src_ty src hSrc) = @UScalar.ofNat tgt_ty tgt hTgt

  private def check_cast_u_to_i (src : Nat) (src_ty : UScalarTy) (tgt : Int) (tgt_ty : IScalarTy)
    (hSrc : src ≤ UScalar.cMax src_ty := by decide)
    (hTgt : IScalar.cMin tgt_ty ≤ tgt ∧ tgt ≤ IScalar.cMax tgt_ty := by decide) : Bool :=
    UScalar.hcast tgt_ty (@UScalar.ofNat src_ty src hSrc) = @IScalar.ofInt tgt_ty tgt hTgt

  private def check_cast_u_to_u (src : Nat) (src_ty : UScalarTy) (tgt : Nat) (tgt_ty : UScalarTy)
    (hSrc : src ≤ UScalar.cMax src_ty := by decide)
    (hTgt : tgt ≤ UScalar.cMax tgt_ty := by decide) : Bool :=
    UScalar.cast tgt_ty (@UScalar.ofNat src_ty src hSrc) = @UScalar.ofNat tgt_ty tgt hTgt

  private def check_cast_i_to_i (src : Int) (src_ty : IScalarTy) (tgt : Int) (tgt_ty : IScalarTy)
    (hSrc : IScalar.cMin src_ty ≤ src ∧ src ≤ IScalar.cMax src_ty := by decide)
    (hTgt : IScalar.cMin tgt_ty ≤ tgt ∧ tgt ≤ IScalar.cMax tgt_ty := by decide) : Bool :=
    IScalar.cast tgt_ty (@IScalar.ofInt src_ty src hSrc) = @IScalar.ofInt tgt_ty tgt hTgt

  local macro:max x:term:max noWs "i8" : term => `(I8.ofInt $x (by decide))
  local macro:max x:term:max noWs "i16" : term => `(I16.ofInt $x (by decide))
  local macro:max x:term:max noWs "i32" : term => `(I32.ofInt $x (by decide))
  local macro:max x:term:max noWs "u8" : term => `(U8.ofNat $x (by decide))
  local macro:max x:term:max noWs "u16" : term => `(U16.ofNat $x (by decide))

  /- Cast between integers of same size -/
  #assert IScalar.hcast _ 42i8    = 42u8       -- assert_eq!(42i8 as u8, 42u8);
  #assert IScalar.hcast _ (-1)i8  = 255u8      -- assert_eq!(-1i8 as u8, 255u8);
  #assert UScalar.hcast _ 255u8   = (-1)i8     -- assert_eq!(255u8 as i8, -1i8);
  #assert IScalar.hcast _ (-1)i16 = 65535u16   -- assert_eq!(-1i16 as u16, 65535u16);

  /- Cast from larger integer to smaller integer -/
  #assert UScalar.cast _ 42u16 = 42u8         -- assert_eq!(42u16 as u8, 42u8);
  #assert UScalar.cast _ 1234u16 = 210u8      -- assert_eq!(1234u16 as u8, 210u8);
  #assert UScalar.cast _ 0xabcdu16 = 0xcdu8   -- assert_eq!(0xabcdu16 as u8, 0xcdu8);

  #assert IScalar.cast _ (-42)i16 = (-42)i8   -- assert_eq!(-42i16 as i8, -42i8);
  #assert UScalar.hcast _ 1234u16 = (-46)i8   -- assert_eq!(1234u16 as i8, -46i8);
  #assert IScalar.cast _ 0xabcdi32 = (-51)i8  -- assert_eq!(0xabcdi32 as i8, -51i8);

  /- Cast from a smaller integer to a larger integer -/
  #assert IScalar.cast _ 42i8 = 42i16 -- assert_eq!(42i8 as i16, 42i16);
  #assert IScalar.cast _ (-17)i8 = (-17)i16 -- assert_eq!(-17i8 as i16, -17i16);
  #assert UScalar.cast _ 0b1000_1010u8 = 0b0000_0000_1000_1010u16 -- assert_eq!(0b1000_1010u8 as u16, 0b0000_0000_1000_1010u16, "Zero-extend");
  #assert IScalar.cast _ 0b0000_1010i8 = 0b0000_0000_0000_1010i16 -- assert_eq!(0b0000_1010i8 as i16, 0b0000_0000_0000_1010i16, "Sign-extend 0");
  #assert (IScalar.cast .I16 (UScalar.hcast .I8 0b1000_1010u8)) = UScalar.hcast .I16 0b1111_1111_1000_1010u16 -- assert_eq!(0b1000_1010u8 as i8 as i16, 0b1111_1111_1000_1010u16 as i16, "Sign-extend 1");

end

def UScalar.cast_fromBool (ty : UScalarTy) (x : Bool) : UScalar ty :=
  if x then ⟨ 1#ty.numBits ⟩ else ⟨ 0#ty.numBits ⟩

def IScalar.cast_fromBool (ty : IScalarTy) (x : Bool) : IScalar ty :=
  if x then ⟨ 1#ty.numBits ⟩ else ⟨ 0#ty.numBits ⟩

/-!
# Casts: Theorems
-/

/-- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
theorem UScalar.cast_inBounds_spec {src_ty : UScalarTy}
  (tgt_ty : UScalarTy) (x : UScalar src_ty) (h : x.val ≤ UScalar.max tgt_ty) :
  ∃ y, toResult (UScalar.cast tgt_ty x) = ok y ∧
  y.val = x.val := by
  simp only [toResult, cast, BitVec.truncate_eq_setWidth, ok.injEq, exists_eq_left', UScalar.val]
  simp only [max, BitVec.toNat_setWidth, bv_toNat] at *
  have : 0 < 2^tgt_ty.numBits := by simp
  apply Nat.mod_eq_of_lt; omega

/-- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
def UScalar.hcast_inBounds_spec {src_ty : UScalarTy}
  (tgt_ty : IScalarTy) (x : UScalar src_ty)
  (h : x.val ≤ IScalar.max tgt_ty) :
  ∃ y, toResult (UScalar.hcast tgt_ty x) = ok y ∧
  y.val = x.val := by
  simp [toResult, hcast]
  simp only [IScalar.val, UScalar.val]
  simp [IScalar.max] at *
  apply Int.bmod_pow2_eq_of_inBounds'
  . apply IScalarTy.numBits_nonzero
  . have : -2 ^ (tgt_ty.numBits - 1) ≤ 0 := by simp
    scalar_tac
  . scalar_tac

/-- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
def IScalar.cast_inBounds_spec {src_ty : IScalarTy}
  (tgt_ty : IScalarTy) (x : IScalar src_ty) (h : IScalar.min tgt_ty ≤ x.val ∧ x.val ≤ IScalar.max tgt_ty) :
  ∃ y, toResult (IScalar.cast tgt_ty x) = ok y ∧
  y.val = x.val
  := by
  simp only [toResult, cast, BitVec.signExtend, bv_toInt_eq, ok.injEq, exists_eq_left']
  simp only [IScalar.val]
  simp only [min, max, bv_toInt_eq, BitVec.toInt_ofInt] at *
  apply Int.bmod_pow2_eq_of_inBounds'
  . apply IScalarTy.numBits_nonzero
  . scalar_tac
  . scalar_tac

/-- This theorem allows us not to use bit-vectors when reasoning about casts, if there are no overflows -/
def IScalar.hcast_inBounds_spec {src_ty : IScalarTy}
  (tgt_ty : UScalarTy) (x : IScalar src_ty) (h : 0 ≤ x.val ∧ x.val ≤ UScalar.max tgt_ty) :
  ∃ y, toResult (IScalar.hcast tgt_ty x) = ok y ∧
  y.val = x.val := by
  simp [toResult, hcast, BitVec.signExtend, bv_toInt_eq, ok.injEq, exists_eq_left']
  simp only [IScalar.val, UScalar.val]
  simp only [UScalar.max, Nat.ofNat_pos, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat,
    bv_toInt_eq, BitVec.toNat_ofInt, Int.ofNat_toNat] at *
  have : 0 < 2^tgt_ty.numBits := by simp
  have : x.val % 2^tgt_ty.numBits = x.val := by apply Int.emod_eq_of_lt <;> scalar_tac
  simp only [this, sup_eq_left, ge_iff_le]
  scalar_tac

@[simp, progress_pure cast_fromBool ty b]
theorem UScalar.cast_fromBool_val_eq ty (b : Bool) : (UScalar.cast_fromBool ty b).val = b.toNat := by
  simp only [cast_fromBool]
  split <;> simp only [val, *] <;> simp
  have := ty.numBits_nonzero
  omega

@[simp, progress_pure cast_fromBool ty b]
theorem IScalar.cast_fromBool_val_eq ty (b : Bool) :(IScalar.cast_fromBool ty b).val = b.toInt := by
  simp only [cast_fromBool]
  split <;> simp only [val, *] <;> simp
  cases ty <;> simp [BitVec.toInt]
  have := System.Platform.numBits_eq
  cases this <;>
  rename_i h <;>
  rw [h] <;> simp

@[scalar_tac UScalar.cast_fromBool ty b]
theorem UScalar.cast_fromBool_bound_eq ty (b : Bool) : (UScalar.cast_fromBool ty b).val ≤ 1 := by
  simp only [cast_fromBool]
  split <;> simp only [val] <;> simp
  have := @Nat.mod_eq_of_lt 1 (2^ty.numBits) (by simp [ty.numBits_nonzero])
  rw [this]

@[simp]
theorem UScalar.cast_fromBool_bv_eq ty (b : Bool) : (UScalar.cast_fromBool ty b).bv = (BitVec.ofBool b).zeroExtend _ := by
  simp only [cast_fromBool, BitVec.truncate_eq_setWidth]
  cases b <;> simp
  apply @BitVec.toNat_injective ty.numBits
  simp

@[simp]
theorem IScalar.cast_fromBool_bv_eq ty (b : Bool) :(IScalar.cast_fromBool ty b).bv = (BitVec.ofBool b).zeroExtend _ := by
  simp only [cast_fromBool, BitVec.truncate_eq_setWidth]
  cases b <;> simp
  apply @BitVec.toNat_injective ty.numBits
  simp

@[scalar_tac IScalar.cast_fromBool ty b]
theorem IScalar.cast_fromBool_bound_eq ty (b : Bool) :
  0 ≤ (IScalar.cast_fromBool ty b).val ∧ (IScalar.cast_fromBool ty b).val ≤ 1 := by
  simp only [cast_fromBool]
  split <;> simp only [val]
  . have : (1#ty.numBits).toInt  = 1 := by
      simp [BitVec.toInt]
      cases ty <;> simp
      cases System.Platform.numBits_eq <;> simp [*]
    simp [this]
  . simp

theorem UScalar.cast_val_eq {src_ty : UScalarTy} (tgt_ty : UScalarTy) (x : UScalar src_ty) :
  (cast tgt_ty x).val = x.val % 2^(tgt_ty.numBits) := by
  simp only [cast, val]
  simp

-- TODO: factor our the casts

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U8.cast_U16_val_eq (x : U8) : (UScalar.cast .U16 x).val = x.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U8.cast_U32_val_eq (x : U8) : (UScalar.cast .U32 x).val = x.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U8.cast_U64_val_eq (x : U8) : (UScalar.cast .U64 x).val = x.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U8.cast_U128_val_eq (x : U8) : (UScalar.cast .U128 x).val = x.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U8.cast_Usize_val_eq (x : U8) : (UScalar.cast .Usize x).val = x.val := by
  simp [UScalar.cast_val_eq]; cases System.Platform.numBits_eq <;> simp [*] <;> scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U16.cast_U32_val_eq (x : U16) : (UScalar.cast .U32 x).val = x.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U16.cast_U64_val_eq (x : U16) : (UScalar.cast .U64 x).val = x.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U16.cast_U128_val_eq (x : U16) : (UScalar.cast .U128 x).val = x.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U16.cast_Usize_val_eq (x : U16) : (UScalar.cast .Usize x).val = x.val := by
  simp [UScalar.cast_val_eq]; cases System.Platform.numBits_eq <;> simp [*] <;> scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U32.cast_U64_val_eq (x : U32) : (UScalar.cast .U64 x).val = x.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U32.cast_U128_val_eq (x : U32) : (UScalar.cast .U128 x).val = x.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U32.cast_Usize_val_eq (x : U32) : (UScalar.cast .Usize x).val = x.val := by
  simp [UScalar.cast_val_eq]; cases System.Platform.numBits_eq <;> simp [*] <;> scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem U64.cast_U128_val_eq (x : U64) : (UScalar.cast .U128 x).val = x.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

@[simp, scalar_tac_simps, simp_scalar_simps]
theorem UScalar.cast_val_mod_pow_greater_numBits_eq {src_ty : UScalarTy} (tgt_ty : UScalarTy) (x : UScalar src_ty) (h : src_ty.numBits ≤ tgt_ty.numBits) :
  (cast tgt_ty x).val = x.val := by
  simp [UScalar.cast_val_eq]
  have hBounds := x.hBounds
  apply Nat.mod_eq_of_lt
  have : 0 < 2^src_ty.numBits := by simp
  have := @Nat.pow_le_pow_right 2 (by simp) src_ty.numBits tgt_ty.numBits (by omega)
  omega

@[simp]
theorem UScalar.cast_val_mod_pow_of_inBounds_eq {src_ty : UScalarTy} (tgt_ty : UScalarTy) (x : UScalar src_ty) (h : x.val < 2^tgt_ty.numBits) :
  (cast tgt_ty x).val = x.val := by
  simp [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  assumption

@[simp]
theorem UScalar.cast_bv_eq {src_ty : UScalarTy} (tgt_ty : UScalarTy) (x : UScalar src_ty) :
  (cast tgt_ty x).bv = x.bv.setWidth tgt_ty.numBits := by
  simp [UScalar.cast]

example (x : U16) : (x.cast .U32).val = x.val := by simp
example : ((U32.ofNat 42).cast .U16).val = 42 := by simp

theorem IScalar.cast_val_eq {src_ty : IScalarTy} (tgt_ty : IScalarTy) (x : IScalar src_ty) :
  (cast tgt_ty x).val = Int.bmod x.val (2^(Min.min tgt_ty.numBits src_ty.numBits)) := by
  simp only [cast, val]
  simp only [BitVec.toInt_signExtend]

@[simp]
theorem IScalar.val_mod_pow_greater_numBits {src_ty : IScalarTy} (tgt_ty : IScalarTy) (x : IScalar src_ty) (h : src_ty.numBits ≤ tgt_ty.numBits) :
  (cast tgt_ty x).val = x.val := by
  simp [IScalar.cast_val_eq]
  have hBounds := x.hBounds
  simp [h]
  have := src_ty.numBits_nonzero
  have : src_ty.numBits = src_ty.numBits - 1 + 1 := by omega
  rw [this]
  apply Int.bmod_pow2_eq_of_inBounds <;> omega

@[simp]
theorem IScalar.val_mod_pow_inBounds {src_ty : IScalarTy} (tgt_ty : IScalarTy) (x : IScalar src_ty)
  (hMin : -2^(tgt_ty.numBits - 1) ≤ x.val) (hMax : x.val < 2^(tgt_ty.numBits - 1)) :
  (cast tgt_ty x).val = x.val := by
  simp [IScalar.cast_val_eq]
  have hBounds := x.hBounds
  have := src_ty.numBits_nonzero
  have := tgt_ty.numBits_nonzero
  have : tgt_ty.numBits ⊓ src_ty.numBits = tgt_ty.numBits ⊓ src_ty.numBits - 1 + 1 := by omega
  rw [this]
  have : -2 ^ (tgt_ty.numBits ⊓ src_ty.numBits - 1) ≤ x.val ∧
         x.val < 2 ^ (tgt_ty.numBits ⊓ src_ty.numBits - 1) := by
    have : tgt_ty.numBits ⊓ src_ty.numBits = tgt_ty.numBits ∨ tgt_ty.numBits ⊓ src_ty.numBits = src_ty.numBits := by
      rw [Nat.min_def]
      split <;> simp
    cases this <;> rename_i hEq <;> simp [hEq] <;> omega
  apply Int.bmod_pow2_eq_of_inBounds <;> omega


end Aeneas.Std
