import Aeneas.Std.Scalar.Core
import Aeneas.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith

/-- Important theorem to reason with `Int.bmod` in the proofs about `IScalar` -/
theorem bmod_pow_numBits_eq_of_lt (ty : IScalarTy) (x : Int)
  (h0 : - 2 ^ (ty.numBits-1) ≤ x) (h1 : x < 2 ^ (ty.numBits -1)) :
  Int.bmod x (2^ty.numBits) = x := by
  have := ty.numBits_nonzero
  have hEq : ty.numBits - 1 + 1 = ty.numBits := by omega
  have := Int.bmod_pow2_eq_of_inBounds (ty.numBits-1) x (by omega) (by omega)
  simp [hEq] at this
  apply this

/-- We need this lemma to prove the theorems about division and remainder -/
theorem IScalar.neg_imp_toNat_neg_eq_neg_toInt {ty} (x : IScalar ty) (hNeg : x.val < 0):
  (-x.bv).toNat = -x.bv.toInt := by
  have hmsb : x.bv.msb = true := by
    have := @BitVec.msb_eq_toInt _ x.bv
    simp only [val] at hNeg
    simp only [hNeg] at this
    apply this
  have hx := @BitVec.toInt_eq_msb_cond _ x.bv
  simp [hmsb] at hx

  have hxNeg : x.val < 0 := by
    have := @BitVec.msb_eq_toInt _ x.bv
    simp_all

  conv => lhs; simp only [Neg.neg, BitVec.neg]
  simp only [BitVec.toInt_eq_toNat_bmod]

  have hxToNatMod : (x.bv.toNat : Int) % 2^ty.numBits = x.bv.toNat := by
    apply Int.emod_eq_of_lt <;> omega

  have hPow : (2 ^ ty.numBits + 1 : Int) / 2  = 2^(ty.numBits - 1) := by
    have : ty.numBits = ty.numBits - 1 + 1 := by
      have := ty.numBits_nonzero
      omega
    conv => lhs; rw [this]
    rw [Int.pow_succ']
    rw [Int.add_ediv_of_dvd_left] <;> simp

  have : ¬ ((x.bv.toNat : Int) % ↑(2 ^ ty.numBits : Nat) < (↑(2 ^ ty.numBits : Nat) + 1) / 2) := by
    have hIneq := @BitVec.msb_eq_toNat _ x.bv
    rw [hmsb] at hIneq
    simp at hIneq
    simp
    rw [hPow]

    rw [hxToNatMod]
    zify at hIneq
    omega
  rw [Int.bmod_def]
  simp only [this]
  simp
  have : (2 ^ ty.numBits - x.bv.toNat : Nat) % (2 ^ ty.numBits : Int) =
         (2^ty.numBits - x.bv.toNat : Nat) := by
    apply Int.emod_eq_of_lt
    . omega
    . have := x.hBounds
      simp only [val] at *
      have : (2 ^ ty.numBits - x.bv.toNat : Nat) = (2 ^ ty.numBits - x.bv.toNat : Int) := by
        have : (2 ^ ty.numBits : Nat) = (2 ^ ty.numBits : Int) := by simp
        omega
      rw [this]
      have : x.bv.toNat > 0 := by
        by_contra
        have hxz : x.bv.toNat = 0 := by omega
        have : x.bv.toInt = 0 := by
          simp only [BitVec.toInt_eq_toNat_bmod, Int.bmod_def, hxz]
          simp [hPow]
        omega
      omega
  rw [this]; clear this
  rw [hxToNatMod]

  have : (2 ^ ty.numBits : Nat) = (2 ^ ty.numBits : Int) := by simp
  omega

/-!
# Misc Theorems
-/

@[simp] theorem UScalar.exists_eq_left {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), a.val = a'.val ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    cases a'
    simp_all only [val]
    have := @BitVec.toNat_injective ty.numBits
    have := this h
    simp [← this]
    apply hp
  . exists a'

@[simp] theorem IScalar.exists_eq_left {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), a.val = a'.val ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    cases a'
    simp_all only [val, eq_comm]
    rw [BitVec.toInt_inj] at h
    simp [h]
    apply hp
  . exists a'

@[simp] theorem UScalar.exists_eq_left' {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), a'.val = a.val ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    cases a'
    simp_all only [val]
    have := @BitVec.toNat_injective ty.numBits
    have := this h
    simp [this]
    apply hp
  . exists a'

@[simp] theorem IScalar.exists_eq_left' {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), a'.val = a.val ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    cases a'
    simp_all only [val]
    rw [BitVec.toInt_inj] at h
    simp [h]
    apply hp
  . exists a'

@[simp] theorem UScalar.exists_eq_right {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), p a ∧ a.val = a'.val) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    cases a'
    simp_all only [val]
    have := @BitVec.toNat_injective ty.numBits
    have := this h
    simp [← this]
    apply hp
  . exists a'

@[simp] theorem IScalar.exists_eq_right {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), p a ∧ a.val = a'.val) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    cases a'
    simp_all only [val, eq_comm]
    rw [BitVec.toInt_inj] at h
    simp [h]
    apply hp
  . exists a'

@[simp] theorem UScalar.exists_eq_right' {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), p a ∧ a'.val = a.val) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    cases a'
    simp_all only [val]
    have := @BitVec.toNat_injective ty.numBits
    have := this h
    simp [this]
    apply hp
  . exists a'

@[simp] theorem IScalar.exists_eq_right' {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), p a ∧ a'.val = a.val) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    cases a'
    simp_all only [val]
    rw [BitVec.toInt_inj] at h
    simp [h]
    apply hp
  . exists a'

@[simp] theorem UScalar.exists_eq {a' : UScalar ty} : ∃ (a : UScalar ty), a.val = a'.val := by exists a'
@[simp] theorem UScalar.exists_eq' {a' : UScalar ty} : ∃ (a : UScalar ty), a'.val = a.val := by exists a'
@[simp] theorem IScalar.exists_eq {a' : IScalar ty} : ∃ (a : IScalar ty), a.val = a'.val := by exists a'
@[simp] theorem IScalar.exists_eq' {a' : IScalar ty} : ∃ (a : IScalar ty), a'.val = a.val := by exists a'

/-!
# Equalities and simplification lemmas
-/

theorem UScalar.ofNatCore_bv_lt_equiv {ty} (x y : Nat) (hx) (hy) :
  (@UScalar.ofNatCore ty x hx).bv < (@UScalar.ofNatCore ty y hy).bv ↔ x < y := by
  simp only [ofNatCore]
  have := Nat.mod_eq_of_lt hx
  have := Nat.mod_eq_of_lt hy
  simp only [BitVec.lt_ofFin, Fin.mk_lt_mk]

@[simp, scalar_tac_simps] theorem U8.val_mod_size_eq (x : U8) : x.val % U8.size = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U8.val_mod_size_eq' (x : U8) : x.val % 256 = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U16.val_mod_size_eq (x : U16) : x.val % U16.size = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U16.val_mod_size_eq' (x : U16) : x.val % 65536 = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U32.val_mod_size_eq (x : U32) : x.val % U32.size = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U32.val_mod_size_eq' (x : U32) : x.val % 4294967296 = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U64.val_mod_size_eq (x : U64) : x.val % U64.size = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U64.val_mod_size_eq' (x : U64) : x.val % 18446744073709551616 = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U128.val_mod_size_eq (x : U128) : x.val % U128.size = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U128.val_mod_size_eq' (x : U128) : x.val % 340282366920938463463374607431768211456 = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem Usize.val_mod_size_eq (x : Usize) : x.val % Usize.size = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U8.val_mod_max_eq (x : U8) : x.val % (U8.max + 1) = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U16.val_mod_max_eq (x : U16) : x.val % (U16.max + 1) = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U32.val_mod_max_eq (x : U32) : x.val % (U32.max + 1) = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U64.val_mod_max_eq (x : U64) : x.val % (U64.max + 1) = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U128.val_mod_max_eq (x : U128) : x.val % (U128.max + 1) = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem Usize.val_mod_max_eq (x : Usize) : x.val % (Usize.max + 1) = x.val := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem I8.val_mod_size_eq (x : I8) : Int.bmod x.val I8.size = x.val := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I8.val_mod_size_eq' (x : I8) : Int.bmod x.val 256 = x.val := by
  have := val_mod_size_eq x; simp [size, numBits] at this; assumption

@[simp, scalar_tac_simps] theorem I16.val_mod_size_eq (x : I16) : Int.bmod x.val I16.size = x.val := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I16.val_mod_size_eq' (x : I16) : Int.bmod x.val 65536 = x.val := by
  have := val_mod_size_eq x; simp [size, numBits] at this; assumption

@[simp, scalar_tac_simps] theorem I32.val_mod_size_eq (x : I32) : Int.bmod x.val I32.size = x.val := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I32.val_mod_size_eq' (x : I32) : Int.bmod x.val 4294967296 = x.val := by
  have := val_mod_size_eq x; simp [size, numBits] at this; assumption

@[simp, scalar_tac_simps] theorem I64.val_mod_size_eq (x : I64) : Int.bmod x.val I64.size = x.val := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I64.val_mod_size_eq' (x : I64) : Int.bmod x.val 18446744073709551616 = x.val := by
  have := val_mod_size_eq x; simp [size, numBits] at this; assumption

@[simp, scalar_tac_simps] theorem I128.val_mod_size_eq (x : I128) : Int.bmod x.val I128.size = x.val := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I128.val_mod_size_eq' (x : I128) : Int.bmod x.val 340282366920938463463374607431768211456 = x.val := by
  have := val_mod_size_eq x; simp [size, numBits] at this; assumption

@[simp, scalar_tac_simps] theorem Isize.val_mod_size_eq (x : Isize) : Int.bmod x.val Isize.size = x.val := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> try scalar_tac
  simp [numBits]; cases System.Platform.numBits_eq <;> simp [*]

@[simp] theorem U8.val_max_zero_eq (x : U8) : x.val ⊔ 0 = x.val := by scalar_tac
@[simp] theorem U16.val_max_zero_eq (x : U16) : x.val ⊔ 0 = x.val := by scalar_tac
@[simp] theorem U32.val_max_zero_eq (x : U32) : x.val ⊔ 0 = x.val := by scalar_tac
@[simp] theorem U64.val_max_zero_eq (x : U64) : x.val ⊔ 0 = x.val := by scalar_tac
@[simp] theorem U128.val_max_zero_eq (x : U128) : x.val ⊔ 0 = x.val := by scalar_tac
@[simp] theorem Usize.val_max_zero_eq (x : Usize) : x.val ⊔ 0 = x.val := by scalar_tac


end Aeneas.Std
