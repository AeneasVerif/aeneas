import Aeneas.Std.Scalar.Core
import Aeneas.Tactic.Solver.ScalarTac
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
theorem IScalar.neg_imp_toNat_neg_eq_neg_toInt {ty} (x : IScalar ty) (hNeg : x.toInt < 0):
  (-x.toBitVec).toNat = -x.toBitVec.toInt := by
  have hmsb : x.toBitVec.msb = true := by
    have := @BitVec.msb_eq_toInt _ x.toBitVec
    simp only [toInt] at hNeg
    simp only [hNeg] at this
    apply this
  have hx := @BitVec.toInt_eq_msb_cond _ x.toBitVec
  simp [hmsb] at hx

  have hxNeg : x.toInt < 0 := by
    have := @BitVec.msb_eq_toInt _ x.toBitVec
    simp_all

  conv => lhs; simp only [Neg.neg, BitVec.neg]
  simp only [BitVec.toInt_eq_toNat_bmod]

  have hxToNatMod : (x.toBitVec.toNat : Int) % 2^ty.numBits = x.toBitVec.toNat := by
    apply Int.emod_eq_of_lt <;> omega

  have hPow : (2 ^ ty.numBits + 1 : Int) / 2  = 2^(ty.numBits - 1) := by
    have : ty.numBits = ty.numBits - 1 + 1 := by
      have := ty.numBits_nonzero
      omega
    conv => lhs; rw [this]
    rw [Int.pow_succ']
    rw [Int.add_ediv_of_dvd_left] <;> simp

  have : ¬ ((x.toBitVec.toNat : Int) % ↑(2 ^ ty.numBits : Nat) < (↑(2 ^ ty.numBits : Nat) + 1) / 2) := by
    have hIneq := @BitVec.msb_eq_toNat _ x.toBitVec
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
  have : (2 ^ ty.numBits - x.toBitVec.toNat : Nat) % (2 ^ ty.numBits : Int) =
         (2^ty.numBits - x.toBitVec.toNat : Nat) := by
    apply Int.emod_eq_of_lt
    . omega
    . have := x.hBounds
      simp only [toInt] at *
      have : (2 ^ ty.numBits - x.toBitVec.toNat : Nat) = (2 ^ ty.numBits - x.toBitVec.toNat : Int) := by
        have : (2 ^ ty.numBits : Nat) = (2 ^ ty.numBits : Int) := by simp
        omega
      rw [this]
      have : x.toBitVec.toNat > 0 := by
        by_contra
        have hxz : x.toBitVec.toNat = 0 := by omega
        have : x.toBitVec.toInt = 0 := by
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
  (∃ (a : UScalar ty), a.toNat = a'.toNat ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    cases a'
    simp_all only [toNat]
    have := @BitVec.toNat_injective ty.numBits
    have := this h
    simp [← this]
    apply hp
  . exists a'

@[simp] theorem IScalar.exists_eq_left {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), a.toInt = a'.toInt ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    cases a'
    simp_all only [toInt, eq_comm]
    rw [BitVec.toInt_inj] at h
    simp [h]
    apply hp
  . exists a'

@[simp] theorem UScalar.exists_eq_left' {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), a'.toNat = a.toNat ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    cases a'
    simp_all only [toNat]
    have := @BitVec.toNat_injective ty.numBits
    have := this h
    simp [this]
    apply hp
  . exists a'

@[simp] theorem IScalar.exists_eq_left' {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), a'.toInt = a.toInt ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    cases a'
    simp_all only [toInt]
    rw [BitVec.toInt_inj] at h
    simp [h]
    apply hp
  . exists a'

@[simp] theorem UScalar.exists_eq_right {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), p a ∧ a.toNat = a'.toNat) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    cases a'
    simp_all only [toNat]
    have := @BitVec.toNat_injective ty.numBits
    have := this h
    simp [← this]
    apply hp
  . exists a'

@[simp] theorem IScalar.exists_eq_right {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), p a ∧ a.toInt = a'.toInt) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    cases a'
    simp_all only [toInt, eq_comm]
    rw [BitVec.toInt_inj] at h
    simp [h]
    apply hp
  . exists a'

@[simp] theorem UScalar.exists_eq_right' {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), p a ∧ a'.toNat = a.toNat) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    cases a'
    simp_all only [toNat]
    have := @BitVec.toNat_injective ty.numBits
    have := this h
    simp [this]
    apply hp
  . exists a'

@[simp] theorem IScalar.exists_eq_right' {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), p a ∧ a'.toInt = a.toInt) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    cases a'
    simp_all only [toInt]
    rw [BitVec.toInt_inj] at h
    simp [h]
    apply hp
  . exists a'

@[simp] theorem UScalar.exists_eq {a' : UScalar ty} : ∃ (a : UScalar ty), a.toNat = a'.toNat := by exists a'
@[simp] theorem UScalar.exists_eq' {a' : UScalar ty} : ∃ (a : UScalar ty), a'.toNat = a.toNat := by exists a'
@[simp] theorem IScalar.exists_eq {a' : IScalar ty} : ∃ (a : IScalar ty), a.toInt = a'.toInt := by exists a'
@[simp] theorem IScalar.exists_eq' {a' : IScalar ty} : ∃ (a : IScalar ty), a'.toInt = a.toInt := by exists a'

/-!
# Equalities and simplification lemmas
-/

theorem UScalar.ofNatCore_toBitVec_lt_equiv {ty} (x y : Nat) (hx) (hy) :
  (@UScalar.ofNatCore ty x hx).toBitVec < (@UScalar.ofNatCore ty y hy).toBitVec ↔ x < y := by
  simp only [ofNatCore]
  have := Nat.mod_eq_of_lt hx
  have := Nat.mod_eq_of_lt hy
  simp only [BitVec.lt_ofFin, Fin.mk_lt_mk]

@[simp, scalar_tac_simps] theorem U8.toNat_mod_size_eq (x : U8) : x.toNat % U8.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U8.toNat_mod_size_eq' (x : U8) : x.toNat % 256 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U16.toNat_mod_size_eq (x : U16) : x.toNat % U16.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U16.toNat_mod_size_eq' (x : U16) : x.toNat % 65536 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U32.toNat_mod_size_eq (x : U32) : x.toNat % U32.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U32.toNat_mod_size_eq' (x : U32) : x.toNat % 4294967296 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U64.toNat_mod_size_eq (x : U64) : x.toNat % U64.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U64.toNat_mod_size_eq' (x : U64) : x.toNat % 18446744073709551616 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U128.toNat_mod_size_eq (x : U128) : x.toNat % U128.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U128.toNat_mod_size_eq' (x : U128) : x.toNat % 340282366920938463463374607431768211456 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem Usize.toNat_mod_size_eq (x : Usize) : x.toNat % Usize.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U8.toNat_mod_max_eq (x : U8) : x.toNat % (U8.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U16.toNat_mod_max_eq (x : U16) : x.toNat % (U16.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U32.toNat_mod_max_eq (x : U32) : x.toNat % (U32.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U64.toNat_mod_max_eq (x : U64) : x.toNat % (U64.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U128.toNat_mod_max_eq (x : U128) : x.toNat % (U128.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem Usize.toNat_mod_max_eq (x : Usize) : x.toNat % (Usize.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem I8.toInt_mod_size_eq (x : I8) : Int.bmod x.toInt I8.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I8.toInt_mod_size_eq' (x : I8) : Int.bmod x.toInt 256 = x.toInt := by
  have := toInt_mod_size_eq x; simp [size, numBits] at this; assumption

@[simp, scalar_tac_simps] theorem I16.toInt_mod_size_eq (x : I16) : Int.bmod x.toInt I16.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I16.toInt_mod_size_eq' (x : I16) : Int.bmod x.toInt 65536 = x.toInt := by
  have := toInt_mod_size_eq x; simp [size, numBits] at this; assumption

@[simp, scalar_tac_simps] theorem I32.toInt_mod_size_eq (x : I32) : Int.bmod x.toInt I32.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I32.toInt_mod_size_eq' (x : I32) : Int.bmod x.toInt 4294967296 = x.toInt := by
  have := toInt_mod_size_eq x; simp [size, numBits] at this; assumption

@[simp, scalar_tac_simps] theorem I64.toInt_mod_size_eq (x : I64) : Int.bmod x.toInt I64.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I64.toInt_mod_size_eq' (x : I64) : Int.bmod x.toInt 18446744073709551616 = x.toInt := by
  have := toInt_mod_size_eq x; simp [size, numBits] at this; assumption

@[simp, scalar_tac_simps] theorem I128.toInt_mod_size_eq (x : I128) : Int.bmod x.toInt I128.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I128.toInt_mod_size_eq' (x : I128) : Int.bmod x.toInt 340282366920938463463374607431768211456 = x.toInt := by
  have := toInt_mod_size_eq x; simp [size, numBits] at this; assumption

@[simp, scalar_tac_simps] theorem Isize.toInt_mod_size_eq (x : Isize) : Int.bmod x.toInt Isize.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> try scalar_tac
  simp [numBits]; cases System.Platform.numBits_eq <;> simp [*]

@[simp] theorem U8.toNat_max_zero_eq (x : U8) : x.toNat ⊔ 0 = x.toNat := by scalar_tac
@[simp] theorem U16.toNat_max_zero_eq (x : U16) : x.toNat ⊔ 0 = x.toNat := by scalar_tac
@[simp] theorem U32.toNat_max_zero_eq (x : U32) : x.toNat ⊔ 0 = x.toNat := by scalar_tac
@[simp] theorem U64.toNat_max_zero_eq (x : U64) : x.toNat ⊔ 0 = x.toNat := by scalar_tac
@[simp] theorem U128.toNat_max_zero_eq (x : U128) : x.toNat ⊔ 0 = x.toNat := by scalar_tac
@[simp] theorem Usize.toNat_max_zero_eq (x : Usize) : x.toNat ⊔ 0 = x.toNat := by scalar_tac


end Aeneas.Std
