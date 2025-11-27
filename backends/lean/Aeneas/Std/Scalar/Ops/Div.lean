import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Division: Definitions
-/

def UScalar.div {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if y.bv != 0 then ok ⟨ BitVec.udiv x.bv y.bv ⟩ else fail divisionByZero

def IScalar.div {ty : IScalarTy} (x y : IScalar ty): Result (IScalar ty) :=
  if y.val != 0 then
    -- There can be an overflow if `x` is equal to the lower bound and `y` to `-1`
    if ¬ (x.val = IScalar.min ty && y.val = -1) then ok ⟨ BitVec.sdiv x.bv y.bv ⟩
    else fail integerOverflow
  else fail divisionByZero

def UScalar.try_div {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (div x y)

def IScalar.try_div {ty : IScalarTy} (x y : IScalar ty): Option (IScalar ty) :=
  Option.ofResult (div x y)

instance {ty} : HDiv (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hDiv x y := UScalar.div x y

instance {ty} : HDiv (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hDiv x y := IScalar.div x y

/-!
# Sanity Checks
-/
/-!
The scalar division/modulo on signed machine integers 't'runcates towards 0, meaning it is
implemented by the `Int.tdiv`, `Int.tmod`, etc. definitions.
-/

namespace Tests
  -- Checking that the division over signed integers agrees with Rust
  #assert Int.tdiv 3 2 = 1
  #assert Int.tdiv (-3) 2 = -1
  #assert Int.tdiv 3 (-2) = -1
  #assert Int.tdiv (-3) (-2) = 1
  #assert Int.tdiv 7 3 = 2
  #assert Int.tdiv (-7) 3 = -2
  #assert Int.tdiv 7 (-3) = -2
  #assert Int.tdiv (-7) (-3) = 2

  -- Checking that the signed division over bit-vectors agrees with Rust
  private def bv_sdiv (x y : Int) : Int :=
    (BitVec.sdiv (BitVec.ofInt 32 x) (BitVec.ofInt 32 y)).toInt

  #assert bv_sdiv 3 2 = 1
  #assert bv_sdiv (-3) 2 = -1
  #assert bv_sdiv 3 (-2) = -1
  #assert bv_sdiv (-3) (-2) = 1
  #assert bv_sdiv 7 3 = 2
  #assert bv_sdiv (-7) 3 = -2
  #assert bv_sdiv 7 (-3) = -2
  #assert bv_sdiv (-7) (-3) = 2
end Tests

/-!
# Division: Theorems
-/

/-!
Theorems with a specification which use integers and bit-vectors
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.div_bv_spec {ty} (x : UScalar ty) {y : UScalar ty}
  (hzero : y.val ≠ 0) :
  ∃ z, x / y = ok z ∧ (↑z : Nat) = ↑x / ↑y ∧ z.bv = x.bv / y.bv := by
  have hzero' : y.bv ≠ 0#ty.numBits := by
    intro h
    zify at h
    simp_all
  conv => congr; ext; lhs; simp [HDiv.hDiv]
  simp [hzero', div]
  simp only [val]
  simp

theorem Int.bmod_pow2_IScalarTy_numBits_minus_one (ty : IScalarTy) :
  Int.bmod (2 ^ (ty.numBits - 1)) (2 ^ ty.numBits) = - 2 ^ (ty.numBits - 1) := by
  rw [Int.bmod]
  /- Just doing a case disjunction on the number of bits because
     those proofs are annoying -/
  cases ty <;> simp
  have := System.Platform.numBits_eq
  cases this <;> simp [*]

theorem IScalar.neg_imp_neg_val_toNat_mod_pow_eq_neg_val {ty} (x : IScalar ty)
  (hNeg : x.bv.toInt < 0) :
  ((-x.val).toNat : Int) % 2^ty.numBits = -(x.val : Int) := by
  have hmsb : x.bv.msb = true := by
    have := @BitVec.msb_eq_toInt _ x.bv
    simp only [hNeg] at this
    apply this
  have hx := @BitVec.toInt_eq_msb_cond _ x.bv
  simp [hmsb] at hx
  have hBounds := x.hBounds
  have pow2Ineq : (2^(ty.numBits - 1) : Int) < 2^ty.numBits := by
    have := ty.numBits_nonzero
    have : (0 : Int) < 2^(ty.numBits - 1) := by simp
    have : ty.numBits = ty.numBits - 1 + 1 := by omega
    conv => rhs; rw [this]
    rw [Int.pow_succ']
    omega
  have hyToNat : 2 ^ ty.numBits - x.bv.toNat = (-x.val).toNat := by
    rw [hx]
    simp
    norm_cast
  have hyValToNatMod : ((-x.val).toNat : Nat) % 2^ty.numBits = (-x.val).toNat := by
    have : ↑(-x.val).toNat < 2 ^ ty.numBits := by
      zify
      apply Int.lt_of_neg_lt_neg
      have : - (-x.val).toNat = x.val := by omega
      rw [this]; clear this
      have := x.hmin
      omega
    have := @Nat.mod_eq_of_lt (-x.val).toNat (2^ty.numBits) (by omega)
    apply this
  zify at hyValToNatMod
  rw [hyValToNatMod]
  omega

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.div_bv_spec {ty} {x y : IScalar ty}
  (hzero : y.val ≠ 0) (hNoOverflow : ¬ (x.val = IScalar.min ty ∧ y.val = -1)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = Int.tdiv ↑x ↑y ∧ z.bv = BitVec.sdiv x.bv y.bv := by
  conv => congr; ext; lhs; simp only [HDiv.hDiv]
  simp only [div, bne_iff_ne, ne_eq, hzero, not_false_eq_true, ↓reduceIte, Int.reduceNeg,
    Bool.and_eq_true, decide_eq_true_eq, hNoOverflow, ok.injEq, _root_.exists_eq_left', and_true]
  simp only [val]
  -- TODO: simplify the proof by using BitVec.toInt_srem

  simp only [BitVec.sdiv_eq, BitVec.udiv_eq, BitVec.udiv_def, BitVec.toNat_neg, bv_toInt_eq]
  have pow2Ineq : (2^(ty.numBits - 1) : Int) < 2^ty.numBits := by
    have := ty.numBits_nonzero
    have : (0 : Int) < 2^(ty.numBits - 1) := by simp only [Nat.ofNat_pos, pow_pos]
    have : ty.numBits = ty.numBits - 1 + 1 := by omega
    conv => rhs; rw [this]
    rw [Int.pow_succ']
    omega
  have hxBounds := x.hBounds
  have hyBounds := y.hBounds

  split

  . -- 0 ≤ x.bv.toInt
    -- 0 ≤ y.bv.toInt
    rw [BitVec.toInt_ofNat']
    simp only [Int.natCast_ediv]
    have hx : x.bv.toNat = x.bv.toInt := by
      have := @BitVec.toInt_eq_msb_cond _ x.bv
      simp_all
    have hy : y.bv.toNat = y.bv.toInt := by
      have := @BitVec.toInt_eq_msb_cond _ y.bv
      simp_all
    simp only [hx, bv_toInt_eq, hy]
    simp only [bv_toInt_eq] at hx hy
    have := @Int.tdiv_nonneg x.val y.val (by omega) (by omega)
    have : -2 ^ (ty.numBits - 1) ≤ 0 := by
      simp only [Left.neg_nonpos_iff, Nat.ofNat_nonneg, pow_nonneg]
    have : (x.val).tdiv y.val < 2 ^ (ty.numBits - 1) := by
      rw [Int.tdiv_eq_ediv]; split <;> try omega
      have := @Int.ediv_le_self x.val y.val (by omega)
      omega

    have hEq := bmod_pow_numBits_eq_of_lt ty (Int.tdiv x.val y.val) (by omega) (by omega)
    rw [← hEq]
    have htdiv : Int.tdiv x.val y.val = x.val / y.val := by
      rw [Int.tdiv_eq_ediv]
      have : 0 ≤ x.val := by omega
      simp only [this, true_or, ↓reduceIte, add_zero]
    rw [htdiv]

  . -- 0 ≤ x.bv.toInt
    -- y.bv.toInt < 0
    rename_i hxIneq hyIneq
    have hx := @BitVec.toInt_eq_msb_cond _ x.bv
    simp only [bv_toInt_eq, hxIneq, Bool.false_eq_true, ↓reduceIte] at hx
    have hy := @BitVec.toInt_eq_msb_cond _ y.bv
    simp only [bv_toInt_eq, hyIneq, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] at hy
    have hyNeg : y.val < 0 := by
      have := @BitVec.msb_eq_toInt _ y.bv
      simp_all
    have : -2 ^ (ty.numBits - 1) ≤ Int.tdiv x.val y.val := by
      have : Int.tdiv x.val (-y.val) ≤ 2^(ty.numBits - 1) := by
        rw [Int.tdiv_eq_ediv]
        have := @Int.ediv_le_self x.val (-y.val) (by omega)
        simp only [ne_eq, Int.reduceNeg, not_and, Int.ediv_neg, ge_iff_le] at *
        have := x.hmax
        omega
      replace this := Int.neg_le_neg this
      simp only [Int.tdiv_neg, neg_neg] at this
      apply this
    have hyToNat : 2 ^ ty.numBits - y.bv.toNat = (-y.val).toNat := by
      rw [hy]
      simp only [neg_sub, Int.toNat_sub']
      norm_cast
    rw [BitVec.toInt_neg, BitVec.toInt_ofNat']
    simp only [Int.natCast_ediv, Int.natCast_emod, Nat.cast_pow, Nat.cast_ofNat]
    rw [hyToNat]
    have : ((-y.val).toNat : Int) % 2^ty.numBits = -(y.val : Int) := by
      apply IScalar.neg_imp_neg_val_toNat_mod_pow_eq_neg_val
      simp only [bv_toInt_eq]; omega
    rw [this]; clear this
    simp only [Int.ediv_neg, Int.bmod_neg_bmod, neg_neg]
    rw [← hx]
    have : (x.val / y.val).bmod (2^ty.numBits) = x.val / y.val := by
      have : -2 ^ (ty.numBits - 1) ≤ x.val / ↑y := by
        apply Int.le_of_neg_le_neg
        have : - (x.val / y.val) = x.val / -y.val := by simp only [Int.ediv_neg]
        rw [this]; clear this
        have := @Int.ediv_le_self x.val (-y.val) (by omega)
        omega
      have : x.val / ↑y < 2 ^ (ty.numBits - 1) := by
        have : 0 < 2 ^ (ty.numBits - 1) := by simp only [Nat.ofNat_pos, pow_pos]
        have : x.val / y.val ≤ 0 := by apply Int.ediv_nonpos_of_nonneg_of_nonpos <;> omega
        omega
      have := bmod_pow_numBits_eq_of_lt ty (x.val / y.val) (by omega) (by omega)
      rw [this]

    rw [this]; clear this

    have : x.val.tdiv y.val = - (x.val.tdiv (-y.val)) := by simp only [Int.tdiv_neg, neg_neg]
    rw [this]
    have : x.val.tdiv (-y.val) = (x.val) / (-y.val) := by
      have := @Int.tdiv_eq_ediv x.val (-y.val)
      rw [this]
      split <;> omega
    rw [this]; clear this
    simp only [Int.ediv_neg, neg_neg]

  . -- x.bv.toInt < 0
    -- 0 ≤ y.bv.toInt
    rename_i hxIneq hyIneq
    have hx := @BitVec.toInt_eq_msb_cond _ x.bv
    simp only [bv_toInt_eq, hxIneq, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] at hx
    have hy := @BitVec.toInt_eq_msb_cond _ y.bv
    simp only [bv_toInt_eq, hyIneq, Bool.false_eq_true, ↓reduceIte] at hy
    have hxNeg : x.val < 0 := by
      have := @BitVec.msb_eq_toInt _ x.bv
      simp_all
    have hyPos : 0 ≤ y.val := by
      have := @BitVec.msb_eq_toInt _ y.bv
      simp_all
    have : -2 ^ (ty.numBits - 1) ≤ x.val / y.val := by
      have := @Int.ediv_le_ediv (-2 ^ (ty.numBits - 1)) x.val y.val (by omega) (by omega)
      have := @Int.self_le_ediv x.val y.val (by omega) (by omega)
      omega
    have hxToNat : 2 ^ ty.numBits - x.bv.toNat = (-x.val).toNat := by
      rw [hx]
      simp only [neg_sub, Int.toNat_sub']
      norm_cast
    rw [BitVec.toInt_neg, BitVec.toInt_ofNat']
    simp only [Int.natCast_ediv, Int.natCast_emod, Nat.cast_pow, Nat.cast_ofNat]

    rw [hxToNat]
    have : ((-x.val).toNat : Int) % 2^ty.numBits = -(x.val : Int) := by
      apply IScalar.neg_imp_neg_val_toNat_mod_pow_eq_neg_val
      simp only [bv_toInt_eq]; omega
    rw [this]; clear this

    /- We have to treat separately the degenerate case where `x` touches the upper bound
       and `y = 1` -/
    dcases hxDivY : -x.val / y.val = 2^(ty.numBits - 1)
    . rw [← hy]
      rw [hxDivY]
      have ⟨ hx, hy ⟩ : x.val = - 2^(ty.numBits - 1) ∧ y.val = 1 := by
        have := @Int.le_div_eq_bound_imp_eq (-x.val) y.val (2^(ty.numBits - 1))
          (by omega) (by omega) (by omega) (by omega)
        omega
      simp only [hx, hy, Int.tdiv_one]

      have : Int.bmod (2 ^ (ty.numBits - 1)) (2 ^ ty.numBits) =
             - 2 ^ (ty.numBits - 1) :=
        Int.bmod_pow2_IScalarTy_numBits_minus_one ty
      rw [this]
      simp only [neg_neg]
      rw [this]
    . have : 0 ≤ (-x.val) / y.val := by
        apply Int.ediv_nonneg <;> omega
      have : -x.val / y.val < 2^(ty.numBits - 1) := by
        have : -x.val ≤ 2^(ty.numBits - 1) := by omega
        have := @Int.ediv_le_self (-x.val) y.val (by omega)
        omega
      rw [← hy]
      have : (-x.val / y.val).bmod (2 ^ ty.numBits) =
             (-x.val / y.val) := by
        apply bmod_pow_numBits_eq_of_lt ty _ (by omega) (by omega)
      rw [this]; clear this
      have : (-(-x.val / ↑y)).bmod (2 ^ ty.numBits) =
             (-(-x.val / ↑y)) := by
        apply bmod_pow_numBits_eq_of_lt ty _ (by omega) (by omega)
      rw [this]; clear this
      have : (-x.val) / y.val = (-x.val).tdiv y.val := by
        rw [Int.tdiv_eq_ediv]
        omega

      rw [this]; simp only [Int.neg_tdiv, neg_neg]

  . -- x.bv.toInt < 0
    -- y.bv.toInt < 0
    rename_i hxIneq hyIneq
    have hx := @BitVec.toInt_eq_msb_cond _ x.bv
    simp only [bv_toInt_eq, hxIneq, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] at hx
    have hy := @BitVec.toInt_eq_msb_cond _ y.bv
    simp only [bv_toInt_eq, hyIneq, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] at hy
    have hxNeg : x.val < 0 := by
      have := @BitVec.msb_eq_toInt _ x.bv
      simp_all
    have hyNeg : y.val < 0 := by
      have := @BitVec.msb_eq_toInt _ y.bv
      simp_all
    have hxToNat : 2 ^ ty.numBits - x.bv.toNat = (-x.val).toNat := by
      rw [hx]
      simp only [neg_sub, Int.toNat_sub']
      norm_cast
    have hyToNat : 2 ^ ty.numBits - y.bv.toNat = (-y.val).toNat := by
      rw [hy]
      simp only [neg_sub, Int.toNat_sub']
      norm_cast
    rw [hxToNat, hyToNat]

    have : (-x.val).toNat % 2^ty.numBits = (-x.val).toNat := by
      apply Nat.mod_eq_of_lt
      omega
    rw [this]
    have : (-y.val).toNat % 2^ty.numBits = (-y.val).toNat := by
      apply Nat.mod_eq_of_lt
      omega
    rw [this]

    rw [BitVec.toInt_ofNat']

    /- We have to treat separately the degenerate case where `x` touches the lower bound
       and `y = -1`, because then `x / y` actually overflows -/
    have hxyInBouds : (-x.val) / (-y.val) ≠ 2^(ty.numBits - 1) := by
      -- We do the proof by contradiction
      intro hEq
      have hContra : x.val = - 2^(ty.numBits - 1) ∧ y.val = -1 := by
        have := @Int.le_div_eq_bound_imp_eq (-x.val) (-y.val) (2^(ty.numBits - 1))
          (by omega) (by omega) (by omega) (by omega)
        omega
      simp only [hContra, min, Int.reduceNeg, and_self, not_true_eq_false] at hNoOverflow

    have : -(2 ^ (ty.numBits - 1) : Int) ≤ ↑((-x.val).toNat / (-y.val).toNat) := by
      have := @Int.ediv_nonneg (-x.val).toNat (-y.val).toNat (by omega) (by omega)
      have : -(2 ^ (ty.numBits - 1) : Int) ≤ 0 := by
        simp only [Left.neg_nonpos_iff, Nat.ofNat_nonneg, pow_nonneg]
      omega

    have : ((-x.val).toNat / (-y.val).toNat) < (2 ^ (ty.numBits - 1) : Int) := by
      -- First prove a ≤ bound
      have hIneq : ((-x.val).toNat / (-y.val).toNat) ≤ (2 ^ (ty.numBits - 1) : Int) := by
        have := @Int.ediv_le_self (-x.val).toNat (-y.val).toNat (by omega)
        omega
      -- Then use the hypothesis about the fact that we're not equal to the bound
      zify at hIneq
      have : (-x.val).toNat = -x.val := by omega
      rw [this] at hIneq; rw [this]
      have : (-y.val).toNat = -y.val := by omega
      rw [this] at hIneq; rw [this]
      omega
    have := bmod_pow_numBits_eq_of_lt ty ((-x.val).toNat / (-y.val).toNat : Nat) (by omega) (by omega)
    rw [this]

    zify; simp only [Int.ofNat_toNat]

    have : (-x.val) ⊔ 0 = -x.val := by omega
    simp only [this]; clear this
    have : -↑y ⊔ 0 = -y.val := by omega
    simp only [this]; clear this

    have : (-x.val) / (-y.val) = (-x.val).tdiv (-y.val) := by
      rw [Int.tdiv_eq_ediv]; omega
    rw [this]
    simp only [Int.tdiv_neg, Int.neg_tdiv, neg_neg]

uscalar theorem «%S».div_bv_spec (x : «%S») {y : «%S»} (hnz : ↑y ≠ (0 : Nat)) :
  ∃ z, x / y = ok z ∧ (↑z : Nat) = ↑x / ↑y ∧ z.bv = x.bv / y.bv :=
  UScalar.div_bv_spec x hnz

iscalar theorem «%S».div_bv_spec {x y : «%S»} (hnz : ↑y ≠ (0 : Int))
  (hNoOverflow : ¬ (x.val = «%S».min ∧ y.val = -1)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = Int.tdiv ↑x ↑y ∧ z.bv = BitVec.sdiv x.bv y.bv :=
  IScalar.div_bv_spec hnz (by scalar_tac)

/-!
Theorems with a specification which only use integers
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.div_spec {ty} (x : UScalar ty) {y : UScalar ty}
  (hzero : y.val ≠ 0) :
  ∃ z, x / y = ok z ∧ (↑z : Nat) = ↑x / ↑y := by
  have ⟨ z, hz ⟩ := UScalar.div_bv_spec x hzero
  simp [hz]

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.div_spec {ty} {x y : IScalar ty}
  (hzero : y.val ≠ 0)
  (hNoOverflow : ¬ (x.val = IScalar.min ty ∧ y.val = -1)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = Int.tdiv ↑x ↑y := by
  have ⟨ z, hz ⟩ := IScalar.div_bv_spec hzero hNoOverflow
  simp [hz]

uscalar @[progress] theorem «%S».div_spec (x : «%S») {y : «%S»} (hnz : ↑y ≠ (0 : Nat)) :
  ∃ z, x / y = ok z ∧ (↑z : Nat) = ↑x / ↑y :=
  UScalar.div_spec x hnz

iscalar @[progress] theorem «%S».div_spec {x y : «%S»} (hnz : ↑y ≠ (0 : Int))
  (hNoOverflow : ¬ (x.val = «%S».min ∧ y.val = -1)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = Int.tdiv ↑x ↑y :=
  IScalar.div_spec hnz (by scalar_tac)

end Aeneas.Std
