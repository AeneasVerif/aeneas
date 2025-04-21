import Mathlib.Data.Nat.Bitwise
import Aeneas.SimpScalar.Init
import Aeneas.ScalarTac.CondSimpTac
import Aeneas.SimpLists.Init -- We need to mark some lemmas as `simp_lists_simps`

/-!
# `simp_scalar` tactic

The `simp_scalar` tactic is used to simplify arithmetic expressions.
-/

namespace Aeneas.SimpScalar

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

/- Theorems to simplify booleans.

   This is useful because simplifying arithmetic expressions often introduces
   those. As they are quite trivial we expect them to get simplified away
   independently of the simp tactic we're using.
-/
attribute [simp_scalar_simps]
  implies_true
  Bool.and_true Bool.true_and
  Bool.false_or Bool.or_false
  Bool.true_or Bool.or_true
  true_or or_true
  true_and and_true
  false_or or_false
  false_and and_false
  decide_eq_false_iff_not ne_eq
  false_eq_decide_iff true_eq_decide_iff
  not_false_eq_true Bool.not_true Bool.not_false
  Bool.not_eq_eq_eq_not
  decide_true decide_false
  Bool.and_self
  iff_false iff_true

/- Making sure we always reason in terms of `≤` and `<` -/
attribute [simp_scalar_simps] ge_iff_le gt_iff_lt

@[simp_scalar_simps] theorem Nat.eq_imp_eq_true (x y : ℕ) (h : x = y) : (x = y) ↔ True := by simp [*]
@[simp_scalar_simps] theorem Nat.ne_imp_ne_true (x y : ℕ) (h : ¬ x = y) : (¬ x = y) ↔ True := by simp [*]
@[simp_scalar_simps] theorem Int.eq_imp_eq_true (x y : ℤ) (h : x = y) : (x = y) ↔ True := by simp [*]
@[simp_scalar_simps] theorem Int.ne_imp_ne_true (x y : ℤ) (h : ¬ x = y) : (¬ x = y) ↔ True := by simp [*]

@[simp_scalar_simps] theorem Nat.ne_imp_eq_false (x y : ℕ) (h : ¬ x = y) : (x = y) ↔ False := by simp [*]
@[simp_scalar_simps] theorem Nat.eq_imp_ne_false (x y : ℕ) (h : x = y) : (¬ x = y) ↔ False := by simp [*]
@[simp_scalar_simps] theorem Int.ne_imp_eq_false (x y : ℤ) (h : ¬ x = y) : (x = y) ↔ False := by simp [*]
@[simp_scalar_simps] theorem Int.eq_imp_ne_false (x y : ℤ) (h : x = y) : (¬ x = y) ↔ False := by simp [*]

@[simp_scalar_simps] theorem Nat.lt_imp_lt (a b : ℕ) : a < b → a < b := by omega
@[simp_scalar_simps] theorem Nat.le_imp_le (a b : ℕ) : a ≤ b → a ≤ b := by omega

@[simp_scalar_simps] theorem Int.lt_imp_lt (a b : ℤ) : a < b → a < b := by omega
@[simp_scalar_simps] theorem Int.le_imp_le (a b : ℤ) : a ≤ b → a ≤ b := by omega

@[simp_scalar_simps] theorem Nat.ge_imp_lt_iff_false (a b : ℕ) : a ≥ b → (a < b ↔ False) := by
  simp +contextual only [ge_iff_le, iff_false, not_lt, implies_true]

@[simp_scalar_simps] theorem Nat.gt_imp_le_iff_false (a b : ℕ) : a > b → (a ≤ b ↔ False) := by
  simp +contextual only [gt_iff_lt, iff_false, not_le, implies_true]

@[simp_scalar_simps] theorem Int.ge_imp_lt_iff_false (a b : ℤ) : a ≥ b → (a < b ↔ False) := by
  simp +contextual only [ge_iff_le, iff_false, not_lt, implies_true]

@[simp_scalar_simps] theorem Int.gt_imp_le_iff_false (a b : ℤ) : a > b → (a ≤ b ↔ False) := by
  simp +contextual only [gt_iff_lt, iff_false, not_le, implies_true]

attribute [simp_scalar_simps] Nat.mod_eq_of_lt

@[simp_scalar_simps]
theorem Int.emod_eq_of_lt' {a b : ℤ} (h : 0 ≤ a ∧ a < b) : a % b = a := by
  apply Int.emod_eq_of_lt <;> omega

@[simp_scalar_simps]
theorem Nat.le_pow (a i : ℕ) (h : 0 < a ∧ 0 < i) : a ≤ a ^ i := by
  have : a ^ 1 ≤ a ^ i := by apply Nat.pow_le_pow_right <;> omega
  simp_all

@[simp_scalar_simps]
theorem Nat.lt_pow (a i : ℕ) (h : 1 < a ∧ 1 < i) : a < a ^ i := by
  have : a ^ 1 < a ^ i := by apply Nat.pow_lt_pow_right <;> omega
  simp_all

attribute [simp_scalar_simps]
  zero_add add_zero
  inf_of_le_left inf_of_le_right
  Nat.pow_le_pow_right Nat.pow_le_pow_left
  Nat.pow_lt_pow_right Nat.pow_lt_pow_left
  Nat.mul_eq_zero
  add_tsub_cancel_right add_tsub_cancel_left
  not_lt not_le

-- TODO: we want a general simproc to normalize arithmetic expressions like what ring does
attribute [simp_scalar_simps]
  Nat.add_sub_of_le
  mul_eq_mul_left_iff mul_eq_mul_right_iff
  Nat.add_left_inj Nat.add_right_inj
  Nat.add_div_right Nat.add_div_left

-- TODO: general simproc for canceling mul then div/mod (all those lemmas are quite specific)
attribute [simp_scalar_simps]
  Nat.mul_div_cancel Nat.mul_div_cancel_left Nat.mul_div_mul_left Nat.mul_div_mul_right
  Nat.div_mul_cancel Nat.mul_div_cancel'
  Nat.mul_add_div Nat.mod_div_self
  Nat.add_mul_div_left Nat.add_mul_div_right
  Nat.mul_add_mod' Nat.mul_add_mod
  Nat.add_mul_mod_self_left Nat.add_mul_mod_self_right

@[simp_scalar_simps]
theorem Nat.div_div_eq_div_mul_true (m n k : ℕ) : (m / n / k = m / (n * k)) ↔ True := by
  simp only [Nat.div_div_eq_div_mul]

@[simp_scalar_simps]
theorem Nat.div_mul_eq_div_div_true (m n k : ℕ) : (m / (n * k) = m / n / k) ↔ True := by
  simp only [Nat.div_div_eq_div_mul]

@[simp_scalar_simps]
theorem Nat.eq_imp_div_eq (a b c : ℕ) (h : a = b) : a / c = b / c := by simp [*]

@[simp_scalar_simps]
theorem Nat.mul_add_div' {m : Nat} (m_pos : m > 0) (x y : Nat) : (x * m + y) / m = x + y / m := by
  have : x * m = m * x := by ring_nf
  rw [this]
  apply Nat.mul_add_div m_pos

@[simp_scalar_simps]
theorem Nat.lt_mul_imp_div_lt {k x y : ℕ} (Hk : 0 < k ∧ x < y * k) : x / k < y := by
  rw [Nat.div_lt_iff_lt_mul] <;> omega

@[simp_scalar_simps]
theorem Nat.sub_mod_div_eq_div {m n : ℕ} : (m - m % n) / n = m / n := by
  simp only [← Nat.div_eq_sub_mod_div]

/- Remark: this one may be quite expensive because there tends to be a lot of subtractions
   which don't simplify in the context -/
attribute [simp_scalar_simps] Nat.sub_eq_zero_of_le

attribute [simp_scalar_simps]
  Nat.div_le_div_right Nat.mul_div_le Nat.div_mul_le_self
  Nat.pow_lt_pow_right Nat.mod_lt Nat.mod_le

@[simp_scalar_simps]
theorem Nat.lt_imp_mod_eq_self (x n : ℕ) (h : x < n) : (x = x % n) ↔ True := by
  have := Nat.mod_eq_of_lt h
  simp [*]

/- Bitwise reasoning -/
attribute [simp_scalar_simps]
  Nat.testBit_two_pow_add_gt Nat.testBit_eq_false_of_lt
  Nat.testBit_two_pow Nat.testBit_mod_two_pow
  Nat.testBit_shiftRight Nat.testBit_shiftLeft
  Nat.testBit_add_one
  Nat.div_eq_of_lt
  Nat.testBit_two_pow_add_eq

/- This one is very common so marking it as `simp` as well -/
attribute [simp] Nat.testBit_two_pow_add_eq

@[simp_scalar_simps, simp_lists_simps]
theorem Nat.testBit_two_pow_add_eq' (x i j : ℕ) (h : i = j) : (2 ^ i + x).testBit j = !x.testBit i := by
  simp only [h]
  apply Nat.testBit_two_pow_add_eq

@[simp_scalar_simps, simp_lists_simps]
theorem Nat.testBit_add_two_pow_eq' (x i j : ℕ) (h : i = j) : (x + 2 ^ i).testBit j = !x.testBit i := by
  rw [add_comm]
  simp only [h]
  apply Nat.testBit_two_pow_add_eq

@[simp_scalar_simps, simp_lists_simps]
theorem Nat.testBit_add_two_pow_gt {i j : ℕ} (j_lt_i : j < i) (x : ℕ) : (x + 2 ^ i).testBit j = x.testBit j := by
  rw [add_comm]
  apply Nat.testBit_two_pow_add_gt
  omega

@[simp_scalar_simps, simp_lists_simps]
theorem Nat.testBit_one : Nat.testBit 1 i = decide (i = 0) := by
  cases i
  . simp only [Nat.testBit_zero, Nat.mod_succ, decide_true]
  . simp only [Nat.add_eq_zero, one_ne_zero, and_false, decide_false, Nat.testBit_add_one, Nat.reduceDiv, Nat.zero_testBit]

-- TODO: use that with scalar_tac +nonLin
@[simp_scalar_simps]
theorem BitVec.toNat_lt_two_pow {w} (x : BitVec w) (i : ℕ) (h : w ≤ i) : x.toNat < 2^i := by
  have : 2^w ≤ 2^i := by scalar_tac +nonLin
  omega

def simpScalarTac (args : ScalarTac.CondSimpPartialArgs) (loc : Utils.Location) : TacticM Unit := do
  let addSimpThms : TacticM (Array FVarId) := pure #[]
  let args : ScalarTac.CondSimpArgs := {
      simpThms := #[← simpScalarSimpExt.getTheorems],
      simprocs := #[← simpScalarSimprocExt.getSimprocs],
      declsToUnfold := args.declsToUnfold,
      addSimpThms := args.addSimpThms,
      hypsToUse := args.hypsToUse,
    }
  ScalarTac.condSimpTac "simp_scalar" true {maxDischargeDepth := 2, failIfUnchanged := false, contextual := true} args addSimpThms false loc

syntax (name := simp_scalar) "simp_scalar" ("[" (term<|>"*"),* "]")? (location)? : tactic

def parseSimpScalar : TSyntax ``simp_scalar -> TacticM (ScalarTac.CondSimpPartialArgs × Utils.Location)
| `(tactic| simp_scalar $[[$args,*]]?) => do
  let args := args.map (·.getElems) |>.getD #[]
  let args ← ScalarTac.condSimpParseArgs "simp_scalar" args
  pure (args, Utils.Location.targets #[] true)
| `(tactic| simp_scalar $[[$args,*]]? $[$loc:location]?) => do
  let args := args.map (·.getElems) |>.getD #[]
  let args ← ScalarTac.condSimpParseArgs "simp_scalar" args
  let loc ← Utils.parseOptLocation loc
  pure (args, loc)
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:simp_scalar : tactic =>
  withMainContext do
  let (args, loc) ← parseSimpScalar stx
  simpScalarTac args loc

end Aeneas.SimpScalar
