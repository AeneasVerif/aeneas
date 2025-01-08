import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Cast.Order.Ring

namespace Arith

open Lean Elab Term Meta

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Arith

-- TODO: move?
theorem ne_zero_is_lt_or_gt {x : Int} (hne : x ≠ 0) : x < 0 ∨ x > 0 := by
  cases h: x <;> simp_all
  . rename_i n;
    cases n <;> simp_all
  . apply Int.negSucc_lt_zero

-- TODO: move?
theorem ne_is_lt_or_gt {x y : Int} (hne : x ≠ y) : x < y ∨ x > y := by
  have hne : x - y ≠ 0 := by
    simp
    intro h
    have: x = y := by omega
    simp_all
  have h := ne_zero_is_lt_or_gt hne
  match h with
  | .inl _ => left; omega
  | .inr _ => right; omega

-- TODO: move?
theorem add_one_le_iff_le_ne (n m : Nat) (h1 : m ≤ n) (h2 : m ≠ n) : m + 1 ≤ n := by
  -- Damn, those proofs on natural numbers are hard - I wish Omega was in mathlib4...
  simp [Nat.add_one_le_iff]
  simp [Nat.lt_iff_le_and_ne]
  simp_all

/- Induction over positive integers -/
-- TODO: move
theorem int_pos_ind (p : Int → Prop) :
  (zero:p 0) → (pos:∀ i, 0 ≤ i → p i → p (i + 1)) → ∀ i, 0 ≤ i → p i := by
  intro h0 hr i hpos
--  have heq : Int.toNat i = i := by
--    cases i <;> simp_all
  have ⟨ n, heq ⟩  : {n:Nat // n = i } := ⟨ Int.toNat i, by cases i <;> simp_all ⟩
  revert i
  induction n
  . intro i hpos heq
    cases i <;> simp_all
  . rename_i n hi
    intro i hpos heq
    cases i <;> simp_all
    rename_i m
    cases m <;> simp_all

-- This is mostly used in termination proofs
theorem to_int_to_nat_lt (x y : ℤ) (h0 : 0 ≤ x) (h1 : x < y) :
  ↑(x.toNat) < y := by
  simp [*]

-- This is mostly used in termination proofs
theorem to_int_sub_to_nat_lt (x y : ℤ) (x' : ℕ)
  (h0 : ↑x' ≤ x) (h1 : x - ↑x' < y) :
  ↑(x.toNat - x') < y := by
  have : 0 ≤ x := by omega
  simp [Int.toNat_sub_of_le, *]

-- WARNING: do not use this with `simp` as it might loop. The left-hand side indeed reduces to the
-- righ-hand side, meaning the rewriting can be applied to `n` itself.
theorem ofNat_instOfNatNat_eq (n : Nat) : @OfNat.ofNat Nat n (instOfNatNat n) = n := by rfl


/-- Small helper

    We used to use this for the list definitions, as some definitions like `index` used to
    manipulate integers and not natural numbers.

    We cover a set of cases which might imply inequality, to make sure that using
    this as the precondition of a `simp` lemma will allow the lemma to get correctly
    triggered.
    TODO: there should be something more systematic to do, with discharged procedures
    or simprocs I guess. -/
@[simp]
abbrev Int.not_eq (i j : Int) : Prop :=
  i ≠ j ∨ j ≠ i ∨ i < j ∨ j < i

theorem Int.not_eq_imp_not_eq {i j} : Int.not_eq i j → i ≠ j := by
  intro h g
  simp_all

@[simp]
abbrev Nat.not_eq (i j : Nat) : Prop :=
  i ≠ j ∨ j ≠ i ∨ i < j ∨ j < i

theorem Nat.not_eq_imp_not_eq {i j} : Nat.not_eq i j → i ≠ j := by
  intro h g
  simp_all

@[simp]
theorem Nat.le_imp_le_equiv_eq (i j : Nat) (h0 : i ≤ j) : j ≤ i ↔ i = j := by
  omega

@[simp]
theorem Int.le_imp_le_equiv_eq (i j : Int) (h0 : i ≤ j) : j ≤ i ↔ i = j := by
  omega

example (i : Int) (j : Nat) (h : i ≤ j) (h2 : j ≤ i) :
  i = j := by
  simp_all

end Arith
