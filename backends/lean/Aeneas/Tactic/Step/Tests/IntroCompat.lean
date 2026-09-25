module
import Aeneas.Tactic.Step
public meta import Lean
public meta import Aeneas.Tactic.Step
import Aeneas.Tactic.Solver.ScalarTac

/-!
# `step` introduces outputs and facts like it did before `intro_tactic`

Proofs written against earlier versions of `step` (e.g. the VCR proofs) rely on the order
and names of the introduced variables, and on the shape of the remaining goal. Each test
below is reduced from such a proof.
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.IntroCompat

def dup (n : Nat) : Result (Nat × Nat) := ok (n, n)

def id' (n : Nat) : Result Nat := ok n

@[local step]
theorem id'_spec (n : Nat) : id' n ⦃ r => r = n ⦄ := by simp [id']

/-! ## Leading existentials of a postcondition come after the outputs -/

theorem dup_witness_spec (n : Nat) :
    dup n ⦃ a b => ∃ (w : Bool) (k : Nat), a = n + k ∧ b = n ∧ w = (k == 0) ⦄ := by
  simp [dup, Aeneas.Std.WP.uncurry']

example (n : Nat) :
    (do let (a, b) ← dup n; ok (a, b)) ⦃ _ b => b = n ⦄ := by
  step with dup_witness_spec as ⟨a, b, w, k, ha, hb, hw⟩
  guard_hyp a : Nat
  guard_hyp b : Nat
  guard_hyp w : Bool
  guard_hyp k : Nat
  guard_hyp ha : a = n + k
  guard_hyp hb : b = n
  guard_hyp hw : w = (k == 0)
  exact hb

/-! ## Facts about existential witnesses are named after the binder

The facts about the witness of `∃ s, …` are named `s_post`, `s_post1`, ... -/

theorem dup_nested_spec (n : Nat) :
    dup n ⦃ a b => a = n ∧ ∃ s, s ≥ a ∧ s = a + b ∧ b = n ⦄ := by
  simp [dup, Aeneas.Std.WP.uncurry']

example (n : Nat) :
    (do let (a, b) ← dup n; ok (a + b)) ⦃ r => r = n + n ⦄ := by
  step with dup_nested_spec
  rename_i s
  guard_hyp s_post : s ≥ a
  guard_hyp s_post1 : s = a + b
  guard_hyp b_post : b = n
  simp [a_post, b_post]

/-! ## Facts which become trivial after instantiation are kept

`↑12#u32 = 12` only reduces to `True` once `step` has introduced the facts: it stays a
conjunct. -/

def flag (d : U32) : Result Bool := ok (d.val = 12)

theorem flag_spec (d : U32) (P : Nat → Prop) (hP : ∀ j, ¬ P j) :
    flag d ⦃ b => match b with
      | true => d.val = 12 ∧ ∃ j, j < 5 ∧ ¬ P j
      | false => True ⦄ := by
  simp only [flag, WP.spec_ok]
  split
  · rename_i h
    simp only [decide_eq_true_eq] at h
    exact ⟨h, 0, by agrind, hP 0⟩
  · trivial

example (P : Nat → Prop) (hP : ∀ j, ¬ P j) :
    flag 12#u32 ⦃ b => b = false ∨ ∃ j, j < 5 ∧ ¬ P j ⦄ := by
  step with flag_spec (P := P) (hP := hP) as ⟨b, h⟩
  cases b
  · exact Or.inl rfl
  · obtain ⟨_, j, hj, hnot⟩ := h
    exact Or.inr ⟨j, hj, hnot⟩

/-! ## Reducible postconditions are split -/

abbrev dupPost (n a b : Nat) : Prop :=
  ∃ (_h : a = n), b = n ∧ a = b

theorem dup_abbrev_spec (n : Nat) : dup n ⦃ a b => dupPost n a b ⦄ := by
  simp [dup, Aeneas.Std.WP.uncurry']

example (n : Nat) :
    (do let (a, b) ← dup n; ok (a, b)) ⦃ a b => dupPost n a b ⦄ := by
  step with dup_abbrev_spec as ⟨a, b, h0, h1, h2⟩
  guard_hyp h0 : a = n
  guard_hyp h1 : b = n
  guard_hyp h2 : a = b
  exact ⟨h0, h1, h2⟩

/-! ## The facts and the postcondition of the goal are normalized

Conjunctive and existential premises are curried, and `True` premises are dropped. -/

theorem id'_curried_spec (n : Nat) : id' n ⦃ r => ∀ j, (_h : j ≤ r ∧ r ≤ j) → j = n ⦄ := by
  simp only [id', WP.spec_ok]
  intro j h
  agrind

example (n : Nat) : (do let r ← id' n; ok r) ⦃ r => r = n ⦄ := by
  step with id'_curried_spec as ⟨r, h⟩
  exact h r (Nat.le_refl r) (Nat.le_refl r)

example (n : Nat) :
    (do let r ← id' n; id' r) ⦃ r => ∀ j, (_h : j ≤ r ∧ r ≤ j) → j = n ⦄ := by
  step
  apply WP.spec_mono (id'_spec r)
  intro r' hr' j h1 h2
  guard_hyp h1 : j ≤ r'
  guard_hyp h2 : r' ≤ j
  agrind

example (n : Nat) :
    (do let r ← id' n; id' r) ⦃ r => (∃ k, k + n = r) → r ≥ n ⦄ := by
  step
  apply WP.spec_mono (id'_spec r)
  intro r' hr' k hk
  guard_hyp k : Nat
  guard_hyp hk : k + n = r'
  agrind

example (n : Nat) (hn : n < 2) :
    (do let r ← id' n; id' r) ⦃ r => True → ∀ j : Fin 2, j.val < 2 ∧ r < 2 ⦄ := by
  step
  apply WP.spec_mono (id'_spec r)
  intro r' hr' j
  guard_hyp j : Fin 2
  agrind

end Aeneas.Tactic.Step.Tests.IntroCompat
