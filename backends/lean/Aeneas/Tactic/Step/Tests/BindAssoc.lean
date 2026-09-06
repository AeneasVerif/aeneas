import Aeneas.Tactic.Step
import Aeneas.Do

open Aeneas Aeneas.Std Result

/-!
# Tests for `bind_assoc` normalization of tuple-destructuring binds (issue #1148)

A tuple-destructuring bind `let (a, b) ← e` is elaborated as
`Bind.bind e (Std.uncurry f)`. Before the fix, `simp only [step_simps]` would
reassociate `(e >>= uncurry f) >>= h` with the generic `bind_assoc`, producing the
ugly `do let x ← e; let (a, b) := x; …`. The `bind_assoc_uncurry` /
`bind_uncurry_app` lemmas (registered with high priority in `step_simps`) keep the
destructuring on the bind, yielding the expected `do let (a, b) ← e; …` form.

Each test pins the exact normalized goal via `#guard_msgs`. -/

namespace Aeneas.Tactic.Step.Tests.BindAssoc

axiom pairProg : Result (Nat × Nat)
axiom tripProg : Result (Nat × Nat × Nat)
axiom nestProg : Result ((Nat × Nat) × (Nat × Nat))

/- The exact example from issue #1148: a 2-tuple bind nested inside an outer bind.
The destructuring must stay on the bind (`let (a, b) ← pairProg`), NOT degrade to
`let x ← pairProg; let (a, b) := x`.-/
/--
error: unsolved goals
h : ℕ → Result ℕ
⊢ (do
      let (a, b) ← pairProg
      h (a + b)) =
    ok 0
-/
#guard_msgs in
example (h : Nat → Result Nat) :
    (do let k ← (do let (a, b) ← pairProg; ok (a + b)); h k) = ok 0 := by
  simp only [step_simps]; done

/- 3-tuple (right-nested `uncurry` chain): all destructuring stays on the bind.-/
/--
error: unsolved goals
h : ℕ → Result ℕ
⊢ (do
      let (a, (a, b)) ← tripProg
      h (a + a + b)) =
    ok 0
-/
#guard_msgs in
example (h : Nat → Result Nat) :
    (do let k ← (do let (a, b, c) ← tripProg; ok (a + b + c)); h k) = ok 0 := by
  simp only [step_simps]; done

/- Deeply nested tuple `((a, b), (c, d))`: every layer is threaded cleanly.-/
/--
error: unsolved goals
h : ℕ → Result ℕ
⊢ (do
      let ((a, b), (a, b)) ← nestProg
      h (a + b + a + b)) =
    ok 0
-/
#guard_msgs in
example (h : Nat → Result Nat) :
    (do let k ← (do let ((a, b), (c, d)) ← nestProg; ok (a + b + c + d)); h k) = ok 0 := by
  simp only [step_simps]; done

/- Regression: a non-destructuring bind still reassociates as before.-/
/--
error: unsolved goals
h : ℕ → Result ℕ
e : Result ℕ
⊢ (do
      let x ← e
      h (x + 1)) =
    ok 0
-/
#guard_msgs in
example (h : Nat → Result Nat) (e : Result Nat) :
    (do let k ← (do let x ← e; ok (x + 1)); h k) = ok 0 := by
  simp only [step_simps]; done

/- Idempotence: an already-normalized tuple bind is left unchanged (no loop, no
re-introduction of an intermediate variable).-/
/--
error: unsolved goals
h : ℕ → Result ℕ
⊢ (do
      let (a, b) ← pairProg
      h (a + b)) =
    ok 0
-/
#guard_msgs in
example (h : Nat → Result Nat) :
    (do let (a, b) ← pairProg; let k ← ok (a + b); h k) = ok 0 := by
  simp only [step_simps]; done

/-- End-to-end: `step*` discharges a proof over a program that alternates
tuple-destructuring binds with plain binds, exercising the new lemmas through the
`step` tactic's cached simp set. -/
def readPair (xs : List Nat) (i : Nat) : Result (Nat × Nat) :=
  ok (xs.getD i 0, xs.getD (i + 1) 0)

@[step]
theorem readPair_spec (xs : List Nat) (i : Nat) :
    readPair xs i ⦃ x y => x = xs.getD i 0 ∧ y = xs.getD (i + 1) 0 ⦄ := by
  unfold readPair; step*

def prog (xs : List Nat) : Result Nat := do
  let (a, b) ← readPair xs 0
  let c ← ok (a + b)
  let (d, e) ← readPair xs 2
  ok (c + d + e)

example (xs : List Nat) : prog xs ⦃ _ => True ⦄ := by
  unfold prog; step*

end Aeneas.Tactic.Step.Tests.BindAssoc
