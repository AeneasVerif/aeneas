module
import Aeneas.Tactic.Step
public meta import Lean
public meta import Aeneas.Tactic.Step
import Aeneas.Tactic.Solver.ScalarTac

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.IntroRecursion

def quadruple (n : Nat) : Result (Nat × Nat × Nat × Nat) :=
  ok (n, n, n, n)

@[local step]
theorem quadruple_spec (n : Nat) :
    quadruple n ⦃ a b c d => a = n ∧ b = n ∧ c = n ∧ d = n ⦄ := by
  simp [quadruple, Aeneas.Std.WP.uncurry']

def countdown (n : Nat) : Result Nat := do
  if n = 0 then
    ok 0
  else
    let (a, _, _, _) ← quadruple (n - 1)
    let (b, _, _, _) ← quadruple a
    let (c, _, _, _) ← quadruple b
    let (d, _, _, _) ← quadruple c
    let (e, _, _, _) ← quadruple d
    let (f, _, _, _) ← quadruple e
    let (g, _, _, _) ← quadruple f
    let (h, _, _, _) ← quadruple g
    countdown h
partial_fixpoint

elab "check_decreasing" : tactic => Lean.Elab.Tactic.withMainContext do
  unless (← Lean.Elab.Tactic.getGoals).length == 1 do
    throwError "Output normalization duplicated the recursive call"
  for decl in ← Lean.getLCtx do
    if (decl.type.find? (·.isConstOf ``Aeneas.Std.WP.uncurry')).isSome then
      throwError "An unsplit tuple postcondition leaked into the termination context"
  Lean.Elab.Tactic.evalTactic (← `(tactic| agrind))

set_option maxHeartbeats 200000 in
@[local step]
theorem countdown_spec (n : Nat) : countdown n ⦃ out => out = 0 ⦄ := by
  unfold countdown
  split
  · simp
  · step*
termination_by n
decreasing_by check_decreasing

structure Cursor where
  start : Nat
  stop : Nat

def advance (iter : Cursor) : Result (Bool × Cursor) :=
  ok (true, { iter with start := iter.start + 1 })

@[local step]
theorem advance_spec (iter : Cursor) :
    advance iter ⦃ b next => b = true ∧ next.start = iter.start + 1 ∧ next.stop = iter.stop ⦄ := by
  simp [advance, Aeneas.Std.WP.uncurry']

def countRange (iter : Cursor) : Result Nat := do
  if iter.start < iter.stop then
    let (_, next) ← advance iter
    countRange next
  else
    ok iter.stop
partial_fixpoint

@[local step]
theorem countRange_spec (iter : Cursor) (h : iter.start ≤ iter.stop) :
    countRange iter ⦃ out => out = iter.stop ∧ h = h ⦄ := by
  unfold countRange
  split
  · step as ⟨b, next, hb, hStart, hEnd⟩
    step*
  · simp
termination_by iter.stop - iter.start
decreasing_by rw [hEnd, hStart]; scalar_tac

end Aeneas.Tactic.Step.Tests.IntroRecursion
