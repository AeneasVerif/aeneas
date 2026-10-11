module
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.StepWithUnfold

def add1 (n : Nat) : Result Nat := ok (n + 1)

@[step]
theorem add1.spec (n : Nat) : add1 n ⦃ r => r = n + 1 ⦄ := by simp [add1]

/- `step with` matches the program of the given theorem up to unfolding -/
example (n : Nat) : add1 ([n].headD 0) ⦃ r => r = n + 1 ⦄ := by
  step with add1.spec n
  simp [*]

/- `step with` uses a specification of the whole program, which is the body of a definition -/
def addTwo (n : Nat) : Result Nat := do
  let a ← add1 n
  add1 a

theorem addTwo.spec (n : Nat) : addTwo n ⦃ r => r = n + 2 ⦄ := by
  unfold addTwo
  step*

example (n : Nat) : (do let a ← add1 n; add1 a) ⦃ r => r = n + 2 ⦄ := by
  step with addTwo.spec n
  simp [*]

/- A theorem about a different call is rejected -/
def add1' (n : Nat) : Result Nat := ok (n + 1)

example : (do let a ← add1' 3; ok a) ⦃ r => r = 4 ⦄ := by
  fail_if_success step with add1.spec 7
  simp [add1']

end Aeneas.Tactic.Step.Tests.StepWithUnfold
