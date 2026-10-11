module
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.SubstOutputs

def add1 (n : Nat) : Result Nat := ok (n + 1)

@[step]
theorem add1.spec (n : Nat) : add1 n ⦃ r => r = n + 1 ⦄ := by simp [add1]

def add1' (n : Nat) : Result Nat := ok (n + 1)

@[step]
theorem add1'.spec (n : Nat) : add1' n ⦃ r => n + 1 = r ⦄ := by simp [add1']

/- With `+subst`, the outputs defined by an equation are substituted -/
example (n : Nat) : (do let a ← add1 n; add1 a) ⦃ r => r = n + 2 ⦄ := by
  step +subst
  guard_target =ₛ add1 (n + 1) ⦃ r => r = n + 2 ⦄
  step*

-- The equation is `e = x`
example (n : Nat) : (do let a ← add1' n; add1 a) ⦃ r => r = n + 2 ⦄ := by
  step +subst
  guard_target =ₛ add1 (n + 1) ⦃ r => r = n + 2 ⦄
  step*

end Aeneas.Tactic.Step.Tests.SubstOutputs
