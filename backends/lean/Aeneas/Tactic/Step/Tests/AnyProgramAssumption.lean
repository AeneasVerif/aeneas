module
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.AnyProgramAssumption

def add1 (n : Nat) : Result Nat := ok (n + 1)

@[step]
theorem add1.spec (n : Nat) : add1 n ⦃ r => r = n + 1 ⦄ := by simp [add1]

/- A local assumption which applies to any program is not used as a specification -/
example (P : Prop) (_hpre : ∀ Q (prog : Result Nat), P → prog ⦃ Q ⦄) (n : Nat) :
    add1 n ⦃ r => r = n + 1 ⦄ := by
  step*

end Aeneas.Tactic.Step.Tests.AnyProgramAssumption
