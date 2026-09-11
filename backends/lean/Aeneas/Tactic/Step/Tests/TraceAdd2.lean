import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.TraceAdd2

def add2 (x : Nat) : Result (Nat × Nat) :=
  ok (x + 1, x + 2)

@[step]
theorem add2_spec (x : Nat) :
    add2 x ⦃ y z => y = x + 1 ∧ z = x + 2 ⦄ := by
  simp [add2]

set_option trace.Step true

example (x : Nat) :
    (do
      let (_, _) ← add2 x
      add2 x) ⦃ y _ => y = x + 1 ⦄ := by
  step
  step
  omega

end Aeneas.Tactic.Step.Tests.TraceAdd2
