module
import Mathlib.Data.Finset.Basic
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.Membership

def notIn (_ : Finset Nat) (n : Nat) : Result Nat := ok n

@[step]
theorem notIn.spec (S : Finset Nat) (n : Nat) (_ : n ∉ S) : notIn S n ⦃ r => r = n ⦄ := by
  simp [notIn]

attribute [local agrind =] Finset.mem_erase

/- The preprocessing of the preconditions must not unfold `∈`, so that `agrind` can use the
lemmas about membership -/
example (S : Finset Nat) (n : Nat) : notIn (S.erase n) n ⦃ r => r = n ⦄ := by
  step
  simp [*]

end Aeneas.Tactic.Step.Tests.Membership
