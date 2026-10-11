module
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.NestedBinds

def add1 (n : Nat) : Result Nat := ok (n + 1)

@[step]
theorem add1.spec (n : Nat) : add1 n ⦃ r => r = n + 1 ⦄ := by simp [add1]

def pairOf (n : Nat) : Result (Nat × Nat) := ok (n, n + 1)

@[step]
theorem pairOf.spec (n : Nat) : pairOf n ⦃ a b => a = n ∧ b = n + 1 ⦄ := by simp [pairOf]

/- The bind of a nested block which destructures a tuple is flattened, and the outputs of a
continuation which destructures its input are destructured -/
def nestedPair (n : Nat) : Result Nat := do
  let x ← (do let (a, b) ← pairOf n; let c ← add1 a; ok (c, b))
  let (c, b) := x
  ok (c + b)

example (n : Nat) : nestedPair n ⦃ r => r = 2 * n + 2 ⦄ := by
  unfold nestedPair
  step as ⟨a, b⟩
  guard_hyp a : Nat
  guard_hyp b : Nat
  step*

/- The continuation destructures its input, and also uses it as a whole -/
def reuse (n : Nat) : Result Nat := do
  let x ← pairOf n
  let (a, b) := x
  ok (a + b + x.1)

example (n : Nat) : reuse n ⦃ r => r = 3 * n + 1 ⦄ := by
  unfold reuse
  step*

end Aeneas.Tactic.Step.Tests.NestedBinds
