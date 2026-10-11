module
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.LocalFunctions

def add1 (n : Nat) : Result Nat := ok (n + 1)

@[step]
theorem add1.spec (n : Nat) : add1 n ⦃ r => r = n + 1 ⦄ := by simp [add1]

/- `step` unfolds the local functions defined by an equation, such as the backward functions -/
def withBack (n : Nat) : Result (Nat × (Nat → Result Nat)) := ok (n, fun m => add1 m)

@[step]
theorem withBack.spec (n : Nat) :
    withBack n ⦃ a back => a = n ∧ back = fun m => add1 m ⦄ := by simp [withBack]

def callBack (n : Nat) : Result Nat := do
  let (a, back) ← withBack n
  back a

example (n : Nat) : callBack n ⦃ r => r = n + 1 ⦄ := by
  unfold callBack
  step*

-- A backward value (of type `Result`)
def withBack0 (n : Nat) : Result (Nat × Result Nat) := ok (n, add1 n)

@[step]
theorem withBack0.spec (n : Nat) :
    withBack0 n ⦃ a back => a = n ∧ back = add1 n ⦄ := by simp [withBack0]

def callBack0 (n : Nat) : Result Nat := do
  let (a, back) ← withBack0 n
  let b ← back
  ok (a + b)

example (n : Nat) : callBack0 n ⦃ r => r = 2 * n + 1 ⦄ := by
  unfold callBack0
  step*

-- A closure
example (f : Nat → Result Nat) (hf : ∀ x, f x = add1 x) (n : Nat) :
    (do let a ← f n; add1 a) ⦃ r => r = n + 2 ⦄ := by
  step*

-- An equation which holds only under a condition is not used
example (f : Nat → Result Nat) (hf : ∀ x, x > 0 → f x = add1 x) (n : Nat) (hn : n > 0) :
    (do let a ← f n; add1 a) ⦃ r => r = n + 2 ⦄ := by
  fail_if_success step
  rw [hf n hn]
  step*

/- We do not unfold if the specification we then apply does not determine all its outputs: we
stop where we stopped before -/
def touch (n : Nat) : Result Nat := ok n

-- `m` is not determined by the call
@[step]
theorem touch.spec (n m : Nat) : touch n ⦃ r => r = n ∧ r + m = n + m ⦄ := by simp [touch]

def withTouch (n : Nat) : Result (Nat × Result Nat) := ok (n, touch n)

@[step]
theorem withTouch.spec (n : Nat) :
    withTouch n ⦃ a back => a = n ∧ back = touch n ⦄ := by simp [withTouch]

def callTouch (n : Nat) : Result Nat := do
  let (_, back) ← withTouch n
  back

example (n : Nat) : callTouch n ⦃ r => r = n ⦄ := by
  unfold callTouch
  step*
  rw [back_post]
  step with touch.spec _ 0
  simp [*]

end Aeneas.Tactic.Step.Tests.LocalFunctions
