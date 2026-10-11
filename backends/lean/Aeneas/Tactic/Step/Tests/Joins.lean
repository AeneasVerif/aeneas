module
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.Joins

def add1 (n : Nat) : Result Nat := ok (n + 1)

@[step]
theorem add1.spec (n : Nat) : add1 n ⦃ r => r = n + 1 ⦄ := by simp [add1]

def addN (x y : Nat) : Result Nat := ok (x + y)

@[step]
theorem addN.spec (x y : Nat) : addN x y ⦃ r => r = x + y ⦄ := by simp [addN]

/- The joins whose branches are values are lifted, rather than split: splitting them duplicates
the continuation, and the number of branches would grow exponentially here. -/
def chain (b1 b2 b3 b4 b5 b6 b7 b8 : Bool) (x : Nat) : Result Nat := do
  let y1 ← if b1 then ok 1 else ok 0
  let x1 ← addN x y1
  let y2 ← if b2 then ok 1 else ok 0
  let x2 ← addN x1 y2
  let y3 ← if b3 then ok 1 else ok 0
  let x3 ← addN x2 y3
  let y4 ← if b4 then ok 1 else ok 0
  let x4 ← addN x3 y4
  let y5 ← if b5 then ok 1 else ok 0
  let x5 ← addN x4 y5
  let y6 ← if b6 then ok 1 else ok 0
  let x6 ← addN x5 y6
  let y7 ← if b7 then ok 1 else ok 0
  let x7 ← addN x6 y7
  let y8 ← (if _ : b8 then ok 1 else ok 0)
  addN x7 y8

example (b1 b2 b3 b4 b5 b6 b7 b8 : Bool) (x : Nat) :
    chain b1 b2 b3 b4 b5 b6 b7 b8 x ⦃ r => x ≤ r ⦄ := by
  unfold chain
  step*

inductive Enum where | V0 | V1 | V2

def useEnum (e : Enum) (x : Nat) : Result Nat := do
  let y ← match e with
    | .V0 => ok 0
    | .V1 => ok 1
    | .V2 => ok 2
  let z ← match x with
    | 0 => ok 1
    | _ => ok x
  addN y z

/--
info: Try this:

  [apply]     simp only [step_simps, Aeneas.liftValueJoin]
    let* ⟨ r, r_post ⟩ ← addN.spec
    sorry
-/
#guard_msgs in
example (e : Enum) (x : Nat) : useEnum e x ⦃ r => 0 < r ⦄ := by
  unfold useEnum
  step*?
  subst r_post
  cases e <;> cases x <;> simp

/- The joins whose values depend on the variables bound by the patterns are split: lifting them
would lose the information that the split gives -/
def optionJoin (o : Option Nat) : Result Nat := do
  let y ← match o with
    | none => ok 0
    | some v => ok v
  addN y 1

example (o : Option Nat) : optionJoin o ⦃ r => ∀ v, o = some v → r = v + 1 ⦄ := by
  unfold optionJoin
  step*

/- The joins whose branches have effects are split -/
def branchThenCall (b : Bool) (n : Nat) : Result Nat := do
  let i ← if b then add1 n else ok 0
  let j ← add1 i
  ok (j + n)

example (b : Bool) (n : Nat) : branchThenCall b n ⦃ r => r = (if b then 2 * n + 2 else n + 1) ⦄ := by
  unfold branchThenCall
  step*

def matchThenCall (o : Option Nat) : Result Nat := do
  let x ← match o with
    | none => fail .panic
    | some v => add1 v
  add1 x

example (o : Option Nat) (h : o.isSome) :
    matchThenCall o ⦃ r => ∀ v, o = some v → r = v + 2 ⦄ := by
  unfold matchThenCall
  step*

end Aeneas.Tactic.Step.Tests.Joins
