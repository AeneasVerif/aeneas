import Aeneas.Std.Slice
import Aeneas.Tactic.Step
import Aeneas.Do

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.UncurryBind

/-- A toy "indexed read with a setter" that returns a pair, mirroring
    `Array.index_mut_usize`. -/
def readPair (xs : List Nat) (i : Nat) : Result (Nat × (Nat → List Nat)) :=
  ok (xs.getD i 0, fun y => xs.set i y)

@[step]
theorem readPair_spec (xs : List Nat) (i : Nat) :
    readPair xs i ⦃ x y => x = xs.getD i 0 ∧ y = (fun y => xs.set i y) ⦄ := by
  unfold readPair; simp [WP.spec_ok, WP.predn]

def readSingle (xs : List Nat) (i : Nat) : Result Nat :=
  ok (xs.getD i 0)

@[step]
theorem readSingle_spec (xs : List Nat) (i : Nat) :
    readSingle xs i ⦃ x => x = xs.getD i 0 ⦄ := by
  unfold readSingle; simp [WP.spec_ok]

/-- a `do` block alternating tuple-destructuring binds with single binds.
  Before the fix to `step*`, this was causing some issues -/
def prog (xs : List Nat) : Result (List Nat × Nat) := do
  let (a, setA) ← readPair xs 0
  let b ← readSingle xs 1
  let (c, setC) ← readPair (setA b) 2
  let d ← readSingle (setC c) 3
  ok (setC c, a + b + c + d)

-- `step*` should finish this proof off in one step, the new `do` elab use of
-- `uncurry` was preventing that 
example (xs : List Nat) :
    prog xs ⦃ _ => True ⦄ := by
  unfold prog
  step*

end Aeneas.Tactic.Step.Tests.UncurryBind
