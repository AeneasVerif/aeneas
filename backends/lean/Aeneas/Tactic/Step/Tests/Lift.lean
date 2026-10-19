module
import Aeneas.Std
import Aeneas.Tactic.Step

/-! # Stepping through lifted calls

In code of level `n` (`Result%n`), Lean lifts the calls to code of a lower level (`liftM`). `step`
steps through them with the spec of the call. -/

open Aeneas
open Std Result WP

namespace Aeneas.Tactic.Step.Tests.Lift

/-- Level 2: a level-0 call lifted twice. -/
def add2 (x y : U32) : Result%2 U32 := do
  let z ← x + y
  ok z

example (x y : U32) (h : x.val + y.val ≤ U32.max) : add2 x y ⦃ z => z.val = x.val + y.val ⦄ := by
  unfold add2; step*

/-- A level-0 function with a `@[step]` spec, called at level 1. -/
def incr (x : U32) : Result U32 := x + 1#u32

@[step] theorem incr_spec (x : U32) (h : x.val < U32.max) : incr x ⦃ y => y.val = x.val + 1 ⦄ := by
  unfold incr; step*

def incrTwice (x : U32) : Result%1 U32 := do
  let y ← incr x
  incr y

example (x : U32) (h : x.val + 1 < U32.max) : incrTwice x ⦃ y => y.val = x.val + 2 ⦄ := by
  unfold incrTwice; step*

/-- `step with` a level-0 spec on a lifted call. -/
example (x : U32) (h : x.val + 1 < U32.max) : incrTwice x ⦃ y => y.val = x.val + 2 ⦄ := by
  unfold incrTwice
  step with incr_spec
  step with incr_spec
  scalar_tac

/-- A closure of level 0, called at level 1: its spec is an assumption. -/
def callF (f : Nat → Result Nat) (x : Nat) : Result%1 Nat := do
  let y ← f x
  massert (y > 0)
  ok y

example (f : Nat → Result Nat) (x : Nat) (hf : ∀ y, f y ⦃ r => r = y + 1 ⦄) :
    callF f x ⦃ r => r = x + 1 ⦄ := by
  unfold callF; step*

/-- Partial correctness through the lift (`dspec`). -/
example (f : Nat → Result Nat) (x : Nat) (hf : ∀ y, f y ⦃ r => r = y + 1 ⦄) :
    callF f x ⦃ r => r = x + 1 ⦄div := by
  unfold callF; step*

/-- `simp` computes through the lift. -/
example (x : Nat) : (do let y ← (ok x : Result Nat); ok (y + 1) : Result%2 Nat) = ok (x + 1) := by
  simp

end Aeneas.Tactic.Step.Tests.Lift
