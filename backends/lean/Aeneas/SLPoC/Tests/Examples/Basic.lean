import Aeneas.SLPoC.MutableData.Ptr

namespace Aeneas.SepLogic

open Aeneas.Std (Heap Result)


namespace Examples

def add1 (x : Nat) : Result Nat :=
  pure (x + 1)

@[step]
theorem add1.spec (x : Nat) :
    (add1 x) ⦃⇓ y => y = x + 1⦄ := by
  unfold add1
  step*

def add2 (x : Nat) : Result (Nat × Nat) :=
  pure (x + 1, x + 2)

@[step]
theorem add2.spec (x : Nat) :
    (add2 x) ⦃⇓ (y, z) => y = x + 1 ∧ z = x + 2⦄ := by
  unfold add2
  step*

def incr_ptr (p : Ptr Nat) : Result Unit := do
  let value ← read p
  update p (value + 1)

@[step]
theorem incr_ptr.spec (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ incr_ptr p ⦃⇓ p ↦ value + 1⦄ := by
  unfold incr_ptr
  step*

def incr_borrow (value : Nat) : Result Nat := do
  let p ← mut_to_raw value
  incr_ptr p
  end_mut_to_raw p

@[step]
theorem incr_borrow.spec (value : Nat) :
    ⦃ emp ⦄ incr_borrow value ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold incr_borrow
  step*

end Examples

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ Examples.incr_ptr p ⦃⇓ p ↦ value + 1⦄ := by
  step*

example (value : Nat) :
    ⦃ emp ⦄ Examples.incr_borrow value ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  step*

example (x : Nat) :
    (do
      let y ← Examples.add1 x
      Examples.add1 y) ⦃⇓ y => y = x + 2⦄ := by
  step*

example (x : Nat) :
    (do
      let (y, _) ← Examples.add2 x
      Examples.add2 y) ⦃⇓ (y, _) => y = x + 2⦄ := by
  step*

def conditionalUpdate (b : Bool) (p : Ptr Nat) (value : Nat) : Result Unit :=
  if b then update p (value + 1) else update p (value + 2)

example (b : Bool) (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ conditionalUpdate b p value
      ⦃⇓ p ↦ if b then value + 1 else value + 2⦄ := by
  unfold conditionalUpdate
  step*

end Aeneas.SepLogic
