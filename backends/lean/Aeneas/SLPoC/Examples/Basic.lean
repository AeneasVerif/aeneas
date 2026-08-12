import Aeneas.SLPoC.Step

namespace Aeneas.SLPoC

open scoped SepLogic

namespace Examples

def add1 (x : Nat) : St Nat :=
  pure (x + 1)

theorem add1.spec (x : Nat) :
    (add1 x) ⦃⇓ y => y = x + 1⦄ := by
  apply triple_pure
  intro h hEmpty
  exact ⟨rfl, hEmpty⟩

def add2 (x : Nat) : St (Nat × Nat) :=
  pure (x + 1, x + 2)

theorem add2.spec (x : Nat) :
    (add2 x) ⦃⇓ (y, z) => y = x + 1 ∧ z = x + 2⦄ := by
  apply triple_pure
  intro h hEmpty
  exact ⟨⟨rfl, rfl⟩, hEmpty⟩

attribute [step] add1.spec add2.spec

def incr_ptr (p : Ptr Nat) : St Unit := do
  let value ← read p
  update p (value + 1)

theorem incr_ptr.spec (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ incr_ptr p ⦃⇓ p ↦ value + 1⦄ := by
  unfold incr_ptr
  sl_step*

attribute [step] incr_ptr.spec

def incr_borrow (value : Nat) : St Nat := do
  let p ← mut_to_raw value
  incr_ptr p
  end_mut_to_raw p

theorem incr_borrow.spec (value : Nat) :
    (incr_borrow value) ⦃⇓ result => result = value + 1⦄ := by
  unfold incr_borrow
  sl_step*

attribute [step] incr_borrow.spec

end Examples

example (p q : Ptr Nat) (x y : Nat) :
    p ↦ x ∗ q ↦ y ⊢ q ↦ y ∗ p ↦ x := by
  sl_frame

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ Examples.incr_ptr p ⦃⇓ p ↦ value + 1⦄ := by
  unfold Examples.incr_ptr
  step* by sl_frame

example (value : Nat) :
    (Examples.incr_borrow value) ⦃⇓ result => result = value + 1⦄ := by
  unfold Examples.incr_borrow Examples.incr_ptr
  step* by sl_frame

example (x : Nat) :
    (do
      let y ← Examples.add1 x
      Examples.add1 y) ⦃⇓ y => y = x + 2⦄ := by
  step* by sl_frame

example (x : Nat) :
    (do
      let (y, _) ← Examples.add2 x
      Examples.add2 y) ⦃⇓ (y, _) => y = x + 2⦄ := by
  step* by sl_frame

def conditionalUpdate (b : Bool) (p : Ptr Nat) (value : Nat) : St Unit :=
  if b then update p (value + 1) else update p (value + 2)

example (b : Bool) (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ conditionalUpdate b p value
      ⦃⇓ p ↦ if b then value + 1 else value + 2⦄ := by
  unfold conditionalUpdate
  step* by sl_frame

end Aeneas.SLPoC
