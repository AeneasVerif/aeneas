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

def incr_ptr (p : Ref Nat) : St Unit := do
  let value ← read p
  update p (value + 1)

theorem incr_ptr.spec (p : Ref Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ incr_ptr p ⦃⇓ p ↦ value + 1⦄ := by
  unfold incr_ptr
  step* by sl_frame

attribute [step] incr_ptr.spec

def incr_borrow (value : Nat) : St Nat := do
  let p ← mut_to_raw value
  incr_ptr p
  end_mut_to_raw p

theorem incr_borrow.spec (value : Nat) :
    (incr_borrow value) ⦃⇓ result => result = value + 1⦄ := by
  unfold incr_borrow
  step* by sl_frame

attribute [step] incr_borrow.spec

inductive EqOrDisj (α : Type) where
  | equal (value : α)
  | disjoint (leftValue rightValue : α)

def isEqOrDisj {α : Type} (left right : Ref α)
    (relation : EqOrDisj α) : SLProp :=
  match relation with
  | .equal value => iprop(⌜left = right⌝ ∗ left ↦ value)
  | .disjoint leftValue rightValue =>
      iprop(left ↦ leftValue ∗ right ↦ rightValue)

def EqOrDisj.read {α : Type} (relation : EqOrDisj α) : α :=
  match relation with
  | .equal value => value
  | .disjoint leftValue _ => leftValue

def EqOrDisj.write {α : Type} (relation : EqOrDisj α)
    (value : α) : EqOrDisj α :=
  match relation with
  | .equal _ => .equal value
  | .disjoint leftValue _ => .disjoint leftValue value

theorem read.spec' {α : Type} {relation : EqOrDisj α}
    (left right : Ref α) :
    ⦃ isEqOrDisj left right relation ⦄ read left
      ⦃⇓ result =>
        ⌜result = relation.read⌝ ∗ isEqOrDisj left right relation⦄ := by
  cases relation <;>
    simp only [isEqOrDisj, EqOrDisj.read] <;>
    step* by sl_frame

theorem update.spec' {α : Type} {relation : EqOrDisj α}
    (left right : Ref α) (value : α) :
    ⦃ isEqOrDisj left right relation ⦄ update right value
      ⦃⇓ isEqOrDisj left right (relation.write value)⦄ := by
  cases relation <;>
    simp only [isEqOrDisj, EqOrDisj.write]
  · apply triple_hpure
    intro hEq
    subst right
    step* by sl_frame
  · step* by sl_frame

end Examples

example (p q : Ref Nat) (x y : Nat) :
    p ↦ x ∗ q ↦ y ⊢ q ↦ y ∗ p ↦ x := by
  sl_frame

example (p : Ref Nat) (value : Nat) :
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

example {α : Type} {relation : Examples.EqOrDisj α}
    (left right : Ref α) :
    ⦃ Examples.isEqOrDisj left right relation ⦄ read left
      ⦃⇓ result =>
        ⌜result = relation.read⌝ ∗
          Examples.isEqOrDisj left right relation⦄ := by
  cases relation <;>
    simp only [Examples.isEqOrDisj, Examples.EqOrDisj.read] <;>
    step* by sl_frame

example {α : Type} {relation : Examples.EqOrDisj α}
    (left right : Ref α) (value : α) :
    ⦃ Examples.isEqOrDisj left right relation ⦄ update right value
      ⦃⇓ Examples.isEqOrDisj left right (relation.write value)⦄ := by
  cases relation <;>
    simp only [Examples.isEqOrDisj, Examples.EqOrDisj.write]
  · apply triple_hpure
    intro hEq
    subst right
    step* by sl_frame
  · step* by sl_frame

def conditionalUpdate (b : Bool) (p : Ref Nat) (value : Nat) : St Unit :=
  if b then update p (value + 1) else update p (value + 2)

example (b : Bool) (p : Ref Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ conditionalUpdate b p value
      ⦃⇓ p ↦ if b then value + 1 else value + 2⦄ := by
  unfold conditionalUpdate
  step* by sl_frame

end Aeneas.SLPoC
