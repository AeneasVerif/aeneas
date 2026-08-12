import Aeneas.SLPoC.Step

namespace Aeneas.SLPoC

open scoped SepLogic

namespace Examples

inductive EqOrDisj (α : Type) where
  | equal (value : α)
  | disjoint (leftValue rightValue : α)

def isEqOrDisj {α : Type} (left right : Ptr α)
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
    (left right : Ptr α) :
    ⦃ isEqOrDisj left right relation ⦄ read left
      ⦃⇓ result =>
        ⌜result = relation.read⌝ ∗ isEqOrDisj left right relation⦄ := by
  cases relation <;>
    simp only [isEqOrDisj, EqOrDisj.read] <;>
    sl_step*

theorem update.spec' {α : Type} {relation : EqOrDisj α}
    (left right : Ptr α) (value : α) :
    ⦃ isEqOrDisj left right relation ⦄ update right value
      ⦃⇓ isEqOrDisj left right (relation.write value)⦄ := by
  cases relation <;>
    simp only [isEqOrDisj, EqOrDisj.write] <;>
    sl_step*

end Examples

example {α : Type} {relation : Examples.EqOrDisj α}
    (left right : Ptr α) :
    ⦃ Examples.isEqOrDisj left right relation ⦄ read left
      ⦃⇓ result =>
        ⌜result = relation.read⌝ ∗
          Examples.isEqOrDisj left right relation⦄ := by
  cases relation <;>
    simp only [Examples.isEqOrDisj, Examples.EqOrDisj.read] <;>
    sl_step*

example {α : Type} {relation : Examples.EqOrDisj α}
    (left right : Ptr α) (value : α) :
    ⦃ Examples.isEqOrDisj left right relation ⦄ update right value
      ⦃⇓ Examples.isEqOrDisj left right (relation.write value)⦄ := by
  cases relation <;>
    simp only [Examples.isEqOrDisj, Examples.EqOrDisj.write] <;>
    sl_step*

end Aeneas.SLPoC
