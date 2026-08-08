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

/-! ## `sl_frame` as an `xsimpl` -/

/-- An existential of the right-hand side is instantiated by the cancellation. -/
example (p : Ref Nat) (value : Nat) :
    p ↦ value ⊢ iprop(∃ w, ⌜w = value⌝ ∗ p ↦ w) := by
  sl_frame

/-- A pure fact of the left-hand side is available when proving the pure facts
of the right-hand side, even though it is consumed by the entailment. -/
example (p : Ref Nat) (value w : Nat) :
    iprop(⌜w = value + 1⌝ ∗ p ↦ value) ⊢ iprop(⌜0 < w⌝ ∗ p ↦ value) := by
  sl_frame

/-- An existential of the left-hand side is introduced before the one of the
right-hand side, so the witness may depend on it. -/
example (p : Ref Nat) :
    iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) ⊢ iprop(∃ m, p ↦ m) := by
  sl_frame

/-- Cancellation happens up to associativity and commutativity. -/
example (p q r : Ref Nat) (x y z : Nat) :
    iprop((p ↦ x ∗ q ↦ y) ∗ r ↦ z) ⊢ iprop(r ↦ z ∗ (q ↦ y ∗ p ↦ x)) := by
  sl_frame

/-- The pure side-goals are proved *after* the cancellation, so they see the
witness that the cancellation chose. -/
example (p : Ref Nat) :
    p ↦ 3 ⊢ iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) := by
  sl_frame

/-! ## `sl_pull` -/

/-- `sl_pull` peels the quantifiers and the pure facts of a precondition. -/
example (p : Ref Nat) :
    ⦃ iprop(∃ n, ⌜n = 1⌝ ∗ p ↦ n) ⦄ Examples.incr_ptr p ⦃⇓ p ↦ 2⦄ := by
  unfold Examples.incr_ptr
  sl_pull n rfl
  step* by sl_frame

/-- Without arguments it peels as much as it can. -/
example (p : Ref Nat) (value : Nat) :
    ⦃ iprop(⌜value = 1⌝ ∗ p ↦ value) ⦄ Examples.incr_ptr p ⦃⇓ p ↦ 2⦄ := by
  unfold Examples.incr_ptr
  sl_pull
  subst_vars
  step* by sl_frame

/-! ## Frame inference

`step` asks `sl_frame` to solve `H ⊢ Hcallee ∗ ?F`.  In that mode nothing may be
extracted from `H`: whatever is not required by the callee has to end up in `?F`,
and `?F` cannot mention anything introduced by the entailment. -/

def touchAny (p : Ref Nat) : St Unit := do
  let value ← read p
  update p value

theorem touchAny.spec (p : Ref Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchAny p ⦃⇓ iprop(∃ n, p ↦ n)⦄ := by
  unfold touchAny
  sl_pull n
  step* by sl_frame

attribute [step] touchAny.spec

def touchThenSet (p : Ref Nat) : St Unit := do
  touchAny p
  update p 7

/-- A pure fact that the callee does not need stays available afterwards, even
though the callee's precondition is an existential. -/
example (p : Ref Nat) (x : Nat) :
    ⦃ iprop(⌜x = 5⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃⇓ iprop(⌜x = 5⌝ ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step by sl_frame
  -- SLF's advice: `xpull` the existential the callee gave back before going on,
  -- otherwise the witness would have to escape the scope of the next frame.
  sl_pull n
  step* by sl_frame

/-- A framed-out existential stays intact: instantiating it here would put a
variable out of the scope of the frame metavariable. -/
example (p q : Ref Nat) (x : Nat) :
    ⦃ iprop(hexists (fun n => q ↦ n) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃⇓ iprop(hexists (fun n => q ↦ n) ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step by sl_frame
  sl_pull
  step* by sl_frame

/-- The callee's precondition may be owned as one opaque existential: the frame
is then `emp`, and the existential must *not* be opened. -/
example (p : Ref Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchThenSet p ⦃⇓ p ↦ 7⦄ := by
  unfold touchThenSet
  step by sl_frame
  sl_pull
  step* by sl_frame

/-- `sl_frame` leaves the other goals of the proof alone. -/
example (p : Ref Nat) (x : Nat) : (p ↦ x ⊢ p ↦ x) ∧ 1 = 1 := by
  refine ⟨?_, ?_⟩
  · sl_frame
  · rfl

/-! ## Terminal `pure` -/

/-- `step*` walks through the `return` of a function. -/
def readAndFree (p : Ref Nat) : St Nat := do
  let v ← read p
  free p
  pure (v + 1)

example (p : Ref Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readAndFree p ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold readAndFree
  step* by sl_frame

end Aeneas.SLPoC
