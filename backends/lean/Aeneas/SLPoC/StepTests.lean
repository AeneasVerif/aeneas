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
    step* by sl_frame

theorem update.spec' {α : Type} {relation : EqOrDisj α}
    (left right : Ptr α) (value : α) :
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

example {α : Type} {relation : Examples.EqOrDisj α}
    (left right : Ptr α) :
    ⦃ Examples.isEqOrDisj left right relation ⦄ read left
      ⦃⇓ result =>
        ⌜result = relation.read⌝ ∗
          Examples.isEqOrDisj left right relation⦄ := by
  cases relation <;>
    simp only [Examples.isEqOrDisj, Examples.EqOrDisj.read] <;>
    step* by sl_frame

example {α : Type} {relation : Examples.EqOrDisj α}
    (left right : Ptr α) (value : α) :
    ⦃ Examples.isEqOrDisj left right relation ⦄ update right value
      ⦃⇓ Examples.isEqOrDisj left right (relation.write value)⦄ := by
  cases relation <;>
    simp only [Examples.isEqOrDisj, Examples.EqOrDisj.write]
  · apply triple_hpure
    intro hEq
    subst right
    step* by sl_frame
  · step* by sl_frame

def conditionalUpdate (b : Bool) (p : Ptr Nat) (value : Nat) : St Unit :=
  if b then update p (value + 1) else update p (value + 2)

example (b : Bool) (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ conditionalUpdate b p value
      ⦃⇓ p ↦ if b then value + 1 else value + 2⦄ := by
  unfold conditionalUpdate
  step* by sl_frame

/-! ## `sl_frame` as an `xsimpl` -/

/-- An existential of the right-hand side is instantiated by the cancellation. -/
example (p : Ptr Nat) (value : Nat) :
    p ↦ value ⊢ iprop(∃ w, ⌜w = value⌝ ∗ p ↦ w) := by
  sl_frame

/-- A pure fact of the left-hand side is available when proving the pure facts
of the right-hand side, even though it is consumed by the entailment. -/
example (p : Ptr Nat) (value w : Nat) :
    iprop(⌜w = value + 1⌝ ∗ p ↦ value) ⊢ iprop(⌜0 < w⌝ ∗ p ↦ value) := by
  sl_frame

/-- An existential of the left-hand side is introduced before the one of the
right-hand side, so the witness may depend on it. -/
example (p : Ptr Nat) :
    iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) ⊢ iprop(∃ m, p ↦ m) := by
  sl_frame

/-- Cancellation happens up to associativity and commutativity. -/
example (p q r : Ptr Nat) (x y z : Nat) :
    iprop((p ↦ x ∗ q ↦ y) ∗ r ↦ z) ⊢ iprop(r ↦ z ∗ (q ↦ y ∗ p ↦ x)) := by
  sl_frame

/-- The pure side-goals are proved *after* the cancellation, so they see the
witness that the cancellation chose. -/
example (p : Ptr Nat) :
    p ↦ 3 ⊢ iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) := by
  sl_frame

/-! ## `sl_pull` -/

/-- `sl_pull` peels the quantifiers and the pure facts of a precondition. -/
example (p : Ptr Nat) :
    ⦃ iprop(∃ n, ⌜n = 1⌝ ∗ p ↦ n) ⦄ Examples.incr_ptr p ⦃⇓ p ↦ 2⦄ := by
  unfold Examples.incr_ptr
  sl_pull n rfl
  step* by sl_frame

/-- Without arguments it peels as much as it can. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ iprop(⌜value = 1⌝ ∗ p ↦ value) ⦄ Examples.incr_ptr p ⦃⇓ p ↦ 2⦄ := by
  unfold Examples.incr_ptr
  sl_pull
  subst_vars
  step* by sl_frame

/-! ## Frame inference

`step` asks `sl_frame` to solve `H ⊢ Hcallee ∗ ?F`.  In that mode nothing may be
extracted from `H`: whatever is not required by the callee has to end up in `?F`,
and `?F` cannot mention anything introduced by the entailment. -/

def touchAny (p : Ptr Nat) : St Unit := do
  let value ← read p
  update p value

theorem touchAny.spec (p : Ptr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchAny p ⦃⇓ iprop(∃ n, p ↦ n)⦄ := by
  unfold touchAny
  sl_pull n
  step* by sl_frame

attribute [step] touchAny.spec

def touchThenSet (p : Ptr Nat) : St Unit := do
  touchAny p
  update p 7

/-- A pure fact that the callee does not need stays available afterwards, even
though the callee's precondition is an existential.  `step` pulls the
existential the callee gives back on its own. -/
example (p : Ptr Nat) (x : Nat) :
    ⦃ iprop(⌜x = 5⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃⇓ iprop(⌜x = 5⌝ ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step* by sl_frame

/-- A framed-out existential stays intact: instantiating it here would put a
variable out of the scope of the frame metavariable. -/
example (p q : Ptr Nat) (x : Nat) :
    ⦃ iprop(hexists (fun n => q ↦ n) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃⇓ iprop(hexists (fun n => q ↦ n) ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step* by sl_frame

/-- The callee's precondition may be owned as one opaque existential: the frame
is then `emp`, and the existential must *not* be opened. -/
example (p : Ptr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchThenSet p ⦃⇓ p ↦ 7⦄ := by
  unfold touchThenSet
  step* by sl_frame

/-- `sl_frame` leaves the other goals of the proof alone. -/
example (p : Ptr Nat) (x : Nat) : (p ↦ x ⊢ p ↦ x) ∧ 1 = 1 := by
  refine ⟨?_, ?_⟩
  · sl_frame
  · rfl

/-! ## The shape of the goal `step` hands back -/

def readThenWrite (p : Ptr Nat) : St Unit := do
  let value ← read p
  update p (value + 1)

/-- The equation `read.spec` returns is substituted, the `Unit` output of
`update` introduces no binder, and the `∗ emp` of an empty frame is gone. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readThenWrite p ⦃⇓ p ↦ value + 1⦄ := by
  unfold readThenWrite
  step by sl_frame
  guard_target =
    triple iprop(p ↦ value) (update p (value + 1)) (fun _ => iprop(p ↦ value + 1))
  step* by sl_frame

/-! ## Terminal `pure` -/

/-- `step*` walks through the `return` of a function. -/
def readAndFree (p : Ptr Nat) : St Nat := do
  let v ← read p
  free p
  pure (v + 1)

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readAndFree p ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold readAndFree
  step* by sl_frame

/-! ## The tactics ported from Separation Logic Foundations

`SLTactics.lean` ports SLF's magic wand, ramified frame rule, `xsimpl`, `xpull`,
`xchange`, `xval` and `xapp`. -/

-- wand laws
example (H1 H2 : SLProp) : H1 ∗ (H1 -∗ H2) ⊢ H2 := hwand_cancel H1 H2
example (Q1 Q2 : SLPost Nat) : Q1 ∗+ (Q1 -∗∗ Q2) ⊢+ Q2 := qwand_cancel Q1 Q2

-- sl_xpull: SLF's canonical example where the RHS witness depends on the LHS one
example (p : Ptr Nat) :
    iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) ⊢ iprop(∃ m, p ↦ (m + 1)) := by
  sl_xpull
  -- `sl_xpull` names the variables it introduces `x` and the facts `h`.
  refine himpl_hexists_r (x - 1) ?_
  rw [show x - 1 + 1 = x by omega]
  sl_xsimpl

-- sl_xchange with an entailment
theorem cellPair (p q : Ptr Nat) : iprop(p ↦ 1 ∗ q ↦ 2) ⊢ iprop(∃ n, p ↦ n ∗ q ↦ 2) :=
  himpl_hexists_r 1 (himpl_refl _)

example (p q r : Ptr Nat) :
    iprop(r ↦ 0 ∗ (p ↦ 1 ∗ q ↦ 2)) ⊢ iprop(∃ n, r ↦ 0 ∗ (p ↦ n ∗ q ↦ 2)) := by
  sl_xchange (cellPair p q)
  sl_xsimpl

-- sl_xchange with an equality, on a triple precondition
theorem swapEq (p q : Ptr Nat) : iprop(p ↦ 1 ∗ q ↦ 2) = iprop(q ↦ 2 ∗ p ↦ 1) :=
  hstar_comm_eq _ _

example (p q : Ptr Nat) :
    ⦃ iprop((p ↦ 1 ∗ q ↦ 2) ∗ emp) ⦄ Examples.incr_ptr q ⦃⇓ iprop(q ↦ 3 ∗ p ↦ 1)⦄ := by
  unfold Examples.incr_ptr
  sl_xchange (swapEq p q)
  step* by sl_frame

-- sl_xval
example (p : Ptr Nat) : ⦃ p ↦ 1 ⦄ (pure 5 : St Nat) ⦃⇓ v => ⌜v = 5⌝ ∗ p ↦ 1⦄ := by
  sl_xval
  sl_xsimpl

-- sl_xapp: terminal call through the ramified frame rule
example (p q : Ptr Nat) (x : Nat) :
    ⦃ iprop(p ↦ x ∗ q ↦ 9) ⦄ Examples.incr_ptr p ⦃⇓ iprop(q ↦ 9 ∗ p ↦ (x + 1))⦄ := by
  sl_xapp (Examples.incr_ptr.spec p x)


/-! ### The ramified frame rule in `step` -/

/-- `sl_step` finishes a terminal call: its obligation is the *main* goal, which
`step`'s own `by` tactic does not reach. -/
example (p q : Ptr Nat) :
    ⦃ iprop(p ↦ 3 ∗ q ↦ 7) ⦄ read p ⦃⇓ r => iprop(⌜r = 3⌝ ∗ (p ↦ 3 ∗ q ↦ 7))⦄ := by
  sl_step

/-- What the ramified frame rule buys: the precondition of the *caller* may be an
existential, and `sl_frame` is free to open it because there is no frame
metavariable to keep it out of.  The explicit frame rule cannot do this. -/
example (q : Ptr Nat) :
    ⦃ hexists (fun n => iprop(q ↦ n)) ⦄ alloc 5
      ⦃⇓ r => iprop(r ↦ 5 ∗ hexists (fun n => iprop(q ↦ n)))⦄ := by
  step* by sl_frame

/-- `sl_xpull` must refuse a frame-inference goal: introducing the existential of
the left-hand side would put a variable out of the scope of the frame `?F`.  The
`hPre` premise of the bind rule is exactly such a goal. -/
example (p q : Ptr Nat) (x : Nat) :
    ⦃ iprop(hexists (fun n => iprop(q ↦ n)) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃⇓ iprop(hexists (fun n => iprop(q ↦ n)) ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  apply triple_step_bind (touchAny p) _ (touchAny.spec p)
  case hPre =>
    fail_if_success sl_xpull
    sl_frame
  case hNext =>
    intro _ _
    sl_pull
    step* by sl_frame

/-- A wand on the right is cancelled against an identical one on the left before
being used to absorb the residual resources. -/
example (Q₁ Q₂ : SLPost Nat) (H : SLProp) :
    iprop(H ∗ (Q₁ -∗∗ Q₂)) ⊢ iprop(H ∗ (Q₁ -∗∗ Q₂)) := by
  sl_frame

/-- `sl_step` only touches the goals `step` produces. -/
example (p q : Ptr Nat) :
    (⦃ iprop(p ↦ 3 ∗ q ↦ 7) ⦄ read p ⦃⇓ r => iprop(⌜r = 3⌝ ∗ (p ↦ 3 ∗ q ↦ 7))⦄)
    ∧ (iprop(p ↦ 3 ∗ q ↦ 7) ⊢ iprop(q ↦ 7 ∗ p ↦ 3)) := by
  refine ⟨?_, ?_⟩
  sl_step
  sl_frame

end Aeneas.SLPoC
