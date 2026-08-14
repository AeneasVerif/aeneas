import Aeneas.SLPoC.Examples.Basic

namespace Aeneas.SLPoC

open scoped SepLogic

/-! ## `sl_frame` as an `xsimpl` -/

example (P Q : SLProp) : emp ⊢ (P ∗ (P -∗ Q)) -∗ Q := by
  apply hwand_intro
  sl_xchange (hwand_cancel P Q)
  sl_frame

example (p q : Ptr Nat) (x y : Nat) :
    p ↦ x ∗ q ↦ y ⊢ q ↦ y ∗ p ↦ x := by
  sl_frame

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

/-- `sl_step` cannot open a leading existential before frame inference.
Pulling only its witness exposes the pure fact for `sl_step`'s `sl_pull_keep`. -/
example (p : Ptr Nat) :
    ⦃ iprop(∃ n, ⌜n = 1⌝ ∗ p ↦ n) ⦄ Examples.incr_ptr p ⦃⇓ p ↦ 2⦄ := by
  unfold Examples.incr_ptr
  fail_if_success sl_step
  sl_pull n
  sl_step*

/-- Without arguments it peels as much as it can. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ iprop(⌜value = 1⌝ ∗ p ↦ value) ⦄ Examples.incr_ptr p ⦃⇓ p ↦ 2⦄ := by
  unfold Examples.incr_ptr
  sl_pull
  sl_step*

/-! ## `sl_pull_keep`

Unlike `sl_pull`, this copies the pure facts of the precondition into the local
context instead of consuming them, so the assertion stays available to the
framing of the later steps.  `sl_step` runs it on every step. -/

/-- The pointer passed to the callee is reducible to the owned pointer only
through a pure fact in the precondition.  `sl_step` copies the fact into the
context while preserving it for the postcondition. -/
example (p q : Ptr Nat) :
    ⦃ iprop(⌜q = p⌝ ∗ p ↦ 1) ⦄ Examples.incr_ptr q ⦃⇓ iprop(⌜q = p⌝ ∗ p ↦ 2)⦄ := by
  unfold Examples.incr_ptr
  sl_step*

/-- `sl_pull_keep` leaves the precondition untouched: the fact is needed both in
the context (to rewrite the cell) and in the assertion (for the postcondition). -/
example (p : Ptr Nat) (n : Nat) :
    ⦃ iprop(⌜n = 1⌝ ∗ p ↦ n) ⦄ pure () ⦃⇓ iprop(⌜n = 1⌝ ∗ p ↦ 1)⦄ := by
  sl_pull_keep
  sl_pure
  sl_frame

/-- `sl_pure` reduces match/let noise around a terminal return. -/
example (n : Nat) :
    ⦃ emp ⦄ (Prod.rec (fun value _ => pure value) (n, true) : St Nat)
      ⦃⇓ result => ⌜result = n⌝⦄ := by
  sl_pure
  sl_frame

def namedPure (n : Nat) : St Nat :=
  pure n

@[step]
theorem namedPure.spec (n : Nat) :
    ⦃ emp ⦄ namedPure n ⦃⇓ result => ⌜result = n⌝⦄ := by
  unfold namedPure
  sl_pure
  sl_frame

/-- The direct terminal rule does not unfold named wrappers and bypass their
registered specifications. -/
example (n : Nat) :
    ⦃ emp ⦄ namedPure n ⦃⇓ result => ⌜result = n⌝⦄ := by
  fail_if_success sl_pure
  sl_step

/-- Normalization inside `sl_pure` stays focused on its original goal. -/
example (n : Nat) :
    True ∧ triple emp (pure n : St Nat) (fun result => ⌜result = n⌝) := by
  constructor
  fail_if_success all_goals sl_pure
  · trivial
  · sl_pure
    sl_frame

/-! ## Frame inference

`step` asks `sl_frame` to solve `H ⊢ Hcallee ∗ ?F`.  In that mode nothing may be
extracted from `H`: whatever is not required by the callee has to end up in `?F`,
and `?F` cannot mention anything introduced by the entailment. -/

def touchAny (p : Ptr Nat) : St Unit := do
  let value ← read p
  update p value

/-- The `sl_pull` is not removable: frame inference may not open the existential. -/
@[step]
theorem touchAny.spec (p : Ptr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchAny p ⦃⇓ iprop(∃ n, p ↦ n)⦄ := by
  unfold touchAny
  fail_if_success sl_step
  sl_pull n
  sl_step*

def touchThenSet (p : Ptr Nat) : St Unit := do
  touchAny p
  update p 7

/-- A pure fact that the callee does not need stays available afterwards, even
though the callee's precondition is an existential.  `step` pulls the
existential the callee gives back on its own. -/
example (p : Ptr Nat) (x : Nat) :
    ⦃ iprop(⌜x = 5⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃⇓ iprop(⌜x = 5⌝ ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  sl_step*

/-- A framed-out existential stays intact: instantiating it here would put a
variable out of the scope of the frame metavariable. -/
example (p q : Ptr Nat) (x : Nat) :
    ⦃ iprop(hexists (fun n => q ↦ n) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃⇓ iprop(hexists (fun n => q ↦ n) ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  sl_step*

/-- The callee's precondition may be owned as one opaque existential: the frame
is then `emp`, and the existential must *not* be opened. -/
example (p : Ptr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchThenSet p ⦃⇓ p ↦ 7⦄ := by
  unfold touchThenSet
  sl_step*

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
  sl_step
  guard_target =
    triple iprop(p ↦ value) (update p (value + 1)) (fun _ => iprop(p ↦ value + 1))
  sl_step*

/-! ## Terminal `pure` -/

/-- `step*` walks through the `return` of a function. -/
def readAndFree (p : Ptr Nat) : St Nat := do
  let v ← read p
  free p
  pure (v + 1)

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readAndFree p ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold readAndFree
  sl_step*

/-! ### Unbounded and bounded `sl_step*` -/

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : Ptr Nat) : St Nat := do
  let value ← read p
  free p
  pure (value + 1)

/-- If final framing fails after successful traversal, `sl_step*` keeps the
resulting entailment instead of rolling the entire tactic back. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  sl_step*
  simp only [opaqueStepResult]
  sl_frame

/-- A bounded `sl_step*` can represent the finite block without entering the
terminal entailment. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  sl_step* 2
  sl_pure
  simp only [opaqueStepResult]
  sl_frame

/-- Conversely, unbounded `sl_step*` may solve the terminal entailment, making
the tactics after the original finite block fail with no goals. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold readFreeReturn
  fail_if_success
    sl_step*
    sl_pure
  sl_step
  sl_step
  sl_pure
  sl_frame

/-! ## Affine resource discard -/

example (p : Ptr Nat) (value : Nat) :
    p ↦ value ⊢ GC := by
  sl_frame

example (p q : Ptr Nat) (left right : Nat) :
    p ↦ left ∗ q ↦ right ⊢ p ↦ left ∗ GC := by
  sl_frame

def allocAndForget (value : Nat) : St Unit := do
  let _ ← alloc value
  pure ()

/-- A freshly allocated cell need not be exposed in the postcondition. -/
example (value : Nat) :
    ⦃ emp ⦄ allocAndForget value ⦃⇓ emp⦄ := by
  unfold allocAndForget
  sl_step*

/-- Resources owned by the caller may be discarded before a computation. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ (pure () : St Unit) ⦃⇓ emp⦄ := by
  sl_step*

/-! ## The tactics ported from Separation Logic Foundations

`SLTactics.lean` ports SLF's magic wand, ramified frame rule, `xsimpl`, `xpull`,
`xchange`, `xval` and `xapp`. -/

-- wand laws
example (H1 H2 : SLProp) : H1 ∗ (H1 -∗ H2) ⊢ H2 := hwand_cancel H1 H2
example (Q1 Q2 : SLPost Nat) : Q1 ∗+ (Q1 -∗+ Q2) ⊢+ Q2 := qwand_cancel Q1 Q2

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
  sl_step*

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
  sl_step*

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
    sl_step*

/-- A wand on the right is cancelled against an identical one on the left before
being used to absorb the residual resources. -/
example (Q₁ Q₂ : SLPost Nat) (H : SLProp) :
    iprop(H ∗ (Q₁ -∗+ Q₂)) ⊢ iprop(H ∗ (Q₁ -∗+ Q₂)) := by
  sl_frame

/-- `sl_step` only touches the goals `step` produces. -/
example (p q : Ptr Nat) :
    (⦃ iprop(p ↦ 3 ∗ q ↦ 7) ⦄ read p ⦃⇓ r => iprop(⌜r = 3⌝ ∗ (p ↦ 3 ∗ q ↦ 7))⦄)
    ∧ (iprop(p ↦ 3 ∗ q ↦ 7) ⊢ iprop(q ↦ 7 ∗ p ↦ 3)) := by
  refine ⟨?_, ?_⟩
  sl_step
  sl_frame

/-! ## `sl_step` -/

/-- `sl_step` supplies `sl_frame` as the precondition discharger, and `with`
is unnecessary for a registered specification. -/
example (p : Ptr Nat) (x : Nat) :
    ⦃ iprop(⌜x = 5⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃⇓ iprop(⌜x = 5⌝ ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  sl_step*

/-- A specification that is not registered still needs `with`; `sl_step` only
drops the `by sl_frame`. -/
example (p : Ptr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchAny p ⦃⇓ iprop(∃ n, p ↦ n)⦄ := by
  unfold touchAny
  sl_pull n
  sl_step with read.spec p n
  sl_step*

/-! ### Side conditions -/

def readTwice (p : Ptr Nat) : St Nat := do
  let a ← read p
  let b ← read p
  pure (a + b)

@[step]
theorem readTwice.spec (p : Ptr Nat) (n : Nat) (hn : 0 < n) :
    ⦃ p ↦ n ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  unfold readTwice
  sl_step*

/-- `sl_side?` discharges the `Prop` argument of a registered specification, so
`with` is unnecessary even though `hn` is not determined by the program. -/
example (p : Ptr Nat) : ⦃ p ↦ 3 ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ 3)⦄ := by
  sl_step*

/-- `grind` is the last resort: `0 < n` follows from `hguard` only together with
`hb`, which is out of reach of `assumption`, `simp` and `omega`. -/
example (p : Ptr Nat) (n : Nat) (b : Bool) (hb : b = true) (hguard : b = true → 0 < n) :
    ⦃ p ↦ n ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  sl_step*

/-- `-grind` drops it, handing the side condition back tagged with its binder name. -/
example (p : Ptr Nat) (n : Nat) (b : Bool) (hb : b = true) (hguard : b = true → 0 < n) :
    ⦃ p ↦ n ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  sl_step* -grind
  case hn => grind

end Aeneas.SLPoC
