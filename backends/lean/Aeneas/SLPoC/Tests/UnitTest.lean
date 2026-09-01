import Aeneas.SLPoC.Tests.Examples.Basic

namespace Aeneas.SLPoC


/-! ## Entailment framing -/

example (P Q : IProp) : emp ⊢ (P ∗ (P -∗ Q)) -∗ Q := by
  apply wand_intro
  irewrite (wand_cancel P Q)
  iframe

example (p q : Ptr Nat) (x y : Nat) :
    p ↦ x ∗ q ↦ y ⊢ q ↦ y ∗ p ↦ x := by
  iframe

/-- An existential of the right-hand side is instantiated by the cancellation. -/
example (p : Ptr Nat) (value : Nat) :
    p ↦ value ⊢ iprop(∃ w, ⌜w = value⌝ ∗ p ↦ w) := by
  iframe

/-- A pure fact of the left-hand side is available when proving the pure facts
of the right-hand side, even though it is consumed by the entailment. -/
example (p : Ptr Nat) (value w : Nat) :
    iprop(⌜w = value + 1⌝ ∗ p ↦ value) ⊢ iprop(⌜0 < w⌝ ∗ p ↦ value) := by
  iframe

/-- An existential of the left-hand side is introduced before the one of the
right-hand side, so the witness may depend on it. -/
example (p : Ptr Nat) :
    iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) ⊢ iprop(∃ m, p ↦ m) := by
  iframe

/-- Cancellation happens up to associativity and commutativity. -/
example (p q r : Ptr Nat) (x y z : Nat) :
    iprop((p ↦ x ∗ q ↦ y) ∗ r ↦ z) ⊢ iprop(r ↦ z ∗ (q ↦ y ∗ p ↦ x)) := by
  iframe

/-- The pure side-goals are proved *after* the cancellation, so they see the
witness that the cancellation chose. -/
example (p : Ptr Nat) :
    p ↦ 3 ⊢ iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) := by
  iframe

/-! ## `iintro` -/

/-- `step` cannot open a leading existential before frame inference. Pulling its witness
exposes the pure fact, which `iintro_keep` then copies into the context. -/
example (p : Ptr Nat) :
    ⦃ iprop(∃ n, ⌜n = 1⌝ ∗ p ↦ n) ⦄ Examples.incr_ptr p ⦃⇓ p ↦ 2⦄ := by
  unfold Examples.incr_ptr
  fail_if_success
    step
    done
  iintro_shallow
  step*

/-- Without arguments it peels as much as it can. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ iprop(⌜value = 1⌝ ∗ p ↦ value) ⦄ Examples.incr_ptr p ⦃⇓ p ↦ 2⦄ := by
  unfold Examples.incr_ptr
  iintro
  step*

/-! ## `iintro_keep`

Unlike `iintro`, this copies the pure facts of the precondition into the local
context instead of consuming them, so the assertion stays available to the
framing of later steps. -/

/-- The pointer passed to the callee is reducible to the owned pointer only
through a pure fact in the precondition, which has to be copied into the context
while the postcondition keeps it. -/
example (p q : Ptr Nat) :
    ⦃ iprop(⌜q = p⌝ ∗ p ↦ 1) ⦄ Examples.incr_ptr q ⦃⇓ iprop(⌜q = p⌝ ∗ p ↦ 2)⦄ := by
  unfold Examples.incr_ptr
  iintro_shallow
  step*

/-- `iintro_keep` leaves the precondition untouched: the fact is needed both in
the context (to rewrite the cell) and in the assertion (for the postcondition). -/
example (p : Ptr Nat) (n : Nat) :
    ⦃ iprop(⌜n = 1⌝ ∗ p ↦ n) ⦄ pure () ⦃⇓ iprop(⌜n = 1⌝ ∗ p ↦ 1)⦄ := by
  iintro_shallow
  step
  case hRamified =>
    apply postWand_intro
    intro _
    iframe

/-- `step` reduces match/let noise around a terminal return. -/
example (n : Nat) :
    ⦃ emp ⦄ (Prod.rec (fun value _ => pure value) (n, true) : St Nat)
      ⦃⇓ result => ⌜result = n⌝⦄ := by
  step
  simp [Entails, ipure]

def namedPure (n : Nat) : St Nat :=
  pure n

@[step]
theorem namedPure.spec (n : Nat) :
    ⦃ emp ⦄ namedPure n ⦃⇓ result => ⌜result = n⌝⦄ := by
  unfold namedPure
  step
  simp [Entails, ipure]

/-- The direct terminal rule does not unfold named wrappers and bypass their
registered specifications: `step` goes through `namedPure.spec` and exposes
the final ramified-frame goal. -/
example (n : Nat) :
    ⦃ emp ⦄ namedPure n ⦃⇓ result => ⌜result = n⌝⦄ := by
  step
  simp [Entails, ipure]

/-- Normalization inside `step` stays focused on its original goal. -/
example (n : Nat) :
    True ∧ ⦃ emp ⦄ (pure n : St Nat) ⦃⇓ result => ⌜result = n⌝⦄ := by
  constructor
  fail_if_success all_goals step
  · trivial
  · step
    simp [Entails, ipure]

/-! ## Frame inference

`step` asks `iframe` to solve `H ⊢ Hcallee ∗ ?F`.  In that mode nothing may be
extracted from `H`: whatever is not required by the callee has to end up in `?F`,
and `?F` cannot mention anything introduced by the entailment. -/

def touchAny (p : Ptr Nat) : St Unit := do
  let value ← read p
  update p value

/-- The `iintro` is not removable: frame inference may not open the existential. -/
@[step]
theorem touchAny.spec (p : Ptr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchAny p ⦃⇓ iprop(∃ n, p ↦ n)⦄ := by
  unfold touchAny
  fail_if_success
    step*
    done
  iintro n
  step*

def touchThenSet (p : Ptr Nat) : St Unit := do
  touchAny p
  update p 7

/-- The witness `step` peels off the precondition of the continuation takes the name given for
it, like an output. -/
example (p : Ptr Nat) (x : Nat) :
    ⦃ iprop(⌜x = 5⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃⇓ iprop(⌜x = 5⌝ ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step as ⟨ pulled ⟩
  guard_hyp pulled : Nat
  step*

/-- A pure fact that the callee does not need stays available afterwards, even
though the callee's precondition is an existential.  `step` pulls the
existential the callee gives back on its own. -/
example (p : Ptr Nat) (x : Nat) :
    ⦃ iprop(⌜x = 5⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃⇓ iprop(⌜x = 5⌝ ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step*

/-- A framed-out existential stays intact: instantiating it here would put a
variable out of the scope of the frame metavariable. -/
example (p q : Ptr Nat) (x : Nat) :
    ⦃ iprop(iexists (fun n => q ↦ n) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃⇓ iprop(iexists (fun n => q ↦ n) ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step*

/-- The callee's precondition may be owned as one opaque existential: the frame
is then `emp`, and the existential must *not* be opened. -/
example (p : Ptr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchThenSet p ⦃⇓ p ↦ 7⦄ := by
  unfold touchThenSet
  step*

/-- `iframe` leaves the other goals of the proof alone. -/
example (p : Ptr Nat) (x : Nat) : (p ↦ x ⊢ p ↦ x) ∧ 1 = 1 := by
  refine ⟨?_, ?_⟩
  · iframe
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
  step
  guard_target =
    ⦃ p ↦ value ⦄ update p (value + 1) ⦃⇓ p ↦ value + 1⦄
  step*

/-! ## Terminal `pure` -/

/-- `step*` walks through the `return` of a function. -/
def readAndFree (p : Ptr Nat) : St Nat := do
  let v ← read p
  free p
  pure (v + 1)

example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readAndFree p ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold readAndFree
  step*

/-! ### Unbounded and bounded `step*` -/

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : Ptr Nat) : St Nat := do
  let value ← read p
  free p
  pure (value + 1)

/-- If final framing fails after successful traversal, `step*` keeps the
resulting entailment instead of rolling the entire tactic back. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  step*
  simp only [opaqueStepResult]
  iframe

/-- A bounded `step*` can represent the finite block without entering the
terminal entailment. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  step* 2
  step
  simp only [opaqueStepResult]
  iframe

/-- Conversely, unbounded `step*` may solve the terminal entailment, making
the tactics after the original finite block fail with no goals. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜result = value + 1⌝⦄ := by
  unfold readFreeReturn
  fail_if_success
    step*
    step
  step
  step
  step
  simp [Entails, Aeneas.SLPoC.emp, ipure]

/-! ## Affine resource discard

The entailment itself is affine, as Iris's is: `H ⊢ emp` for every `H`, so
resources are dropped without any explicit absorbing assertion. -/

example (p : Ptr Nat) (value : Nat) :
    p ↦ value ⊢ emp := by
  iframe

example (p q : Ptr Nat) (left right : Nat) :
    p ↦ left ∗ q ↦ right ⊢ p ↦ left := by
  iframe

/-- A pure fact needs no resources of its own, so it follows from anything. -/
example (P : IProp) : P ⊢ ⌜8 = 8⌝ := by
  iframe

example (p q : Ptr Nat) (left right : Nat) :
    p ↦ left ∗ q ↦ right ⊢ p ↦ left ∗ emp := by
  iframe

/-- Discarding is *not* forgetting: separated cells stay separated, so a cell
still cannot be owned twice. -/
example (p : Ptr Nat) (x y : Nat) :
    p ↦ x ∗ p ↦ y ⊢ ⌜False⌝ :=
  pointsTo_exclusive p x y

/-- Nor is discarding conjuring: `iframe` drops the cell the right-hand side
does not ask for, but still refuses one the left-hand side does not own. -/
example (p q : Ptr Nat) (x y : Nat) : p ↦ x ∗ q ↦ y ⊢ q ↦ y := by
  fail_if_success
    (have : p ↦ x ⊢ q ↦ y := by iframe)
  iframe

/-- Affinity weakens; it does not fabricate resources. -/
example (p : Ptr Nat) (value : Nat) : ¬ (emp ⊢ p ↦ value) := by
  intro hImpl
  have hContains := Ptr.contains_of_sub (hImpl ∅ trivial)
  exact not_contains_empty p hContains

/-- Nor does it excuse a specification from owning what it reads. -/
example (p : Ptr Nat) : ¬ (⦃ emp ⦄ read p ⦃⇓ _ => emp⦄) := by
  intro hTriple
  have hTheta :
      theta (read p) (fun _ => emp) ∅ :=
    (triple_iff _ _ _).mp hTriple ∅ trivial
  simp only [read, guardedModify] at hTheta
  rw [theta_trigger_eq] at hTheta
  obtain ⟨hContains, -⟩ := theta_ev_elim hTheta
  exact not_contains_empty p hContains

def allocAndForget (value : Nat) : St Unit := do
  let _ ← alloc value
  pure ()

/-- A freshly allocated cell need not be exposed in the postcondition. -/
example (value : Nat) :
    ⦃ emp ⦄ allocAndForget value ⦃⇓ emp⦄ := by
  unfold allocAndForget
  step*

/-- Resources owned by the caller may be discarded before a computation. -/
example (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ (pure () : St Unit) ⦃⇓ emp⦄ := by
  step*

/-! ## Separation-logic tactics -/

-- wand laws
example (H1 H2 : IProp) : H1 ∗ (H1 -∗ H2) ⊢ H2 := wand_cancel H1 H2
example (Q1 Q2 : IPost Nat) : Q1 ∗+ (Q1 -∗+ Q2) ⊢+ Q2 := postWand_cancel Q1 Q2

-- The RHS witness depends on the LHS witness.
example (p : Ptr Nat) :
    iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) ⊢ iprop(∃ m, p ↦ (m + 1)) := by
  iintro_entail
  -- `iintro_entail` names the variables it introduces `x` and the facts `h`.
  refine entails_exists_r (x - 1) ?_
  rw [show x - 1 + 1 = x by omega]
  isimpl

-- irewrite with an entailment
theorem cellPair (p q : Ptr Nat) : iprop(p ↦ 1 ∗ q ↦ 2) ⊢ iprop(∃ n, p ↦ n ∗ q ↦ 2) :=
  entails_exists_r 1 (entails_refl _)

example (p q r : Ptr Nat) :
    iprop(r ↦ 0 ∗ (p ↦ 1 ∗ q ↦ 2)) ⊢ iprop(∃ n, r ↦ 0 ∗ (p ↦ n ∗ q ↦ 2)) := by
  irewrite (cellPair p q)
  isimpl

-- irewrite with an equality, on a triple precondition
theorem swapEq (p q : Ptr Nat) : iprop(p ↦ 1 ∗ q ↦ 2) = iprop(q ↦ 2 ∗ p ↦ 1) :=
  sep_comm_eq _ _

example (p q : Ptr Nat) :
    ⦃ iprop((p ↦ 1 ∗ q ↦ 2) ∗ emp) ⦄ Examples.incr_ptr q ⦃⇓ iprop(q ↦ 3 ∗ p ↦ 1)⦄ := by
  unfold Examples.incr_ptr
  irewrite (swapEq p q)
  step*

-- wp_pures
example (p : Ptr Nat) : ⦃ p ↦ 1 ⦄ (pure 5 : St Nat) ⦃⇓ v => ⌜v = 5⌝ ∗ p ↦ 1⦄ := by
  wp_pures
  isimpl

-- wp_apply: terminal call through the ramified frame rule
example (p q : Ptr Nat) (x : Nat) :
    ⦃ iprop(p ↦ x ∗ q ↦ 9) ⦄ Examples.incr_ptr p ⦃⇓ iprop(q ↦ 9 ∗ p ↦ (x + 1))⦄ := by
  wp_apply (Examples.incr_ptr.spec p x)


/-! ### The ramified frame rule in `step` -/

/-- `step` exposes a terminal call's ramified-frame obligation for the caller. -/
example (p q : Ptr Nat) :
    ⦃ iprop(p ↦ 3 ∗ q ↦ 7) ⦄ read p ⦃⇓ r => iprop(⌜r = 3⌝ ∗ (p ↦ 3 ∗ q ↦ 7))⦄ := by
  step with read.spec p 3
  iframe

/-- What the ramified frame rule buys: the precondition of the *caller* may be an
existential, and `iframe` is free to open it because there is no frame
metavariable to keep it out of.  The explicit frame rule cannot do this. -/
example (q : Ptr Nat) :
    ⦃ iexists (fun n => iprop(q ↦ n)) ⦄ alloc 5
      ⦃⇓ r => iprop(r ↦ 5 ∗ iexists (fun n => iprop(q ↦ n)))⦄ := by
  step*

/-- `iintro_entail` must refuse a frame-inference goal: introducing the existential of
the left-hand side would put a variable out of the scope of the frame `?F`.  The
`hPre` premise of the bind rule is exactly such a goal. -/
example (p q : Ptr Nat) (x : Nat) :
    ⦃ iprop(iexists (fun n => iprop(q ↦ n)) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃⇓ iprop(iexists (fun n => iprop(q ↦ n)) ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  apply triple_step_bind (touchAny p) _ (touchAny.spec p)
  case hPre =>
    fail_if_success iintro_entail
    iframe
  case hNext =>
    intro _
    iintro
    step*

/-- A wand on the right is cancelled against an identical one on the left before
being used to absorb the residual resources. -/
example (Q₁ Q₂ : IPost Nat) (H : IProp) :
    iprop(H ∗ (Q₁ -∗+ Q₂)) ⊢ iprop(H ∗ (Q₁ -∗+ Q₂)) := by
  iframe

/-- `step` only touches the goal it steps, leaving sibling goals alone. -/
example (p q : Ptr Nat) :
    (⦃ iprop(p ↦ 3 ∗ q ↦ 7) ⦄ read p ⦃⇓ r => iprop(⌜r = 3⌝ ∗ (p ↦ 3 ∗ q ↦ 7))⦄)
    ∧ (iprop(p ↦ 3 ∗ q ↦ 7) ⊢ iprop(q ↦ 7 ∗ p ↦ 3)) := by
  refine ⟨?_, ?_⟩
  step with read.spec p 3
  iframe
  iframe

/-! ## `step` -/

/-- `step` supplies `iframe` as the precondition discharger, and `with`
is unnecessary for a registered specification. -/
example (p : Ptr Nat) (x : Nat) :
    ⦃ iprop(⌜x = 5⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃⇓ iprop(⌜x = 5⌝ ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step*

/-- A specification that is not registered still needs `with`; `step` only
drops the `by iframe`. -/
example (p : Ptr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchAny p ⦃⇓ iprop(∃ n, p ↦ n)⦄ := by
  unfold touchAny
  iintro n
  step with read.spec p n
  step*

/-! ### Side conditions -/

def readTwice (p : Ptr Nat) : St Nat := do
  let a ← read p
  let b ← read p
  pure (a + b)

@[step]
theorem readTwice.spec (p : Ptr Nat) (n : Nat) (hn : 0 < n) :
    ⦃ p ↦ n ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  unfold readTwice
  step*

/-- The `Prop` argument of a registered specification is handed back tagged with its
binder name, so `with` is unnecessary even though `hn` is not determined by the
program: it is discharged like any other goal. -/
example (p : Ptr Nat) : ⦃ p ↦ 3 ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ 3)⦄ := by
  step*
  case hn => grind

/-- `grind` is the last resort: `0 < n` follows from `hguard` only together with
`hb`, which is out of reach of `assumption`, `simp` and `omega`. -/
example (p : Ptr Nat) (n : Nat) (b : Bool) (hb : b = true) (hguard : b = true → 0 < n) :
    ⦃ p ↦ n ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  step*
  case hn => grind

/-- `-grind` drops it, handing the side condition back tagged with its binder name. -/
example (p : Ptr Nat) (n : Nat) (b : Bool) (hb : b = true) (hguard : b = true → 0 < n) :
    ⦃ p ↦ n ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  step* -grind
  case hn => grind

end Aeneas.SLPoC
