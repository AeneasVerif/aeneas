import Aeneas.Std.Buffer
import SepLogic.Fixtures

open Aeneas
open SepLogic
open Aeneas.SepLogic

namespace SepLogic

open Aeneas.Data.Coinductive

open Aeneas.Std.WP

open Aeneas.Std (Buffer Heap MutRawPtr RawPtr Result RustEffect U8 U32 I32 UScalar IScalar)
open Aeneas.Std.MutRawPtr (alloc free write)
open Aeneas.Std.RawPtr (read pointsTo_exclusive)

unseal Result

/-! ## Failure effect -/

example : (Result.fail .panic : Result Nat) =
    Result.vis (RustEffect.Input.fail .panic) PEmpty.elim :=
  rfl

example (Q : Nat → Prop) :
    ¬ spec (Result.fail .panic : Result Nat) Q :=
  (spec_fail .panic).mp

example (Q : Nat → Prop) :
    ¬ dspec (Result.fail .panic : Result Nat) Q :=
  (dspec_fail .panic).mp

/-! ## Entailment framing -/

example (P Q : IProp) : emp ⊢ (P ∗ (P -∗ Q)) -∗ Q := by
  apply wand_intro
  irewrite (wand_cancel P Q)
  iframe

example (p q : MutRawPtr U32) (x y : U32) :
    p ↦ x ∗ q ↦ y ⊢ q ↦ y ∗ p ↦ x := by
  iframe

/-- An existential of the right-hand side is instantiated by the cancellation. -/
example (p : MutRawPtr U32) (value : U32) :
    p ↦ value ⊢ iprop(∃ w, ⌜w = value⌝ ∗ p ↦ w) := by
  iframe

/-- A pure fact of the left-hand side is available when proving the pure facts
of the right-hand side, even though it is consumed by the entailment. -/
example (p : MutRawPtr U32) (value w : U32) :
    iprop(⌜w.val = value.val + 1⌝ ∗ p ↦ value) ⊢ iprop(⌜0 < w.val⌝ ∗ p ↦ value) := by
  iframe

/-- An existential of the left-hand side is introduced before the one of the
right-hand side, so the witness may depend on it. -/
example (p : MutRawPtr U32) :
    iprop(∃ n, ⌜0 < n.val⌝ ∗ p ↦ n) ⊢ iprop(∃ m, p ↦ m) := by
  iframe

/-- Cancellation happens up to associativity and commutativity. -/
example (p q r : MutRawPtr U32) (x y z : U32) :
    iprop((p ↦ x ∗ q ↦ y) ∗ r ↦ z) ⊢ iprop(r ↦ z ∗ (q ↦ y ∗ p ↦ x)) := by
  iframe

/-- The pure side-goals are proved *after* the cancellation, so they see the
witness that the cancellation chose. -/
example (p : MutRawPtr U32) :
    p ↦ 3#u32 ⊢ iprop(∃ n, ⌜0 < n.val⌝ ∗ p ↦ n) := by
  iframe

/-! ## `iintro` -/

/-- `step` cannot open a leading existential before frame inference. Pulling its witness
exposes the pure fact, which `iintro_keep` then copies into the context. -/
example (p : MutRawPtr U32) :
    ⦃ iprop(∃ n, ⌜n = 1#u32⌝ ∗ p ↦ n) ⦄ Fixtures.incr_ptr p ⦃⇓ p ↦ 2#u32⦄ := by
  unfold Fixtures.incr_ptr
  fail_if_success
    step
    done
  iintro_shallow
  step*

/-- Without arguments it peels as much as it can. -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ iprop(⌜value = 1#u32⌝ ∗ p ↦ value) ⦄ Fixtures.incr_ptr p ⦃⇓ p ↦ 2#u32⦄ := by
  unfold Fixtures.incr_ptr
  iintro
  step*

/-- `iintro_shallow` finds pure facts to the right of spatial resources without
unfolding those resources. -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ iprop(p ↦ value ∗ ⌜value = 1#u32⌝) ⦄ pure () ⦃⇓ p ↦ value⦄ := by
  wp_pures
  iintro_shallow
  guard_hyp h : value = 1#u32
  iframe

/-- Right-side extraction also works for partial ispecs. -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ iprop(p ↦ value ∗ ⌜value = 1#u32⌝) ⦄ pure () ⦃⇓ p ↦ value⦄div := by
  dwp_pures
  iintro_shallow
  guard_hyp h : value = 1#u32
  iframe

/-- The `step` introduction variant extracts facts from the callee
postcondition on the left, but not from the frame on the right. -/
example (p : MutRawPtr U32) (value : U32) (P F : Prop) :
    ⦃ iprop((p ↦ value ∗ ⌜P⌝) ∗ ⌜F⌝) ⦄ pure ()
      ⦃⇓ iprop(p ↦ value ∗ ⌜F⌝)⦄ := by
  wp_pures
  iintro_shallow_post
  guard_hyp h : P
  fail_if_success have : F := by assumption
  iframe

/-! ## `iintro_keep`

Unlike `iintro`, this copies the pure facts of the precondition into the local
context instead of consuming them, so the assertion stays available to the
framing of later steps. -/

/-- The pointer passed to the callee is reducible to the owned pointer only
through a pure fact in the precondition, which has to be copied into the context
while the postcondition keeps it. -/
example (p q : MutRawPtr U32) :
    ⦃ iprop(⌜q = p⌝ ∗ p ↦ 1#u32) ⦄ Fixtures.incr_ptr q ⦃⇓ iprop(⌜q = p⌝ ∗ p ↦ 2#u32)⦄ := by
  unfold Fixtures.incr_ptr
  iintro_shallow
  step*

/-- `iintro_keep` leaves the precondition untouched: the fact is needed both in
the context (to rewrite the cell) and in the assertion (for the postcondition). -/
example (p : MutRawPtr U32) (n : U32) :
    ⦃ iprop(⌜n = 1#u32⌝ ∗ p ↦ n) ⦄ pure () ⦃⇓ iprop(⌜n = 1#u32⌝ ∗ p ↦ 1#u32)⦄ := by
  wp_pures
  iintro_keep
  guard_target = (iprop(⌜n = 1#u32⌝ ∗ p ↦ n) ⊢ iprop(⌜n = 1#u32⌝ ∗ p ↦ 1#u32))
  iframe

/-- `step` reduces match/let noise around a terminal return. -/
example (n : Nat) :
    ⦃ emp ⦄ (Prod.rec (fun value _ => pure value) (n, true) : Result Nat)
      ⦃⇓ result => ⌜result = n⌝⦄ := by
  step

def namedPure (n : Nat) : Result Nat :=
  pure n

@[step]
theorem namedPure.spec (n : Nat) :
    ⦃ emp ⦄ namedPure n ⦃⇓ result => ⌜result = n⌝⦄ := by
  unfold namedPure
  step

/-- The direct terminal rule does not unfold named wrappers and bypass their
registered specifications: `step` goes through `namedPure.spec`. -/
example (n : Nat) :
    ⦃ emp ⦄ namedPure n ⦃⇓ result => ⌜result = n⌝⦄ := by
  step

/-- Normalization inside `step` stays focused on its original goal. -/
example (n : Nat) :
    True ∧ ⦃ emp ⦄ (pure n : Result Nat) ⦃⇓ result => ⌜result = n⌝⦄ := by
  constructor
  fail_if_success all_goals step
  · trivial
  · step

/-! ## Frame inference

`step` asks `iframe` to solve `H ⊢ Hcallee ∗ ?F`.  In that mode nothing may be
extracted from `H`: whatever is not required by the callee has to end up in `?F`,
and `?F` cannot mention anything introduced by the entailment. -/

def touchAny (p : MutRawPtr U32) : Result Unit := do
  let value ← read p
  write p value

/-- The `iintro` is not removable: frame inference may not open the existential. -/
@[step]
theorem touchAny.spec (p : MutRawPtr U32) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchAny p ⦃⇓ iprop(∃ n, p ↦ n)⦄ := by
  unfold touchAny
  fail_if_success
    step*
    done
  iintro n
  step*

def touchThenSet (p : MutRawPtr U32) : Result Unit := do
  touchAny p
  write p 7#u32

/-- The witness `step` peels off the precondition of the continuation takes the name given for
it, like an output. -/
example (p : MutRawPtr U32) (x : U32) :
    ⦃ iprop(⌜x = 5#u32⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃⇓ iprop(⌜x = 5#u32⌝ ∗ p ↦ 7#u32)⦄ := by
  unfold touchThenSet
  step as ⟨ pulled ⟩
  guard_hyp pulled : U32
  step*

/-- A pure fact that the callee does not need stays available afterwards, even
though the callee's precondition is an existential.  `step` pulls the
existential the callee gives back on its own. -/
example (p : MutRawPtr U32) (x : U32) :
    ⦃ iprop(⌜x = 5#u32⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃⇓ iprop(⌜x = 5#u32⌝ ∗ p ↦ 7#u32)⦄ := by
  unfold touchThenSet
  step*

/-- A framed-out existential stays intact: instantiating it here would put a
variable out of the scope of the frame metavariable. -/
example (p q : MutRawPtr U32) (x : U32) :
    ⦃ iprop(iexists (fun n => q ↦ n) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃⇓ iprop(iexists (fun n => q ↦ n) ∗ p ↦ 7#u32)⦄ := by
  unfold touchThenSet
  step*

/-- The callee's precondition may be owned as one opaque existential: the frame
is then `emp`, and the existential must *not* be opened. -/
example (p : MutRawPtr U32) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchThenSet p ⦃⇓ p ↦ 7#u32⦄ := by
  unfold touchThenSet
  step*

/-- `iframe` leaves the other goals of the proof alone. -/
example (p : MutRawPtr U32) (x : U32) : (p ↦ x ⊢ p ↦ x) ∧ 1 = 1 := by
  refine ⟨?_, ?_⟩
  · iframe
  · rfl

/-! ## The shape of the goal `step` hands back -/

def readThenWrite (p : MutRawPtr U32) : Result Unit := do
  let value ← read p
  write p (value.wrapping_add 1#u32)

/-- `step` names the returned value and its equation, and removes the `∗ emp`
of an empty frame. The caller may substitute the equation before continuing. -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ readThenWrite p ⦃⇓ p ↦ value.wrapping_add 1#u32⦄ := by
  unfold readThenWrite
  step as ⟨actual, hActual⟩
  guard_hyp hActual : actual = value
  subst actual
  guard_target =
    ⦃ p ↦ value ⦄ write p (value.wrapping_add 1#u32) ⦃⇓ p ↦ value.wrapping_add 1#u32⦄
  step*

/-! ## Terminal `pure` -/

/-- `step*` walks through the `return` of a function. -/
def readAndFree (p : MutRawPtr U32) : Result Nat := do
  let v ← read p
  free p
  pure (v.val + 1)

example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ readAndFree p ⦃⇓ result => ⌜result = value.val + 1⌝⦄ := by
  unfold readAndFree
  step*

/-! ### Unbounded and bounded `step*` -/

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : MutRawPtr U32) : Result Nat := do
  let value ← read p
  free p
  pure (value.val + 1)

/-- If final framing fails after successful traversal, `step*` keeps the
resulting entailment instead of rolling the entire tactic back. -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜opaqueStepResult result (value.val + 1)⌝⦄ := by
  unfold readFreeReturn
  step*
  simp only [opaqueStepResult]
  agrind

/-- A bounded `step*` can represent the finite block without entering the
terminal entailment. -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜opaqueStepResult result (value.val + 1)⌝⦄ := by
  unfold readFreeReturn
  step* 2
  step
  simp only [opaqueStepResult]
  agrind

/-- Conversely, unbounded `step*` may solve the terminal entailment, making
the tactics after the original finite block fail with no goals. -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃⇓ result => ⌜result = value.val + 1⌝⦄ := by
  unfold readFreeReturn
  fail_if_success
    step*
    step
  step
  step
  step
  agrind

/-! ## Affine resource discard

The entailment itself is affine, as Iris's is: `H ⊢ emp` for every `H`, so
resources are dropped without any explicit absorbing assertion. -/

example (p : MutRawPtr U32) (value : U32) :
    p ↦ value ⊢ emp := by
  iframe

example (p q : MutRawPtr U32) (left right : U32) :
    p ↦ left ∗ q ↦ right ⊢ p ↦ left := by
  iframe

/-- A pure fact needs no resources of its own, so it follows from anything. -/
example (P : IProp) : P ⊢ ⌜8 = 8⌝ := by
  iframe

example (p q : MutRawPtr U32) (left right : U32) :
    p ↦ left ∗ q ↦ right ⊢ p ↦ left ∗ emp := by
  iframe

/-- Discarding is *not* forgetting: separated cells stay separated, so a cell
still cannot be owned twice. -/
example (p : MutRawPtr U32) (x y : U32) :
    p ↦ x ∗ p ↦ y ⊢ ⌜False⌝ :=
  pointsTo_exclusive p x y (UScalar.byteRepr_size_pos _)

/-- Nor is discarding conjuring: `iframe` drops the cell the right-hand side
does not ask for, but still refuses one the left-hand side does not own. -/
example (p q : MutRawPtr U32) (x y : U32) : p ↦ x ∗ q ↦ y ⊢ q ↦ y := by
  fail_if_success
    (have : p ↦ x ⊢ q ↦ y := by iframe)
  iframe

/-- Affinity weakens; it does not fabricate resources. -/
example (p : MutRawPtr U32) (value : U32) : ¬ (emp ⊢ p ↦ value) := by
  intro hImpl
  have hContains := RawPtr.contains_of_pointsTo (hImpl ∅ trivial)
  exact RawPtr.not_contains_empty p (UScalar.byteRepr_size_pos _) hContains

/-- Nor does it excuse a specification from owning what it reads. -/
example (p : MutRawPtr U32) : ¬ (⦃ emp ⦄ read p ⦃⇓ _ => emp⦄) := by
  intro hTriple
  rw [ispec_iff] at hTriple
  have hSpec := hTriple emp ∅ ((sep_emp_r emp).mpr ∅ trivial)
  simp only [Aeneas.Std.RawPtr.read, Result.guardedModify] at hSpec
  obtain ⟨hReadable, -⟩ := hSpec.vis_view
  exact RawPtr.not_contains_empty p (UScalar.byteRepr_size_pos _) hReadable.contains

def allocAndForget (value : U32) : Result Unit := do
  let _ ← alloc value
  pure ()

/-- A freshly allocated cell need not be exposed in the postcondition. -/
example (value : U32) :
    ⦃ emp ⦄ allocAndForget value ⦃⇓ emp⦄ := by
  unfold allocAndForget
  step*

/-- Resources owned by the caller may be discarded before a computation. -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ (pure () : Result Unit) ⦃⇓ emp⦄ := by
  step*

/-! ## Separation-logic tactics -/

-- wand laws
example (H1 H2 : IProp) : H1 ∗ (H1 -∗ H2) ⊢ H2 := wand_cancel H1 H2
example (Q1 Q2 : IPost Nat) : Q1 ∗+ (Q1 -∗+ Q2) ⊢+ Q2 := postWand_cancel Q1 Q2

-- The RHS witness depends on the LHS witness.
example (p : MutRawPtr U32) :
    iprop(∃ n, ⌜0 < n.val⌝ ∗ p ↦ n) ⊢ iprop(∃ m : U32, p ↦ (m.wrapping_add 1#u32)) := by
  iintro_entail
  rename_i x hx
  refine entails_exists_r (x.wrapping_sub 1#u32) ?_
  rw [show (x.wrapping_sub 1#u32).wrapping_add 1#u32 = x by simp [UScalar.eq_equiv_bv_eq]]
  isimpl

-- irewrite with an entailment
theorem cellPair (p q : MutRawPtr U32) :
    iprop(p ↦ 1#u32 ∗ q ↦ 2#u32) ⊢ iprop(∃ n, p ↦ n ∗ q ↦ 2#u32) :=
  entails_exists_r 1#u32 (entails_refl _)

example (p q r : MutRawPtr U32) :
    iprop(r ↦ 0#u32 ∗ (p ↦ 1#u32 ∗ q ↦ 2#u32)) ⊢ iprop(∃ n, r ↦ 0#u32 ∗ (p ↦ n ∗ q ↦ 2#u32)) := by
  irewrite (cellPair p q)
  isimpl

-- irewrite with an equality, on an `ispec` precondition
theorem swapEq (p q : MutRawPtr U32) :
    iprop(p ↦ 1#u32 ∗ q ↦ 2#u32) = iprop(q ↦ 2#u32 ∗ p ↦ 1#u32) :=
  sep_comm_eq _ _

example (p q : MutRawPtr U32) :
    ⦃ iprop((p ↦ 1#u32 ∗ q ↦ 2#u32) ∗ emp) ⦄ Fixtures.incr_ptr q
      ⦃⇓ iprop(q ↦ 3#u32 ∗ p ↦ 1#u32)⦄ := by
  unfold Fixtures.incr_ptr
  irewrite (swapEq p q)
  step*

-- wp_pures
example (p : MutRawPtr U32) : ⦃ p ↦ 1#u32 ⦄ (pure 5 : Result Nat) ⦃⇓ v => ⌜v = 5⌝ ∗ p ↦ 1#u32⦄ := by
  wp_pures
  isimpl

-- wp_apply: terminal call through the ramified frame rule
example (p q : MutRawPtr U32) (x : U32) :
    ⦃ iprop(p ↦ x ∗ q ↦ 9#u32) ⦄ Fixtures.incr_ptr p
      ⦃⇓ iprop(q ↦ 9#u32 ∗ p ↦ (x.wrapping_add 1#u32))⦄ := by
  wp_apply (Fixtures.incr_ptr.spec p x)


/-! ### The ramified frame rule in `step` -/

/-- `step` discharges a terminal call's routine ramified-frame obligation. -/
example (p q : MutRawPtr U32) :
    ⦃ iprop(p ↦ 3#u32 ∗ q ↦ 7#u32) ⦄ read p
      ⦃⇓ r => iprop(⌜r = 3#u32⌝ ∗ (p ↦ 3#u32 ∗ q ↦ 7#u32))⦄ := by
  step with read.spec p 3#u32

/-- What the ramified frame rule buys: the precondition of the *caller* may be an
existential, and `iframe` is free to open it because there is no frame
metavariable to keep it out of.  The explicit frame rule cannot do this. -/
example (q : MutRawPtr U32) :
    ⦃ iexists (fun n => iprop(q ↦ n)) ⦄ alloc 5#u32
      ⦃⇓ r => iprop(r ↦ 5#u32 ∗ iexists (fun n => iprop(q ↦ n)))⦄ := by
  step*

/-- `iintro_entail` must refuse a frame-inference goal: introducing the existential of
the left-hand side would put a variable out of the scope of the frame `?F`.  The
`hPre` premise of the bind rule is exactly such a goal. -/
example (p q : MutRawPtr U32) (x : U32) :
    ⦃ iprop(iexists (fun n => iprop(q ↦ n)) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃⇓ iprop(iexists (fun n => iprop(q ↦ n)) ∗ p ↦ 7#u32)⦄ := by
  unfold touchThenSet
  apply Aeneas.Std.WP.ispec_bind (m := touchAny p) (touchAny.spec p)
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
example (p q : MutRawPtr U32) :
    (⦃ iprop(p ↦ 3#u32 ∗ q ↦ 7#u32) ⦄ read p ⦃⇓ r => iprop(⌜r = 3#u32⌝ ∗ (p ↦ 3#u32 ∗ q ↦ 7#u32))⦄)
    ∧ (iprop(p ↦ 3#u32 ∗ q ↦ 7#u32) ⊢ iprop(q ↦ 7#u32 ∗ p ↦ 3#u32)) := by
  refine ⟨?_, ?_⟩
  step with read.spec p 3#u32
  guard_target = (iprop(p ↦ 3#u32 ∗ q ↦ 7#u32) ⊢ iprop(q ↦ 7#u32 ∗ p ↦ 3#u32))
  iframe

/-! ## `step` -/

/-- `step` supplies `iframe` as the precondition discharger, and `with`
is unnecessary for a registered specification. -/
example (p : MutRawPtr U32) (x : U32) :
    ⦃ iprop(⌜x = 5#u32⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃⇓ iprop(⌜x = 5#u32⌝ ∗ p ↦ 7#u32)⦄ := by
  unfold touchThenSet
  step*

/-- A specification that is not registered still needs `with`; `step` only
drops the `by iframe`. -/
example (p : MutRawPtr U32) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchAny p ⦃⇓ iprop(∃ n, p ↦ n)⦄ := by
  unfold touchAny
  iintro n
  step with read.spec p n
  step*

/-! ### Side conditions -/

def readTwice (p : MutRawPtr U32) : Result Nat := do
  let a ← read p
  let b ← read p
  pure (a.val + b.val)

@[step]
theorem readTwice.spec (p : MutRawPtr U32) (n : U32) (hn : 0 < n.val) :
    ⦃ p ↦ n ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  unfold readTwice
  step*

/-- The `Prop` argument of a registered specification is discharged automatically,
even though its value argument is not determined by the program. -/
example (p : MutRawPtr U32) : ⦃ p ↦ 3#u32 ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ 3#u32)⦄ := by
  step*

/-- The default solver combines the implication and the equality to discharge
the side condition. -/
example (p : MutRawPtr U32) (n : U32) (b : Bool) (hb : b = true) (hguard : b = true → 0 < n.val) :
    ⦃ p ↦ n ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  step*

/-- Disabling both step grind paths does not disable the SL judgment's `iframe`
discharger, which can still prove this side condition. -/
example (p : MutRawPtr U32) (n : U32) (b : Bool) (hb : b = true) (hguard : b = true → 0 < n.val) :
    ⦃ p ↦ n ⦄ readTwice p ⦃⇓ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  step* -grind -threadGrindState

/-! ## Buffers and interior pointers

A pointer is a base address and a byte offset, and ownership of one allocation
splits along its indices: both halves of a split range lie in the *same*
allocation. -/

/-- Splitting and joining a range. -/
example (q : MutRawPtr U32) (x y : U32) :
    q ↦* [x, y] ⊣⊢ q ↦ x ∗ (q.add 1) ↦ y := by
  rw [RawPtr.pointsToRange_cons, ← RawPtr.pointsTo_eq_range]
  exact ⟨entails_refl _, entails_refl _⟩

/-- Splitting does not move the pointer: the halves are interior to the same
allocation. -/
example (q : MutRawPtr U32) (i : Nat) : (q.add i).base = q.base := rfl

/-- Owning nothing is owning the empty range. -/
example (q : MutRawPtr U32) : (q ↦* ([] : List U32)) = emp :=
  RawPtr.pointsToRange_nil q

/-- A slot still cannot be owned twice. -/
example (q : MutRawPtr U32) (x y : U32) : q ↦ x ∗ q ↦ y ⊢ ⌜False⌝ :=
  pointsTo_exclusive q x y (UScalar.byteRepr_size_pos _)

/-- Two slots of one allocation are owned separately. -/
example (q : MutRawPtr U32) (x y : U32) : q ↦ x ∗ (q.add 1) ↦ y ⊢ q ↦* [x, y] := by
  rw [RawPtr.pointsToRange_cons, ← RawPtr.pointsTo_eq_range]
  exact entails_refl _

def bufferOne : Result U32 := do
  let b ← Buffer.alloc 1 0#u32
  b.write 0 42#u32
  let value ← b.read 0
  free (b.ptrAt 0)
  pure value

/-- Allocating a buffer, writing to a slot, reading it back and releasing it,
proved end to end. -/
theorem bufferOne.spec : ⦃ emp ⦄ bufferOne ⦃⇓ result => ⌜result = 42#u32⌝⦄ := by
  unfold bufferOne
  step as ⟨b⟩
  irewrite (Buffer.pointsTo_entails_range b _)
  step*

/-! ## Pointer casts

Ownership is of bytes, so a cast changes the type the bytes are viewed at, not
the heap. -/

/-- A cast neither allocates nor moves the pointer. -/
example (p : MutRawPtr U32) :
    RawPtr.cast_scalar I32 .Const p = .ok p.retype := rfl

/-- Same size: the bytes of a `u32` are the bytes of an `i32`. -/
example (p : MutRawPtr U32) (x : U32) :
    ⦃ p ↦ x ⦄ RawPtr.cast_scalar I32 .Const p
      ⦃⇓ q => ⌜q = p.retype⌝ ∗ q ↦ (⟨x.bv⟩ : I32)⦄ :=
  RawPtr.cast_scalar.spec_of_decode p x _ (UScalar.decode_encode_iscalar x rfl) id

/-- Different size: a `u32` is owned as the four `u8`s of its little-endian
encoding. -/
example (p : MutRawPtr U32) (x : U32) :
    ⦃ p ↦ x ⦄ RawPtr.cast_scalar U8 .Mut p
      ⦃⇓ q => ⌜q = p.retype⌝ ∗ q ↦* x.bv.toLEBytes.map UScalar.mk⦄ := by
  rw [RawPtr.pointsTo_eq_range]
  exact RawPtr.cast_scalar.spec_range p [x] _ (by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact (UScalar.flatMap_encode_u8 _).symm) (fun _ _ => by simp [RawPtr.Aligned])

/-- Viewing owned bytes at another type can be undone, at an address aligned for
the original type. -/
example (p : MutRawPtr U32) (x : U32) (hAlign : p.Aligned) :
    (p.retype : MutRawPtr U8) ↦* x.bv.toLEBytes.map UScalar.mk ⊣⊢ p ↦* [x] := by
  have hBytes : [x].flatMap Aeneas.Std.ByteRepr.encode =
      (x.bv.toLEBytes.map (UScalar.mk (ty := .U8))).flatMap Aeneas.Std.ByteRepr.encode := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact (UScalar.flatMap_encode_u8 _).symm
  exact ⟨RawPtr.pointsToRange_retype _ _ _ hBytes.symm fun _ => hAlign,
    RawPtr.pointsToRange_retype p _ _ hBytes fun _ => by simp [RawPtr.Aligned]⟩

def castBytesBack (p : MutRawPtr U32) : Result (MutRawPtr U32) := do
  let q ← RawPtr.cast_scalar U8 .Mut p
  RawPtr.cast_scalar U32 .Mut q

/-- Casting to bytes and back keeps the alignment the original pointer had, so
the bytes can be read at `u32` again. -/
example (p : MutRawPtr U32) (x : U32) :
    ⦃ p ↦ x ⦄ castBytesBack p ⦃⇓ r => r ↦ x⦄ := by
  unfold castBytesBack
  have hBytes : [x].flatMap Aeneas.Std.ByteRepr.encode =
      (x.bv.toLEBytes.map (UScalar.mk (ty := .U8))).flatMap Aeneas.Std.ByteRepr.encode := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact (UScalar.flatMap_encode_u8 _).symm
  rw [RawPtr.pointsTo_eq_range]
  irewrite (RawPtr.pointsToRange_aligned p [x])
  iintro hAligned
  step with RawPtr.cast_scalar.spec_range p [x] _ hBytes (by intro _ _; simp [RawPtr.Aligned])
    as ⟨q, hq⟩
  step with RawPtr.cast_scalar.spec_range q _ [x] hBytes.symm (by
    intro _ _
    subst hq
    simpa using hAligned (by simp))

def patchByte (x y : U32) : Result (U32 × U32) := do
  let p ← RawPtr.materialize (M := .Mut) [x, y]
  let q ← RawPtr.cast_scalar U8 .Mut p
  MutRawPtr.write (q.add 1) 0xaa#u8
  let r ← RawPtr.cast_scalar U32 .Mut q
  let x' ← RawPtr.read r
  let y' ← RawPtr.read (r.add 1)
  pure (x', y')

theorem patchByte.spec (y : U32) :
    ⦃ emp ⦄ patchByte 0x11223344#u32 y ⦃⇓ r => ⌜r = (0x1122aa44#u32, y)⌝⦄ := by
  unfold patchByte
  step as ⟨p⟩
  irewrite (RawPtr.pointsToRange_aligned p _)
  iintro hAligned
  have hLow : (((0x11223344#u32).bv.toLEBytes.map (UScalar.mk (ty := .U8))).set 1
      0xaa#u8).flatMap Aeneas.Std.ByteRepr.encode = (0x1122aa44#u32).bv.toLEBytes := by
    decide +kernel
  have hBytes : [0x11223344#u32, y].flatMap Aeneas.Std.ByteRepr.encode =
      ((0x11223344#u32).bv.toLEBytes.map (UScalar.mk (ty := .U8)) ++
        y.bv.toLEBytes.map (UScalar.mk (ty := .U8))).flatMap Aeneas.Std.ByteRepr.encode := by
    rw [List.flatMap_append, UScalar.flatMap_encode_u8, UScalar.flatMap_encode_u8]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  step with RawPtr.cast_scalar.spec_range p _ _ hBytes (by intro _ _; simp [RawPtr.Aligned])
    as ⟨q, hq⟩
  step with MutRawPtr.write.spec_range q
    ((0x11223344#u32).bv.toLEBytes.map (UScalar.mk (ty := .U8)) ++
      y.bv.toLEBytes.map (UScalar.mk (ty := .U8))) 1 0xaa#u8 (by simp)
  have hBytes' : (((0x11223344#u32).bv.toLEBytes.map (UScalar.mk (ty := .U8)) ++
        y.bv.toLEBytes.map (UScalar.mk (ty := .U8))).set 1 0xaa#u8).flatMap
          Aeneas.Std.ByteRepr.encode =
      [0x1122aa44#u32, y].flatMap Aeneas.Std.ByteRepr.encode := by
    rw [List.set_append_left _ _ (by simp), List.flatMap_append, hLow,
      UScalar.flatMap_encode_u8]
    simp
  step with RawPtr.cast_scalar.spec_range q _ _ hBytes' (by
    intro _ _
    subst hq
    simpa using hAligned (by simp)) as ⟨r, hr⟩
  simp only [RawPtr.pointsToRange_cons, RawPtr.pointsToRange_nil]
  step*

/-- Bytes give no alignment guarantee: viewing an allocation made at `u8` at
`u32` has no read specification, even at offset `0`. -/
example (p : MutRawPtr U8) (hBase : p.base.align = 1) (P : IProp) (Q : U32 → IProp)
    (hSpec : ⦃ P ⦄ (p.retype : MutRawPtr U32).read ⦃⇓ y => Q y⦄) :
    P ⊢ ⌜False⌝ := by
  refine entails_trans (RawPtr.read.aligned_of_spec hSpec) ?_
  rw [entails_ipure_iff]
  intro hWide
  simp [RawPtr.Aligned, Aeneas.Std.UScalarTy.numBits, hBase] at hWide

/-- Reads are only defined at aligned addresses: the four bytes one past an
address aligned for `u32` have no read specification at `u32`. -/
example (p : MutRawPtr U8) (hAlign : 4 ∣ p.offset) (P : IProp) (Q : U32 → IProp)
    (hSpec : ⦃ P ⦄ ((p.add 1).retype : MutRawPtr U32).read ⦃⇓ y => Q y⦄) :
    P ⊢ ⌜False⌝ := by
  refine entails_trans (RawPtr.read.aligned_of_spec hSpec) ?_
  rw [entails_ipure_iff]
  intro hShifted
  simp [RawPtr.Aligned, Aeneas.Std.UScalarTy.numBits] at hShifted
  omega

/-- Nor can they be owned at `u32`. -/
example (p : MutRawPtr U8) (hAlign : 4 ∣ p.offset) (x : U32) :
    ((p.add 1).retype : MutRawPtr U32) ↦ x ⊢ ⌜False⌝ := by
  intro h hPointsTo
  have hShifted := RawPtr.aligned_of_pointsTo hPointsTo
  simp [RawPtr.Aligned, Aeneas.Std.UScalarTy.numBits] at hShifted
  omega

def reinterpret (x : U32) : Result I32 := do
  let p ← MutRawPtr.alloc x
  let q ← RawPtr.cast_scalar I32 .Mut p
  let y ← RawPtr.read q
  MutRawPtr.free q
  pure y

/-- A value written at one type and read back at another of the same size,
end to end. -/
theorem reinterpret.spec (x : U32) :
    ⦃ emp ⦄ reinterpret x ⦃⇓ y => ⌜y.bv = x.bv⌝⦄ := by
  unfold reinterpret
  step as ⟨p⟩
  step with RawPtr.cast_scalar.spec_of_decode (T' := I32) (M' := .Mut) p x _
    (UScalar.decode_encode_iscalar x rfl) id
  step*
  all_goals simp_all

end SepLogic
