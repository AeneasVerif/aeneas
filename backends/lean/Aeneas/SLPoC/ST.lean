import Aeneas.SLPoC.Exec
import Aeneas.SLPoC.WP
import Aeneas.Tactic.Step.StepStar

/-!
# The state monad `St` and its program logic

`St` is the interaction-tree monad over heap events. This file defines it, gives
it an operational semantics and a certified interpreter, derives its
separation-logic triples, and wires those triples to the `step`/`step*` tactics.
-/

namespace Aeneas.SLPoC

open Aeneas.Data.Coinductive

/-! ## The state monad, its operations and operational semantics -/

universe u v

/-- A partially defined stateful operation: the states it is defined on, the
modification it performs there, and the type of the answer it returns. -/
structure StEvent (Heap : Type u) : Type (max u (v + 1)) where
  /-- The type of the value the operation returns. -/
  Result : Type v
  /-- The heaps the operation is defined on; it is stuck on the others. -/
  pre : Heap → Prop
  /-- The answer and the new heap the operation produces. -/
  modify : (h : Heap) → pre h → Result × Heap

/-- The event signature of stateful computations over `Heap`: one event per
partially defined operation, answered by the value that operation returns.

The effect universe dominates both the heap universe and the universe
containing the result type stored by an event. Answers are lifted into that
common universe; an interaction tree's final result may live elsewhere. -/
def StEvents (Heap : Type u) : Effect.{max u (v + 1)} where
  I := StEvent.{u, v} Heap
  O event := ULift.{max u (v + 1), v} event.Result

abbrev St := ITree (StEvents Heap)

instance St.instLawfulMonad : LawfulMonad St :=
  inferInstanceAs (LawfulMonad (ITree (StEvents Heap)))

/-- The program that performs one event and returns its answer. -/
def trigger (event : StEvent Heap) : St event.Result :=
  ITree.vis (E := StEvents Heap) event fun answer => ITree.ret answer.down

/-- The operational semantics of `St`.
`StEvents.Step e h answer h'` holds when the guard of `e` holds on `h`, and its
modifier returns `answer` and `h'`.  An event whose guard does not hold is
stuck. -/
inductive StEvents.Step {Heap : Type u} :
    (event : (StEvents.{u, v} Heap).I) → Heap →
      (StEvents.{u, v} Heap).O event → Heap → Prop where
  | guardedModify {event : StEvent.{u, v} Heap} {h : Heap} (hPre : event.pre h) :
      Step event h (.up (event.modify h hPre).1) (event.modify h hPre).2

@[reducible]
def StEvents.machine (Heap : Type u) : StateMachine (StEvents.{u, v} Heap) :=
  .ofStep Heap StEvents.Step

theorem StEvents.machine_resolves (Heap : Type u) :
    (StEvents.machine.{u, v} Heap).Resolves :=
  StateMachine.ofStep_resolves Heap StEvents.Step

/-- Big-step relation -/
def Evaluates (m : St α) (h : Heap) (value : α) (h' : Heap) : Prop :=
  (StEvents.machine Heap).Evaluates m h value h'

/-! ## Local event specifications -/

/-- A guarded modification is local when, for every disjoint frame, its guard
holds and its output can be split into an owned result and the unchanged frame.
Quantifying over frames here makes the denotation upward-closed and validates
the frame rule for arbitrary guarded modifications.

This is the raw form of the local specification `theta_ev` of an event, on
plain heap predicates rather than assertions. -/
def theta_evP (event : StEvent Heap) (Q : event.Result → Heap → Prop) (h : Heap) :
    Prop :=
  ∀ frame, PartialCommMonoid.Compatible h frame →
    ∃ hPre : event.pre (h ∪ frame), ∃ h',
      PartialCommMonoid.Compatible h' frame ∧
      (event.modify (h ∪ frame) hPre).2 = h' ∪ frame ∧
      Q (event.modify (h ∪ frame) hPre).1 h'

theorem theta_evP_mono {event : StEvent Heap} {Q Q' : event.Result → Heap → Prop}
    (hQ : ∀ value h', Q value h' → Q' value h') {h : Heap}
    (hWp : theta_evP event Q h) : theta_evP event Q' h := by
  intro frame hDisjoint
  obtain ⟨hPre, h', hDisjoint', hModify, hPost⟩ := hWp frame hDisjoint
  exact ⟨hPre, h', hDisjoint', hModify, hQ _ h' hPost⟩

theorem theta_evP_up_closed {event : StEvent Heap}
    {Q : event.Result → Heap → Prop}
    (hQ : ∀ value h h', Q value h → Heap.Sub h h' → Q value h')
    {h hBig : Heap} (hWp : theta_evP event Q h) (hSub : Heap.Sub h hBig) :
    theta_evP event Q hBig := by
  obtain ⟨rest, hDisjointRest, rfl⟩ := hSub
  intro frame hDisjointFrame
  obtain ⟨hDisjointRestFrame, hDisjointCombined⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hDisjointRest, hDisjointFrame⟩
  have hWp' := hWp (rest ∪ frame) hDisjointCombined
  rw [← PartialCommMonoid.union_assoc hDisjointRest hDisjointFrame] at hWp'
  obtain ⟨hPre, h', hDisjoint', hModify, hPost⟩ := hWp'
  obtain ⟨hDisjoint'Rest, hDisjoint'Frame⟩ :=
    (PartialCommMonoid.compatible_assoc h' rest frame).mpr
      ⟨hDisjointRestFrame, hDisjoint'⟩
  refine ⟨hPre, h' ∪ rest, hDisjoint'Frame, ?_, ?_⟩
  · simpa only [PartialCommMonoid.union_assoc
      hDisjoint'Rest hDisjoint'Frame] using hModify
  · exact hQ _ h' _ hPost (Heap.Sub.union_left hDisjoint'Rest)

/-- Running an event on exactly the heap it owns: the frame is empty, so the
guard holds of that heap and the modification is what the postcondition sees. -/
theorem theta_evP_elim {event : StEvent Heap} {Q : event.Result → Heap → Prop}
    {h : Heap} (hWp : theta_evP event Q h) :
    ∃ hPre : event.pre h,
      Q (event.modify h hPre).1 (event.modify h hPre).2 := by
  have hWp' := hWp empty (PartialCommMonoid.compatible_comm
    (PartialCommMonoid.compatible_empty_left h))
  simp only [Heap.union_empty] at hWp'
  obtain ⟨hPre, h', -, hModify, hPost⟩ := hWp'
  subst h'
  exact ⟨hPre, hPost⟩

theorem theta_evP_frame {event : StEvent Heap} {Q : event.Result → Heap → Prop}
    {H : IProp} {h₁ h₂ : Heap}
    (hDisjoint : PartialCommMonoid.Compatible h₁ h₂)
    (hWp : theta_evP event Q h₁) (hH : H h₂) :
    theta_evP event
      (fun value h' => ∃ u₁ u₂, PartialCommMonoid.Compatible u₁ u₂ ∧
        h' = u₁ ∪ u₂ ∧ Q value u₁ ∧ H u₂) (h₁ ∪ h₂) := by
  intro frame hDisjointFrame
  obtain ⟨hDisjoint₂Frame, hDisjointCombined⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ h₂ frame).mp
      ⟨hDisjoint, hDisjointFrame⟩
  have hWp' := hWp (h₂ ∪ frame) hDisjointCombined
  rw [← PartialCommMonoid.union_assoc hDisjoint hDisjointFrame] at hWp'
  obtain ⟨hPre, h', hDisjoint', hModify, hPost⟩ := hWp'
  obtain ⟨hDisjoint'H₂, hDisjoint'Frame⟩ :=
    (PartialCommMonoid.compatible_assoc h' h₂ frame).mpr
      ⟨hDisjoint₂Frame, hDisjoint'⟩
  refine ⟨hPre, h' ∪ h₂, hDisjoint'Frame, ?_, ?_⟩
  · simpa only [PartialCommMonoid.union_assoc
      hDisjoint'H₂ hDisjoint'Frame] using hModify
  · exact ⟨h', h₂, hDisjoint'H₂, rfl, hPost, hH⟩

/-- The denotation of a single event into the weakest-precondition monad. -/
def theta_ev (event : StEvent Heap) : Wp event.Result where
  wp Q := {
    holds := theta_evP event fun value => (Q value).holds
    up_closed := fun hWp hSub =>
      theta_evP_up_closed
        (fun value _ _ hQ hSub' => (Q value).up_closed hQ hSub') hWp hSub }
  monotone hQ _ hWp := theta_evP_mono (fun value h' => hQ value h') hWp

theorem theta_ev_elim {event : StEvent Heap} {R : IPost event.Result} {h : Heap}
    (hWp : theta_ev event R h) :
    ∃ hPre : event.pre h,
      R (event.modify h hPre).1 (event.modify h hPre).2 :=
  theta_evP_elim (Q := fun value => (R value).holds) hWp

theorem theta_ev_frame (event : StEvent Heap) (Q : IPost event.Result) (H : IProp) :
    theta_ev event Q ∗ H ⊢ theta_ev event (Q ∗+ H) := by
  rintro h ⟨h₁, h₂, hDisjoint, rfl, hWp, hH⟩
  exact theta_evP_frame (Q := fun value => (Q value).holds) hDisjoint hWp hH

/-! ### Total correctness

As for `Aeneas.Std.WP.spec`, total correctness is an inductive judgment. A proof
contains a finite execution ending in `ret`; there is deliberately no
constructor for `ITree.div`. Locality is imposed by `triple`, which quantifies
over arbitrary frames, rather than by the execution judgment itself. -/

inductive TotalSpec (Q : α → Heap → Prop) : St α → Heap → Prop where
  | ret {value : α} {h : Heap} (hPost : Q value h) :
      TotalSpec Q (.ret value) h
  | vis {event : StEvent Heap} {k : (StEvents Heap).O event → St α}
      {h : Heap} (hPre : event.pre h)
      (hNext : TotalSpec Q
        (k (.up (event.modify h hPre).1)) (event.modify h hPre).2) :
      TotalSpec Q (.vis event k) h

/-- Total correctness of `m` on the exact heap `h`. -/
abbrev spec (m : St α) (Q : IPost α) (h : Heap) : Prop :=
  TotalSpec (fun value h' => Q value h') m h

theorem TotalSpec.mono {Q Q' : α → Heap → Prop}
    (hQ : ∀ value h, Q value h → Q' value h)
    {m : St α} {h : Heap} (hSpec : TotalSpec Q m h) :
    TotalSpec Q' m h := by
  induction hSpec with
  | ret hPost => exact .ret (hQ _ _ hPost)
  | vis hPre _ ih => exact .vis hPre ih

theorem spec_mono {Q Q' : IPost α} {m : St α} {h : Heap}
    (hSpec : spec m Q h) (hQ : Q ⊢+ Q') : spec m Q' h :=
  hSpec.mono fun value h' => hQ value h'

theorem TotalSpec.bind {Q₁ : α → Heap → Prop} {Q₂ : β → Heap → Prop}
    {m : St α} {next : α → St β} {h : Heap}
    (hFirst : TotalSpec Q₁ m h)
    (hNext : ∀ value h', Q₁ value h' → TotalSpec Q₂ (next value) h') :
    TotalSpec Q₂ (m >>= next) h := by
  induction hFirst with
  | ret hPost => simpa only [Bind.bind, itree_ret_bind] using hNext _ _ hPost
  | vis hPre _ ih =>
      rw [vis_bind]
      exact .vis hPre ih

theorem spec_bind {Q₁ : IPost α} {Q₂ : IPost β}
    {m : St α} {next : α → St β} {h : Heap}
    (hFirst : spec m Q₁ h)
    (hNext : ∀ value h', Q₁ value h' → spec (next value) Q₂ h') :
    spec (m >>= next) Q₂ h :=
  TotalSpec.bind hFirst hNext

/-- The one-layer view of total correctness. -/
def TotalSpec.view (Q : α → Heap → Prop) (m : St α) (h : Heap) : Prop :=
  ITree.cases
    (motive := fun _ => Prop)
    (fun value => Q value h)
    False
    (fun (event : StEvent Heap) (k : (StEvents Heap).O event → St α) =>
      ∃ hPre : event.pre h,
        TotalSpec Q
          (k (.up (event.modify h hPre).1)) (event.modify h hPre).2)
    m

theorem TotalSpec.view_of {Q : α → Heap → Prop} {m : St α} {h : Heap}
    (hSpec : TotalSpec Q m h) : TotalSpec.view Q m h := by
  induction hSpec with
  | ret hPost =>
      rw [TotalSpec.view, ITree.cases.ret]
      exact hPost
  | vis hPre hNext _ =>
      rw [TotalSpec.view, ITree.cases.vis]
      exact ⟨hPre, hNext⟩

theorem TotalSpec.ret_post {Q : α → Heap → Prop} {value : α} {h : Heap}
    (hSpec : TotalSpec Q (.ret value) h) : Q value h := by
  simpa only [TotalSpec.view, ITree.cases.ret] using hSpec.view_of

theorem TotalSpec.div_false {Q : α → Heap → Prop} {h : Heap}
    (hSpec : TotalSpec Q (.div : St α) h) : False := by
  simpa only [TotalSpec.view, ITree.cases.div] using hSpec.view_of

theorem TotalSpec.vis_view {Q : α → Heap → Prop}
    {event : StEvent Heap} {k : (StEvents Heap).O event → St α} {h : Heap}
    (hSpec : TotalSpec Q (.vis event k) h) :
    ∃ hPre : event.pre h,
      TotalSpec Q
        (k (.up (event.modify h hPre).1)) (event.modify h hPre).2 := by
  simpa only [TotalSpec.view, ITree.cases.vis] using hSpec.view_of

theorem spec_ret (value : α) (Q : IPost α) (h : Heap) :
    spec (ITree.ret value : St α) Q h ↔ Q value h :=
  ⟨TotalSpec.ret_post, fun hPost => .ret hPost⟩

theorem spec_pure (value : α) (Q : IPost α) (h : Heap) :
    spec (Pure.pure value : St α) Q h ↔ Q value h :=
  spec_ret value Q h

/-- Divergence cannot satisfy a total-correctness specification. -/
theorem spec_div (Q : IPost α) (h : Heap) :
    ¬ spec (ITree.div : St α) Q h :=
  TotalSpec.div_false

open Lean.Order in
/-- Total correctness is monotone in the interaction-tree approximation order. -/
theorem spec_mono_le {m m' : St α} (hLe : m ⊑ m') (Q : IPost α)
    {h : Heap} (hSpec : spec m Q h) : spec m' Q h := by
  revert m'
  induction hSpec with
  | ret hPost =>
      intro m' hLe
      rw [ITree.le_unfold] at hLe
      obtain hDiv | ⟨value', hRet, rfl⟩ | ⟨_, _, _, hVis, _, _⟩ := hLe
      · exact absurd hDiv not_ret_div
      · obtain rfl := ret_inj.mp hRet
        exact .ret hPost
      · exact absurd hVis not_vis_ret
  | @vis event k h hPre hNext ih =>
      intro m' hLe
      rw [ITree.le_unfold] at hLe
      obtain hDiv | ⟨_, hRet, _⟩ | ⟨_, k₁, k₂, hVis, rfl, hLe'⟩ := hLe
      · exact absurd hDiv.symm not_div_vis
      · exact absurd hRet.symm not_vis_ret
      · obtain ⟨rfl, hCont⟩ := vis_inj hVis
        obtain rfl := eq_of_heq hCont
        exact .vis hPre (ih (hLe' _))

/-! ## Hoare triples -/

/-- A total-correctness separation triple. The quantified `F` is an arbitrary
frame that the computation must preserve. -/
def triple (P : IPre) (m : St α) (Q : IPost α) : Prop :=
  ∀ F h, (P ∗ F) h → spec m (Q ∗+ F) h

syntax:lead (name := specSyntax)
  "(" term:lead ")" " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
syntax:lead (name := specSyntaxPred)
  "(" term:lead ")" " ⦃" "⇓ " term " ⦄" : term
syntax:lead (name := slSpecSyntax)
  " ⦃" term " ⦄" term:lead
  " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
syntax:lead (name := slSpecSyntaxPred)
  " ⦃" term " ⦄" term:lead " ⦃" "⇓ " term " ⦄" : term

macro_rules
  | `(($m) ⦃⇓ $result => $Q⦄) =>
      `(triple emp $m (fun $result => ⌜$Q⌝))
  | `(($m) ⦃⇓ $Q:term⦄) =>
      `(triple emp $m (fun _ => ⌜$Q⌝))
  | `(⦃$P⦄ $m ⦃⇓ $result => $Q⦄) =>
      `(triple iprop($P) $m (fun $result => iprop($Q)))
  | `(⦃$P⦄ $m ⦃⇓ $Q⦄) =>
      `(triple iprop($P) $m (fun _ => iprop($Q)))

theorem triple_iff (P : IPre) (m : St α) (Q : IPost α) :
    triple P m Q ↔ ∀ F h, (P ∗ F) h → spec m (Q ∗+ F) h :=
  Iff.rfl

theorem triple_apply {P : IPre} {m : St α} {Q : IPost α}
    (hTriple : triple P m Q) {h : Heap} (hPre : P h) :
    spec m Q h := by
  have hSpec := hTriple emp h ((sep_emp_r P).mpr h hPre)
  exact spec_mono hSpec fun value => sep_elim_right (Q value) emp

theorem triple_frame {P : IPre} {m : St α} {Q : IPost α}
    (hTriple : triple P m Q) (H : IProp) :
    triple (P ∗ H) m (Q ∗+ H) := by
  intro F h hPre
  have hSpec := hTriple (H ∗ F) h ((sep_assoc P H F).mp h hPre)
  exact spec_mono hSpec fun value heap =>
    (sep_assoc (Q value) H F).mpr heap

theorem triple_conseq {P' P : IPre} {m : St α}
    {Q' Q : IPost α}
    (hTriple : triple P' m Q') (hP : P ⊢ P')
    (hQ : Q' ⊢+ Q) :
    triple P m Q := by
  intro F h hPre
  have hSpec := hTriple F h (sep_mono hP (entails_refl F) h hPre)
  exact spec_mono hSpec fun value =>
    sep_mono (hQ value) (entails_refl F)

/-- An arbitrary postcondition resource may be discarded.  Since the logic is
affine this is an instance of the rule of consequence. -/
theorem triple_hany_post {P H : IPre} {m : St α} {Q : IPost α}
    (hTriple : triple P m (Q ∗+ H)) :
    triple P m Q :=
  triple_conseq hTriple (entails_refl P)
    (fun value => sep_elim_right (Q value) H)

/-- An arbitrary precondition resource may be discarded. -/
theorem triple_hany_pre {P H : IPre} {m : St α} {Q : IPost α}
    (hTriple : triple P m Q) :
    triple (P ∗ H) m Q :=
  triple_hany_post (triple_frame hTriple H)

theorem triple_ipure {P : Prop} {H : IPre} {m : St α}
    {Q : IPost α}
    (hTriple : P → triple H m Q) :
    triple (⌜P⌝ ∗ H) m Q := by
  intro F h hPre
  have ⟨hP, hHF⟩ :=
    (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
  exact hTriple hP F h hHF

/-- Copy a pure fact of the precondition into the local context *without*
consuming it.  Unlike `triple_ipure` the precondition is unchanged, so the fact
stays available to the framing of the later steps. -/
theorem triple_ipure_keep {P : Prop} {H : IPre} {m : St α}
    {Q : IPost α}
    (hTriple : P → triple (⌜P⌝ ∗ H) m Q) :
    triple (⌜P⌝ ∗ H) m Q := by
  intro F h hPre
  have ⟨hP, _⟩ :=
    (sep_pure_l P (H ∗ F) h).mp ((sep_assoc _ _ _).mp h hPre)
  exact hTriple hP F h hPre

theorem triple_exists {ι : Sort _} {J : ι → IPre} {m : St α}
    {Q : IPost α}
    (hTriple : ∀ x, triple (J x) m Q) :
    triple iprop(∃ x, J x) m Q := by
  intro F h hPre
  obtain ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hJ⟩, hF⟩ := hPre
  exact hTriple x F _ ⟨h₁, h₂, hDisjoint, rfl, hJ, hF⟩

theorem triple_conseq_frame {H₂ : IProp} {H₁ H : IPre}
    {Q₁ Q : IPost α}
    {m : St α}
    (hTriple : triple H₁ m Q₁)
    (hPre : H ⊢ H₁ ∗ H₂)
    (hPost : Q₁ ∗+ H₂ ⊢+ Q) :
    triple H m Q :=
  triple_conseq (triple_frame hTriple H₂) hPre hPost

theorem triple_ipure' {P : Prop} {m : St α} {Q : IPost α}
    (hTriple : P → triple emp m Q) :
    triple ⌜P⌝ m Q := by
  intro F h hPre
  have ⟨hP, hF⟩ := (sep_pure_l P F h).mp hPre
  exact hTriple hP F h ((sep_emp_l F).mpr h hF)

theorem triple_pure {P : IPre} {Q : IPost α} {value : α}
    (hPost : P ⊢ Q value) :
    triple P (pure value : St α) Q := by
  intro F h hPre
  exact .ret (sep_mono hPost (entails_refl F) h hPre)

/-- The specification of a single event is what its denotation says. -/
theorem triple_trigger {event : StEvent Heap} {P : IPre} {Q : IPost event.Result}
    (hWp : P ⊢ theta_ev event Q) : triple P (trigger event) Q := by
  intro F h hPre
  have hEvent : theta_ev event (Q ∗+ F) h :=
    theta_ev_frame event Q F h
      (sep_mono hWp (entails_refl F) h hPre)
  obtain ⟨hGuard, hPost⟩ := theta_ev_elim hEvent
  exact .vis hGuard (.ret hPost)

def guardedModify {α : Type} (pre : Heap → Prop)
    (modify : (h : Heap) → pre h → α × Heap) : St α :=
  trigger ⟨α, pre, modify⟩

/-- The specification of a guarded modification is what its denotation says. -/
theorem triple_guardedModify {α : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → α × Heap} {P : IPre} {Q : IPost α}
    (hWp : P ⊢ theta_ev ⟨α, pre, modify⟩ Q) :
    triple P (guardedModify pre modify) Q :=
  triple_trigger hWp

theorem triple_bind {P : IPre} {Q₁ : IPost α}
    {Q : IPost β} {m : St α} {next : α → St β}
    (hFirst : triple P m Q₁)
    (hNext : ∀ value, triple (Q₁ value) (next value) Q) :
    triple P (m >>= next) Q := by
  intro F h hPre
  apply spec_bind (hFirst F h hPre)
  intro value h' hPost
  exact hNext value F h' hPost

theorem triple_seq {P H : IPre} {Q : IPost β}
    {m₁ : St α} {m₂ : St β}
    (hFirst : triple P m₁ (fun _ => H))
    (hSecond : triple H m₂ Q) :
    triple P (m₁ >>= fun _ => m₂) Q :=
  triple_bind hFirst (fun _ => hSecond)

/-! ## Ramified rules -/

/-- The ramified frame rule. The wand's conclusion is affine, so `Q` alone is
enough to permit leftover resources to be discarded. -/
theorem triple_ramified_frame {α : Type} {P Pm : IPre} {Q Qm : IPost α}
    {m : St α} (hStep : triple Pm m Qm)
    (hPre : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    triple P m Q :=
  triple_conseq_frame hStep hPre (postWand_cancel Qm Q)

/-- The ramified frame rule for a call followed by a continuation. -/
theorem triple_ramified_bind {α β : Type} {P Pm F : IPre} {Qm : IPost α}
    {next : α → St β} {Q : IPost β} {m : St α}
    (hStep : triple Pm m Qm) (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (m >>= next) Q :=
  triple_bind (triple_conseq (triple_frame hStep F) hPre (fun _ => entails_refl _))
    hNext

/-- Rewrite part of a triple's precondition using an entailment. -/
theorem triple_rewrite {α : Type} {H₁ H₂ H₃ : IPre} {Q : IPost α} {m : St α}
    (hPart : H₁ ⊢ H₂) (hRest : triple (H₂ ∗ H₃) m Q) : triple (H₁ ∗ H₃) m Q :=
  triple_conseq hRest (sep_mono hPart (entails_refl H₃)) (fun _ => entails_refl _)

/-! ## Wiring of `step` to separation-logic triples -/

open Lean Elab Meta Tactic

/-- Bind rule used by `step`. It infers a spatial frame and leaves the callee's
postcondition, framed, as the precondition of the continuation. -/
theorem triple_step_bind {α β : Type} {P Pm F : IPre}
    {next : α → St β} {Q : IPost β}
    (m : St α) (Qm : IPost α) (hStep : triple Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (m >>= next) Q :=
  triple_ramified_bind hStep hPre hNext

/-- Rule used by `step` for a terminal monadic call. -/
theorem triple_step_mono {α : Type} {P Pm : IPre} {Q : IPost α}
    (m : St α) (Qm : IPost α) (hStep : triple Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    triple P m Q :=
  triple_ramified_frame hStep hRamified

/-! ## Weakest-precondition tactics -/

/-- Reduce a triple about a terminal `pure v` to the entailment `P ⊢ Q v`. -/
macro "wp_pures" : tactic => `(tactic| apply triple_pure)

/-- Apply a specification to the goal, frame the resources it does not need,
and discharge the resulting entailment with `isimpl`. -/
syntax "wp_apply" (ppSpace colGt term)? (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| wp_apply $[$thm?]? $[by $tac?]?) => do
    let apply ←
      match thm? with
      | some thm => `(tactic| refine triple_ramified_frame $thm ?_)
      | none => `(tactic| refine triple_ramified_frame (by assumption) ?_)
    match tac? with
    | none => `(tactic| ($apply; isimpl))
    | some tac => `(tactic| ($apply; isimpl by $tac))

/-- Re-state an already-proved triple under a weaker postcondition. -/
macro "wp_mono " thm:term : tactic =>
  `(tactic| (apply triple_conseq $thm (entails_refl _) <;> (intro _ <;> iframe)))

theorem forall_unit {p : Unit → Prop} : (∀ value, p value) ↔ p () :=
  ⟨fun h => h (), fun h value => match value with | () => h⟩

/-- The tactic `step` runs on the goals it prepares. A no-op on a goal which is
not a triple. -/
macro "intro_triple" : tactic =>
  `(tactic| (isimp; iintro_shallow))

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 7
    qimp_elim_tactics := #[
      ``forall_eq, ``forall_eq',
      ``forall_unit, ``true_imp_iff
    ]
    intro_tactic := SpecInfo.tac `(tactic| intro_triple)
    discharge_tactic := some `iframe
    to_mvcgen := none
    liftings := #[]
  }

@[step]
theorem ret.spec (value : α) :
    ⦃ emp ⦄ (ITree.ret value : St α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  triple_pure fun _ _ => rfl

@[step]
theorem pure.spec (value : α) :
    ⦃ emp ⦄ (Pure.pure value : St α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  ret.spec value

/-! ## Certified execution -/

/-- What running `m` from `h` produces: the returned value and final heap,
together with the postcondition they satisfy and the evaluation that reaches
them. -/
def Outcome (m : St α) (Q : IPost α) (h : Heap) : Type 1 :=
  { outcome : α × Heap //
      Q outcome.1 outcome.2 ∧ Evaluates m h outcome.1 outcome.2 }

/-- A tree is what its unfolding says it is. -/
theorem eq_of_unfold {m : St α} {shape : ITreeF (StEvents Heap) α (St α)}
    (hm : m.unfold = shape) : m = ITree.fold shape := by
  rw [← hm, ITree.unfold_fold]

theorem eq_ret_of_unfold {m : St α} {value : α} (hm : m.unfold = .ret value) :
    m = ITree.ret value :=
  eq_of_unfold hm

theorem eq_vis_of_unfold {m : St α} {event : StEvent Heap}
    {k : (StEvents Heap).O event → St α} (hm : m.unfold = .vis event k) :
    m = ITree.vis event k :=
  eq_of_unfold hm

/-- At a `vis` node total correctness supplies the guard of the event and total
correctness of the continuation on the modified heap. -/
theorem spec_unfold_vis {m : St α} {event : StEvent Heap}
    {k : (StEvents Heap).O event → St α} {Q : IPost α} {h : Heap}
    (hm : m.unfold = .vis event k) (hSpec : spec m Q h) :
    ∃ hPre : event.pre h,
      spec (k (.up (event.modify h hPre).1)) Q (event.modify h hPre).2 :=
  by
    rw [eq_vis_of_unfold hm] at hSpec
    exact TotalSpec.vis_view hSpec

/-- Run `m` from `h`. The total-correctness proof supplies the guard of each
event, so nothing has to be decided: the guard of an event of `St` is an
arbitrary proposition, and a read through a dangling or mistyped pointer is
stuck rather than erroneous.  Proofs are erased at run time, so this computes.

An interaction tree is coinductive, so this is a partial fixed point rather than
a structural recursion, and it must answer something on a tree with no `ret` in
sight: `runOpt_spec` shows that `none` is unreachable under total correctness,
because `TotalSpec` has no constructor for `ITree.div`. -/
def runOpt (m : St α) (h : Heap) (Q : IPost α) (hSpec : spec m Q h) :
    Option (α × Heap) :=
  match hm : m.unfold with
  | .ret value => some (value, h)
  | .div => none
  | .vis event k =>
      let hNext := spec_unfold_vis hm hSpec
      runOpt (k (.up (event.modify h hNext.choose).1))
        (event.modify h hNext.choose).2 Q hNext.choose_spec
partial_fixpoint

/-- The interpreter answers, its answer satisfies the postcondition, and it is
reached by an evaluation of the machine of `Aeneas.SLPoC.ST`. -/
theorem runOpt_spec (Q : IPost α) (m : St α) (h : Heap) (hSpec : spec m Q h) :
    ∃ outcome : α × Heap, runOpt m h Q hSpec = some outcome ∧
      Q outcome.1 outcome.2 ∧ Evaluates m h outcome.1 outcome.2 := by
  induction hSpec with
  | ret hPost =>
      rw [runOpt.eq_def]
      exact ⟨(_, _), rfl, hPost, StateMachine.Evaluates.pure _ _⟩
  | vis hPre hNext ih =>
      rw [runOpt.eq_def]
      split
      · rename_i value hm
        simp only [unfold_vis] at hm
        cases hm
      · rename_i hm
        simp only [unfold_vis] at hm
        cases hm
      · rename_i event k hm
        simp only [unfold_vis] at hm
        cases hm
        obtain ⟨outcome, hRun, hPost, hEvaluates⟩ := ih
        refine ⟨outcome, ?_, hPost, ?_⟩
        · simpa using hRun
        · exact StateMachine.Evaluates.step (StEvents.Step.guardedModify hPre)
            hEvaluates

theorem runOpt_isSome (Q : IPost α) (m : St α) (h : Heap)
    (hSpec : spec m Q h) : (runOpt m h Q hSpec).isSome := by
  obtain ⟨outcome, hRun, -⟩ := runOpt_spec Q m h hSpec
  rw [hRun]
  rfl

theorem runOpt_get_spec (Q : IPost α) (m : St α) (h : Heap)
    (hSpec : spec m Q h) :
    Q ((runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec)).1
        ((runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec)).2 ∧
      Evaluates m h ((runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec)).1
        ((runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec)).2 := by
  obtain ⟨outcome, hRun, hPost, hEvaluates⟩ := runOpt_spec Q m h hSpec
  have hGet : (runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec) = outcome :=
    Option.some.inj (by
      rw [Option.some_get]
      exact hRun)
  rw [hGet]
  exact ⟨hPost, hEvaluates⟩

/-- Run `m` from `h`, certified: the value and heap come with the postcondition
they satisfy and with the evaluation that reaches them. -/
def run (m : St α) (h : Heap) (Q : IPost α) (hSpec : spec m Q h) :
    Outcome m Q h :=
  ⟨(runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec),
    runOpt_get_spec Q m h hSpec⟩

/-- The value and heap produced by `run`. -/
def exec (m : St α) (h : Heap) (Q : IPost α) (hSpec : spec m Q h) : α × Heap :=
  (run m h Q hSpec).val

theorem exec_post (m : St α) (h : Heap) (Q : IPost α) (hSpec : spec m Q h) :
    Q (exec m h Q hSpec).1 (exec m h Q hSpec).2 :=
  (run m h Q hSpec).property.1

theorem exec_evaluates (m : St α) (h : Heap) (Q : IPost α)
    (hSpec : spec m Q h) :
    Evaluates m h (exec m h Q hSpec).1 (exec m h Q hSpec).2 :=
  (run m h Q hSpec).property.2

/-! ## Executing a specified program -/

/-- Run a program from a heap satisfying the precondition of a proved triple. -/
def runTriple {P : IPre} {Q : IPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) : Outcome m Q h :=
  run m h Q (triple_apply hTriple hPre)

/-- The value and heap produced by a specified program. -/
def execTriple {P : IPre} {Q : IPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) : α × Heap :=
  (runTriple m h hTriple hPre).val

theorem execTriple_post {P : IPre} {Q : IPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) :
    Q (execTriple m h hTriple hPre).1 (execTriple m h hTriple hPre).2 :=
  (runTriple m h hTriple hPre).property.1

theorem execTriple_evaluates {P : IPre} {Q : IPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) :
    Evaluates m h (execTriple m h hTriple hPre).1
      (execTriple m h hTriple hPre).2 :=
  (runTriple m h hTriple hPre).property.2

/-- Run a program proved from `emp` on the empty heap. -/
def execClosed {Q : IPost α} (m : St α) (hTriple : triple emp m Q) : α × Heap :=
  execTriple m empty hTriple trivial

theorem execClosed_post {Q : IPost α} (m : St α) (hTriple : triple emp m Q) :
    Q (execClosed m hTriple).1 (execClosed m hTriple).2 :=
  execTriple_post m empty hTriple trivial

theorem execClosed_evaluates {Q : IPost α} (m : St α)
    (hTriple : triple emp m Q) :
    Evaluates m empty (execClosed m hTriple).1 (execClosed m hTriple).2 :=
  execTriple_evaluates m empty hTriple trivial

end Aeneas.SLPoC
