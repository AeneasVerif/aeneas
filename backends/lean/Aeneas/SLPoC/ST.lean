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

/-! ## Denotation into the weakest-precondition monad -/

/-- A guarded modification is local when, for every disjoint frame, its guard
holds and its output can be split into an owned result and the unchanged frame.
Quantifying over frames here makes the denotation upward-closed and validates
the frame rule for arbitrary guarded modifications.

This is the raw form of the denotation `theta_ev` of an event, on plain heap
predicates rather than on assertions: it is what the fixed point defining
`theta` below is built from. -/
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

/-! ### The weakest precondition of a program

An interaction tree is coinductive, so the denotation of a program cannot be a
structural recursion over it.  It is instead the **least** fixed point of the
one-step unfolding `ThetaF`, written impredicatively as the intersection of the
pre-fixed points of `ThetaF`, exactly as `Exec` is in `Aeneas.SLPoC.Exec`.

Least, not greatest: `ITree.div`, the bottom element of the tree order and what
an unproductive recursion denotes, gets the precondition `False`.  A program
therefore only satisfies a triple when it terminates, which is what makes the
triples of this file total-correctness triples. -/

/-- One step of `theta`: the weakest precondition of a program in terms of those
of its continuations.  A `ret` node hands the heap to the postcondition, a `vis`
node hands it to the denotation of its event, and the divergent tree has no
precondition at all. -/
def ThetaF (Q : α → Heap → Prop) (X : St α → Heap → Prop) (m : St α)
    (h : Heap) : Prop :=
  match m.unfold with
  | .ret value => Q value h
  | .div => False
  | .vis event k => theta_evP event (fun answer h' => X (k (.up answer)) h') h

/-- The weakest precondition of a program as a raw heap predicate: the least
fixed point of `ThetaF`.

Instantiating the definition with `thetaP Q` itself gives the introduction rule
`thetaP_fold`, and instantiating it with an arbitrary predicate gives the
induction principle `thetaP_induction`; together they give the fixed-point
equation `thetaP_unfold`. -/
def thetaP (Q : α → Heap → Prop) (m : St α) (h : Heap) : Prop :=
  ∀ X : St α → Heap → Prop, (∀ m' h', ThetaF Q X m' h' → X m' h') → X m h

theorem ThetaF_mono {Q Q' : α → Heap → Prop} {X X' : St α → Heap → Prop}
    (hQ : ∀ value h', Q value h' → Q' value h')
    (hX : ∀ m' h', X m' h' → X' m' h') {m : St α} {h : Heap}
    (hStep : ThetaF Q X m h) : ThetaF Q' X' m h := by
  revert hStep
  cases m using ITree.cases with
  | ret value => simp only [ThetaF, unfold_pure]; exact hQ value h
  | div => simp only [ThetaF, unfold_tau]; exact id
  | vis event k =>
      simp only [ThetaF, unfold_vis]
      exact theta_evP_mono fun answer h' => hX (k (.up answer)) h'

theorem thetaP_induction {Q : α → Heap → Prop} {X : St α → Heap → Prop}
    (hClosed : ∀ m' h', ThetaF Q X m' h' → X m' h') {m : St α} {h : Heap}
    (hWp : thetaP Q m h) : X m h :=
  hWp X hClosed

theorem thetaP_fold {Q : α → Heap → Prop} {m : St α} {h : Heap}
    (hStep : ThetaF Q (thetaP Q) m h) : thetaP Q m h :=
  fun _X hClosed =>
    hClosed m h (ThetaF_mono (fun _ _ hQ => hQ)
      (fun _ _ hWp => thetaP_induction hClosed hWp) hStep)

theorem thetaP_unfold {Q : α → Heap → Prop} {m : St α} {h : Heap}
    (hWp : thetaP Q m h) : ThetaF Q (thetaP Q) m h :=
  thetaP_induction (X := ThetaF Q (thetaP Q))
    (fun _ _ hStep =>
      ThetaF_mono (fun _ _ hQ => hQ) (fun _ _ => thetaP_fold) hStep) hWp

theorem thetaP_mono {Q Q' : α → Heap → Prop}
    (hQ : ∀ value h', Q value h' → Q' value h') {m : St α} {h : Heap}
    (hWp : thetaP Q m h) : thetaP Q' m h :=
  thetaP_induction (X := thetaP Q')
    (fun _ _ hStep => thetaP_fold (ThetaF_mono hQ (fun _ _ hX => hX) hStep)) hWp

theorem thetaP_up_closed {Q : α → Heap → Prop}
    (hQ : ∀ value h h', Q value h → Heap.Sub h h' → Q value h')
    {m : St α} {h hBig : Heap} (hWp : thetaP Q m h) (hSub : Heap.Sub h hBig) :
    thetaP Q m hBig := by
  refine thetaP_induction
    (X := fun m' h' => ∀ h'', Heap.Sub h' h'' → thetaP Q m' h'') ?_ hWp hBig hSub
  clear hWp hSub m h hBig
  intro m h hStep hBig hSub
  refine thetaP_fold ?_
  revert hStep
  cases m using ITree.cases with
  | ret value =>
      simp only [ThetaF, unfold_pure]
      exact fun hPost => hQ value h hBig hPost hSub
  | div => simp only [ThetaF, unfold_tau]; exact False.elim
  | vis event k =>
      simp only [ThetaF, unfold_vis]
      intro hEvent
      have hEventBig : theta_evP event
          (fun answer h' =>
            ∀ h'', Heap.Sub h' h'' → thetaP Q (k (.up answer)) h'') hBig :=
        theta_evP_up_closed
          (fun _ _ _ hNext hSub' h'' hSub'' => hNext h'' (hSub'.trans hSub''))
          hEvent hSub
      exact theta_evP_mono (fun _ h' hNext => hNext h' (Heap.Sub.refl h'))
        hEventBig

/-- The denotation of a program into the weakest-precondition monad. -/
def theta (m : St α) : Wp α where
  wp Q := {
    holds := thetaP (fun value => (Q value).holds) m
    up_closed := fun hWp hSub =>
      thetaP_up_closed
        (fun value _ _ hPost hSub' => (Q value).up_closed hPost hSub') hWp hSub }
  monotone hQ _ hWp := thetaP_mono (fun value h' => hQ value h') hWp

/-! ### The equations of `theta` -/

theorem theta_ret_eq (value : α) (Q : IPost α) :
    theta (ITree.ret value : St α) Q = Q value :=
  IProp.ext fun _ =>
    ⟨fun hWp => by simpa only [ThetaF, unfold_ret] using thetaP_unfold hWp,
      fun hPost => thetaP_fold (by simpa only [ThetaF, unfold_ret] using hPost)⟩

theorem theta_pure_eq (value : α) (Q : IPost α) :
    theta (Pure.pure value : St α) Q = Q value :=
  theta_ret_eq value Q

/-- A divergent program has no weakest precondition: no heap and no
postcondition make it work.  This is what makes the triples of this file
total-correctness triples. -/
theorem theta_div (Q : IPost α) (h : Heap) :
    ¬ theta (ITree.div : St α) Q h :=
  fun hWp => by simpa only [ThetaF, unfold_tau] using thetaP_unfold hWp

theorem theta_vis_eq (event : StEvent Heap)
    (k : (StEvents Heap).O event → St α)
    (Q : IPost α) :
    theta (ITree.vis event k : St α) Q =
      theta_ev event fun answer => theta (k (.up answer)) Q :=
  IProp.ext fun h => by
    show thetaP (fun value => (Q value).holds) (ITree.vis event k) h ↔
      theta_evP event
        (fun answer h' =>
          thetaP (fun value => (Q value).holds) (k (.up answer)) h') h
    exact ⟨fun hWp => by simpa only [ThetaF, unfold_vis] using thetaP_unfold hWp,
      fun hEvent => thetaP_fold (by simpa only [ThetaF, unfold_vis] using hEvent)⟩

theorem theta_trigger_eq (event : StEvent Heap) (Q : IPost event.Result) :
    theta (trigger event) Q = theta_ev event Q := by
  simp only [trigger, theta_vis_eq, theta_ret_eq]

open Lean.Order in
/-- `theta` is monotone in the order on interaction trees: a tree refined by
another one — the tree order being the approximation order `partial_fixpoint`
takes its fixed points in, with `ITree.div` at the bottom — has at most the
preconditions of that other one.

This is what makes the weakest precondition of a program defined by
`partial_fixpoint` accessible from those of its finite approximations, and it
says again that divergence is the strongest specification of all. -/
theorem thetaP_mono_le {Q : α → Heap → Prop} {m m' : St α} {h : Heap}
    (hLe : m ⊑ m') (hWp : thetaP Q m h) : thetaP Q m' h := by
  refine thetaP_induction
    (X := fun t h' => ∀ t', t ⊑ t' → thetaP Q t' h') ?_ hWp m' hLe
  clear hWp hLe m m' h
  intro m h hStep m' hLe
  rw [ITree.le_unfold] at hLe
  revert hStep
  cases m using ITree.cases with
  | ret value =>
      simp only [ThetaF, unfold_pure]
      intro hPost
      obtain hDiv | ⟨value', hRet, rfl⟩ | ⟨_, _, _, hVis, _, _⟩ := hLe
      · exact absurd hDiv not_ret_div
      · obtain rfl := ret_inj.mp hRet
        exact thetaP_fold (by simpa only [ThetaF, unfold_ret] using hPost)
      · exact absurd hVis not_vis_ret
  | div => simp only [ThetaF, unfold_tau]; exact False.elim
  | vis event k =>
      simp only [ThetaF, unfold_vis]
      intro hEvent
      obtain hDiv | ⟨_, hRet, _⟩ | ⟨_, k₁, k₂, hVis, rfl, hLe'⟩ := hLe
      · exact absurd hDiv.symm not_div_vis
      · exact absurd hRet.symm not_vis_ret
      · obtain ⟨rfl, hCont⟩ := vis_inj hVis
        obtain rfl := eq_of_heq hCont
        refine thetaP_fold ?_
        simp only [ThetaF, unfold_vis]
        exact theta_evP_mono
          (fun answer _ hNext => hNext (k₂ (.up answer)) (hLe' _)) hEvent

open Lean.Order in
theorem theta_mono_le {m m' : St α} (hLe : m ⊑ m') (Q : IPost α) :
    theta m Q ⊢ theta m' Q :=
  fun _ hWp => thetaP_mono_le hLe hWp

theorem theta_frame (m : St α) (Q : IPost α) (H : IProp) :
    theta m Q ∗ H ⊢ theta m (Q ∗+ H) := by
  rintro h ⟨h₁, h₂, hDisjoint, rfl, hWp, hH⟩
  refine thetaP_induction
    (X := fun m' u₁ => ∀ u₂, PartialCommMonoid.Compatible u₁ u₂ → H u₂ →
      thetaP (fun value => (iprop(Q value ∗ H)).holds) m' (u₁ ∪ u₂))
    ?_ hWp h₂ hDisjoint hH
  clear hWp hDisjoint hH m h₁ h₂
  intro m h hStep h₂ hDisjoint hH
  refine thetaP_fold ?_
  revert hStep
  cases m using ITree.cases with
  | ret value =>
      simp only [ThetaF, unfold_pure]
      exact fun hPost => ⟨h, h₂, hDisjoint, rfl, hPost, hH⟩
  | div => simp only [ThetaF, unfold_tau]; exact False.elim
  | vis event k =>
      simp only [ThetaF, unfold_vis]
      intro hEvent
      refine theta_evP_mono ?_ (theta_evP_frame hDisjoint hEvent hH)
      rintro _ _ ⟨u₁, u₂, hDisjoint', rfl, hNext, hH'⟩
      exact hNext u₂ hDisjoint' hH'

/-! ### `theta` is a monad morphism -/

theorem thetaP_bind_le {Q : β → Heap → Prop} (m : St α) (next : α → St β)
    {h : Heap}
    (hWp : thetaP (fun value h' => thetaP Q (next value) h') m h) :
    thetaP Q (m >>= next) h := by
  refine thetaP_induction (X := fun m' h' => thetaP Q (m' >>= next) h') ?_ hWp
  clear hWp m h
  intro m h hStep
  revert hStep
  cases m using ITree.cases with
  | ret value => simp only [ThetaF, unfold_pure, pure_bind]; exact id
  | div => simp only [ThetaF, unfold_tau]; exact False.elim
  | vis event k =>
      simp only [ThetaF, unfold_vis, vis_bind]
      intro hEvent
      exact thetaP_fold (by simpa only [ThetaF, unfold_vis] using hEvent)

theorem thetaP_bind_ge {Q : β → Heap → Prop} (m : St α) (next : α → St β)
    {h : Heap} (hWp : thetaP Q (m >>= next) h) :
    thetaP (fun value h' => thetaP Q (next value) h') m h := by
  refine (thetaP_induction
    (X := fun t h' => thetaP Q t h' ∧ ∀ m', t = m' >>= next →
      thetaP (fun value u => thetaP Q (next value) u) m' h')
    ?_ hWp).2 m rfl
  clear hWp m h
  intro t h hStep
  have hSelf : thetaP Q t h :=
    thetaP_fold (ThetaF_mono (fun _ _ hPost => hPost) (fun _ _ hX => hX.1) hStep)
  refine ⟨hSelf, ?_⟩
  rintro m rfl
  revert hSelf hStep
  cases m using ITree.cases with
  | ret value =>
      simp only [pure_bind, ThetaF]
      exact fun _ hSelf => thetaP_fold hSelf
  | div =>
      simp only [div_bind, ThetaF, unfold_tau]
      exact fun hFalse _ => hFalse.elim
  | vis event k =>
      simp only [vis_bind, ThetaF, unfold_vis]
      intro hEvent _
      refine thetaP_fold ?_
      simp only [ThetaF, unfold_vis]
      exact theta_evP_mono (fun _ _ hNext => hNext.2 _ rfl) hEvent

/-- `theta` preserves the monad operations up to `Wp` equivalence. -/
def thetaMorphism : MonadMorphism St Wp where
  toFun := theta
  map_pure := by
    intro α value
    refine ⟨fun Q h hPost => ?_, fun Q h hWp => ?_⟩
    · rw [theta_pure_eq]; exact hPost
    · rw [theta_pure_eq] at hWp; exact hWp
  map_bind := by
    intro α β m next
    exact ⟨fun Q h hWp => thetaP_bind_le m next hWp,
      fun Q h hWp => thetaP_bind_ge m next hWp⟩


/-! ## Hoare triples -/

/-- A Hoare triple interpreted by embedding its precondition and its
postcondition into the ordered weakest-precondition monad.

The triple is affine because the *assertions* are: a postcondition holds of any
heap that extends the resources it describes, so a computation may leak. No
explicit affine top is needed. -/
def triple (P : IPre) (m : St α) (Q : IPost α) : Prop :=
  theta m ≤ pp2wp P Q

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

/-- The definition of `triple`, spelled out.

This form is known as a **Texan triple**: it is how Iris states specifications,
```
{{{ P }}} e {{{ RET v; Q }}}  ≜  □ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP e {{ Φ }}
```
the postcondition being passed to the continuation `R` through a wand rather
than asserted directly.  The name is due to the "big" `{{{ … }}}` braces.

Two differences with Iris, both inessential here: the outer entailment is left
at the meta level instead of being internalised as a second wand, and there is
no `□`, since this model has no invariants, no step-indexing and no
higher-order specifications to store a triple in. -/
theorem triple_texan (P : IPre) (m : St α) (Q : IPost α) :
    triple P m Q ↔
      ∀ R : IPost α, P ∗ (Q -∗+ R) ⊢ theta m R :=
  Iff.rfl

theorem triple_iff (P : IPre) (m : St α) (Q : IPost α) :
    triple P m Q ↔ P ⊢ theta m Q := by
  constructor
  · intro hTriple h hP
    exact hTriple Q h (pp2wp_conseq (fun _ => entails_refl _) h hP)
  · intro hTriple R h hPre
    apply (theta m).monotone (postWand_cancel Q R) h
    exact theta_frame m Q (Q -∗+ R) h
      (sep_mono hTriple (entails_refl _) h hPre)

theorem triple_frame {P : IPre} {m : St α} {Q : IPost α}
    (hTriple : triple P m Q) (H : IProp) :
    triple (P ∗ H) m (Q ∗+ H) := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  rcases hPre with ⟨h₁, h₂, hDisjoint, hEq, hP, hH⟩
  apply theta_frame m Q H h
  exact ⟨h₁, h₂, hDisjoint, hEq,
    (triple_iff P m Q).mp hTriple h₁ hP, hH⟩

theorem triple_conseq {P' P : IPre} {m : St α}
    {Q' Q : IPost α}
    (hTriple : triple P' m Q') (hP : P ⊢ P')
    (hQ : Q' ⊢+ Q) :
    triple P m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  apply (theta m).monotone hQ h
  exact (triple_iff P' m Q').mp hTriple h (hP h hPre)

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
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have ⟨hP, hH⟩ := (sep_pure_l P H h).mp hPre
  exact (triple_iff H m Q).mp (hTriple hP) h hH

/-- Copy a pure fact of the precondition into the local context *without*
consuming it.  Unlike `triple_ipure` the precondition is unchanged, so the fact
stays available to the framing of the later steps. -/
theorem triple_ipure_keep {P : Prop} {H : IPre} {m : St α}
    {Q : IPost α}
    (hTriple : P → triple (⌜P⌝ ∗ H) m Q) :
    triple (⌜P⌝ ∗ H) m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have ⟨hP, _⟩ := (sep_pure_l P H h).mp hPre
  exact (triple_iff _ m Q).mp (hTriple hP) h hPre

theorem triple_exists {ι : Sort _} {J : ι → IPre} {m : St α}
    {Q : IPost α}
    (hTriple : ∀ x, triple (J x) m Q) :
    triple iprop(∃ x, J x) m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  rcases hPre with ⟨x, hJ⟩
  exact (triple_iff (J x) m Q).mp (hTriple x) h hJ

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
  apply (triple_iff _ _ _).mpr
  intro h hPre
  exact (triple_iff emp m Q).mp (hTriple hPre) h trivial

theorem triple_pure {P : IPre} {Q : IPost α} {value : α}
    (hPost : P ⊢ Q value) :
    triple P (pure value : St α) Q :=
  (triple_iff _ _ _).mpr (by rw [theta_pure_eq]; exact hPost)

/-- The specification of a single event is what its denotation says. -/
theorem triple_trigger {event : StEvent Heap} {P : IPre} {Q : IPost event.Result}
    (hWp : P ⊢ theta_ev event Q) : triple P (trigger event) Q :=
  (triple_iff _ _ _).mpr (by rw [theta_trigger_eq]; exact hWp)

theorem triple_bind {P : IPre} {Q₁ : IPost α}
    {Q : IPost β} {m : St α} {next : α → St β}
    (hFirst : triple P m Q₁)
    (hNext : ∀ value, triple (Q₁ value) (next value) Q) :
    triple P (m >>= next) Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have hBind :
      Wp.bind (theta m) (fun value => theta (next value)) Q h := by
    apply (theta m).monotone
      (fun value => (triple_iff (Q₁ value) (next value) Q).mp (hNext value))
      h
    exact (triple_iff P m Q₁).mp hFirst h hPre
  exact (thetaMorphism.map_bind m next).1 Q h hBind

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

/-- At a `vis` node the weakest precondition supplies the guard of the event,
and the weakest precondition of the continuation on the modified heap. -/
theorem theta_unfold_vis {m : St α} {event : StEvent Heap}
    {k : (StEvents Heap).O event → St α} {Q : IPost α} {h : Heap}
    (hm : m.unfold = .vis event k) (hWp : theta m Q h) :
    ∃ hPre : event.pre h,
      theta (k (.up (event.modify h hPre).1)) Q (event.modify h hPre).2 :=
  theta_evP_elim (by simpa only [ThetaF, hm] using thetaP_unfold hWp)

/-- Run `m` from `h`. The weakest-precondition proof supplies the guard of each
event, so nothing has to be decided: the guard of an event of `St` is an
arbitrary proposition, and a read through a dangling or mistyped pointer is
stuck rather than erroneous.  Proofs are erased at run time, so this computes.

An interaction tree is coinductive, so this is a partial fixed point rather than
a structural recursion, and it must answer something on a tree with no `ret` in
sight: `runOpt_spec` shows that `none` is unreachable under a weakest
precondition, `theta ITree.div` being `False`. -/
def runOpt (m : St α) (h : Heap) (Q : IPost α) (hWp : theta m Q h) :
    Option (α × Heap) :=
  match hm : m.unfold with
  | .ret value => some (value, h)
  | .div => none
  | .vis event k =>
      let hNext := theta_unfold_vis hm hWp
      runOpt (k (.up (event.modify h hNext.choose).1))
        (event.modify h hNext.choose).2 Q hNext.choose_spec
partial_fixpoint

/-- The interpreter answers, its answer satisfies the postcondition, and it is
reached by an evaluation of the machine of `Aeneas.SLPoC.ST`. -/
theorem runOpt_spec (Q : IPost α) (m : St α) (h : Heap) (hWp : theta m Q h) :
    ∃ outcome : α × Heap, runOpt m h Q hWp = some outcome ∧
      Q outcome.1 outcome.2 ∧ Evaluates m h outcome.1 outcome.2 := by
  refine thetaP_induction
    (X := fun m' h' => ∀ hWp' : theta m' Q h', ∃ outcome : α × Heap,
      runOpt m' h' Q hWp' = some outcome ∧ Q outcome.1 outcome.2 ∧
        Evaluates m' h' outcome.1 outcome.2)
    ?_ hWp hWp
  clear hWp m h
  intro m h hStep hWp
  rw [runOpt.eq_def]
  split
  · rename_i value hm
    simp only [ThetaF, hm] at hStep
    exact ⟨(value, h), rfl, hStep,
      Exec.stop ⟨eq_ret_of_unfold hm, rfl⟩⟩
  · rename_i hm
    -- `theta ITree.div` is `False`, so this branch is unreachable: the
    -- simplification below closes the goal.
    simp only [ThetaF, hm] at hStep
  · rename_i event k hm
    simp only [ThetaF, hm] at hStep
    obtain ⟨hPre, hNext⟩ := theta_evP_elim hStep
    obtain ⟨outcome, hRun, hPost, hEvaluates⟩ :=
      hNext (theta_unfold_vis hm hWp).choose_spec
    refine ⟨outcome, hRun, hPost, ?_⟩
    rw [eq_vis_of_unfold hm]
    exact StateMachine.Evaluates.step (StEvents.Step.guardedModify hPre)
      hEvaluates

theorem runOpt_isSome (Q : IPost α) (m : St α) (h : Heap)
    (hWp : theta m Q h) : (runOpt m h Q hWp).isSome := by
  obtain ⟨outcome, hRun, -⟩ := runOpt_spec Q m h hWp
  rw [hRun]
  rfl

theorem runOpt_get_spec (Q : IPost α) (m : St α) (h : Heap)
    (hWp : theta m Q h) :
    Q ((runOpt m h Q hWp).get (runOpt_isSome Q m h hWp)).1
        ((runOpt m h Q hWp).get (runOpt_isSome Q m h hWp)).2 ∧
      Evaluates m h ((runOpt m h Q hWp).get (runOpt_isSome Q m h hWp)).1
        ((runOpt m h Q hWp).get (runOpt_isSome Q m h hWp)).2 := by
  obtain ⟨outcome, hRun, hPost, hEvaluates⟩ := runOpt_spec Q m h hWp
  have hGet : (runOpt m h Q hWp).get (runOpt_isSome Q m h hWp) = outcome :=
    Option.some.inj (by
      rw [Option.some_get]
      exact hRun)
  rw [hGet]
  exact ⟨hPost, hEvaluates⟩

/-- Run `m` from `h`, certified: the value and heap come with the postcondition
they satisfy and with the evaluation that reaches them. -/
def run (m : St α) (h : Heap) (Q : IPost α) (hWp : theta m Q h) :
    Outcome m Q h :=
  ⟨(runOpt m h Q hWp).get (runOpt_isSome Q m h hWp), runOpt_get_spec Q m h hWp⟩

/-- The value and heap produced by `run`. -/
def exec (m : St α) (h : Heap) (Q : IPost α) (hWp : theta m Q h) : α × Heap :=
  (run m h Q hWp).val

theorem exec_post (m : St α) (h : Heap) (Q : IPost α) (hWp : theta m Q h) :
    Q (exec m h Q hWp).1 (exec m h Q hWp).2 :=
  (run m h Q hWp).property.1

theorem exec_evaluates (m : St α) (h : Heap) (Q : IPost α)
    (hWp : theta m Q h) :
    Evaluates m h (exec m h Q hWp).1 (exec m h Q hWp).2 :=
  (run m h Q hWp).property.2

/-! ## Executing a specified program -/

/-- Run a program from a heap satisfying the precondition of a proved triple. -/
def runTriple {P : IPre} {Q : IPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) : Outcome m Q h :=
  run m h Q ((triple_iff P m Q).mp hTriple h hPre)

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
