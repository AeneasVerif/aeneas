import Aeneas.SLPoC.FFree
import Aeneas.SLPoC.WP

/-!
# The state monad `St` and its program logic

`St` is the freer monad over the pointer events of `Aeneas.SLPoC.RustHeap`.
This file defines it, gives it an operational semantics by a state machine in
the sense of `Aeneas.SLPoC.StateMachine`, gives its denotation `theta` into the
weakest-precondition monad `Wp` of `Aeneas.SLPoC.WP`, derives the Hoare triples
from that denotation, and proves the specifications of the pointer
operations.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

/-! ## The state monad, its operations and operational semantics -/

universe u v

/-! The type of partially defined stateful operations. -/
inductive StEvents (Heap : Type u) : Type v → Type (max u v) where
  | GuardedModify {α : Type v} (pre : Heap → Prop)
      (modify : (h : Heap) → pre h → α × Heap) : StEvents Heap α

abbrev St := FFree (StEvents Heap)

instance St.instLawfulMonad : LawfulMonad St :=
  inferInstanceAs (LawfulMonad (FFree (StEvents Heap)))

/-- The operational semantics of `St`.
`StEvents.Step e h result h'` holds when the guard of `e` holds on `h`, and its
modifier returns `result` and `h'`.  An event whose guard does not hold is
stuck. -/
inductive StEvents.Step :
    {β : Type} → StEvents Heap β → Heap → β → Heap → Prop where
  | guardedModify {β : Type} {pre : Heap → Prop}
      {modify : (h : Heap) → pre h → β × Heap} {h : Heap}
      (hPre : pre h) :
      Step (.GuardedModify pre modify) h (modify h hPre).1 (modify h hPre).2

@[reducible]
def StEvents.machine : StateMachine (StEvents Heap) :=
  .ofStep Heap StEvents.Step

theorem StEvents.machine_resolves : StEvents.machine.Resolves :=
  StateMachine.ofStep_resolves Heap StEvents.Step

/-- Big-step relation -/
def Evaluates (m : St α) (h : Heap) (value : α) (h' : Heap) : Prop :=
  StEvents.machine.Evaluates m h value h'

/-! ## Denotation into the weakest-precondition monad -/

/-- A guarded modification is local when, for every disjoint frame, its guard
holds and its output can be split into an owned result and the unchanged frame.
Quantifying over frames here makes the denotation upward-closed and validates
the frame rule for arbitrary guarded modifications. -/
def theta_ev : StEvents Heap α → Wp α
  | .GuardedModify pre modify =>
      { run := fun Q =>
          { holds := fun h =>
              ∀ frame, Finmap.Disjoint h frame →
                ∃ hPre : pre (h ∪ frame), ∃ h',
                  Finmap.Disjoint h' frame ∧
                  (modify (h ∪ frame) hPre).2 = h' ∪ frame ∧
                  Q (modify (h ∪ frame) hPre).1 h'
            up_closed := by
              rintro h hBig hWp ⟨rest, hDisjointRest, rfl⟩ frame hDisjointFrame
              obtain ⟨hDisjointHFrame, hDisjointRestFrame⟩ :=
                (Finmap.disjoint_union_left h rest frame).mp hDisjointFrame
              have hDisjointCombined : Finmap.Disjoint h (rest ∪ frame) :=
                (Finmap.disjoint_union_right h rest frame).mpr
                  ⟨hDisjointRest, hDisjointHFrame⟩
              have hWp' := hWp (rest ∪ frame) hDisjointCombined
              rw [← Finmap.union_assoc] at hWp'
              obtain ⟨hPre, h', hDisjoint', hModify, hQ⟩ := hWp'
              obtain ⟨hDisjoint'Rest, hDisjoint'Frame⟩ :=
                (Finmap.disjoint_union_right h' rest frame).mp hDisjoint'
              refine ⟨?_, h' ∪ rest, ?_, ?_, ?_⟩
              · simpa [Finmap.union_assoc] using hPre
              · exact (Finmap.disjoint_union_left h' rest frame).mpr
                  ⟨hDisjoint'Frame, hDisjointRestFrame⟩
              · simpa [Finmap.union_assoc] using hModify
              · exact (Q _).up_closed hQ (Heap.Sub.union_left hDisjoint'Rest)
          }
        monotone := by
          intro Q₁ Q₂ hQ h hWp frame hDisjoint
          obtain ⟨hPre, h', hDisjoint', hModify, hPost⟩ :=
            hWp frame hDisjoint
          exact ⟨hPre, h', hDisjoint', hModify,
            hQ _ h' hPost⟩
      }

theorem theta_ev_elim {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → α × Heap}
    {R : SLPost α} {h : Heap}
    (hWp : theta_ev (.GuardedModify pre modify) R h) :
    ∃ hPre : pre h,
      R (modify h hPre).1 (modify h hPre).2 := by
  obtain ⟨hPre, h', -, hModify, hPost⟩ :=
    hWp empty (Finmap.Disjoint.symm _ _ (Finmap.disjoint_empty h))
  simp [empty] at hPre hModify hPost
  subst h'
  exact ⟨hPre, hPost⟩

def theta : St α → Wp α
  | .ok value => Wp.pure value
  | .event event next =>
      Wp.bind (theta_ev event) (fun value => theta (next value))

/-- Adequacy — `StateMachineAdequate` of *Program Logics à la Carte*, for the
machine `StEvents.machine`: a program whose weakest precondition holds has an
execution that stops on a returned value satisfying the postcondition. -/
theorem theta_adequate (m : St α) (Q : SLPost α) (h₀ : Heap)
    (hTheta : theta m Q h₀) :
    Exec StEvents.machine m h₀
      fun m' h => ∃ value, m' = .ok value ∧ Q value h := by
  induction m generalizing h₀ with
  | ok value =>
      exact ⟨value, rfl, hTheta⟩
  | event event next ih =>
      have hEvent : theta_ev event (fun value => theta (next value) Q) h₀ :=
        hTheta
      cases event with
      | GuardedModify pre modify =>
          obtain ⟨hPre, hNext⟩ := theta_ev_elim hEvent
          exact Exec.event (M := StEvents.machine)
            ⟨_, _, .guardedModify hPre, ih _ _ hNext⟩

/-- Every terminating evaluation satisfies the postcondition. -/
theorem theta_sound (m : St α) (Q : SLPost α) (h₀ : Heap)
    (hTheta : theta m Q h₀) :
    ∀ value h₁, Evaluates m h₀ value h₁ → Q value h₁ := by
  induction m generalizing h₀ with
  | ok result =>
      rintro value h₁ ⟨hValue, hHeap⟩
      cases hValue
      cases hHeap
      exact hTheta
  | event event next ih =>
      change theta_ev event (fun result => theta (next result) Q) h₀ at hTheta
      intro value h₁ hEval
      rcases hEval with hStop | ⟨result, h, hStep, hEval⟩
      · simp at hStop
      · cases hStep with
        | guardedModify hPre =>
            obtain ⟨hPre', hNext⟩ := theta_ev_elim hTheta
            have hProof : hPre' = hPre := Subsingleton.elim _ _
            subst hPre'
            exact ih _ _ hNext _ _ hEval

theorem theta_ev_frame (event : StEvents Heap α) (Q : SLPost α)
    (H : SLProp) :
    theta_ev event Q ∗ H ⊢ theta_ev event (Q ∗+ H) := by
  cases event with
  | GuardedModify pre modify =>
      rintro h ⟨h₁, h₂, hDisjoint, rfl, hWp, hH⟩ frame hDisjointFrame
      obtain ⟨hDisjoint₁Frame, hDisjoint₂Frame⟩ :=
        (Finmap.disjoint_union_left h₁ h₂ frame).mp hDisjointFrame
      have hDisjointCombined : Finmap.Disjoint h₁ (h₂ ∪ frame) :=
        (Finmap.disjoint_union_right h₁ h₂ frame).mpr
          ⟨hDisjoint, hDisjoint₁Frame⟩
      have hWp' := hWp (h₂ ∪ frame) hDisjointCombined
      rw [← Finmap.union_assoc] at hWp'
      obtain ⟨hPre, h', hDisjoint', hModify, hQ⟩ := hWp'
      obtain ⟨hDisjoint'H₂, hDisjoint'Frame⟩ :=
        (Finmap.disjoint_union_right h' h₂ frame).mp hDisjoint'
      refine ⟨?_, h' ∪ h₂, ?_, ?_, ?_⟩
      · simpa [Finmap.union_assoc] using hPre
      · exact (Finmap.disjoint_union_left h' h₂ frame).mpr
          ⟨hDisjoint'Frame, hDisjoint₂Frame⟩
      · simpa [Finmap.union_assoc] using hModify
      · exact ⟨h', h₂, hDisjoint'H₂, rfl, hQ, hH⟩

theorem theta_frame (m : St α) (Q : SLPost α) (H : SLProp) :
    theta m Q ∗ H ⊢ theta m (Q ∗+ H) := by
  induction m with
  | ok value =>
      intro h hPre
      exact hPre
  | event event next ih =>
      intro h hPre
      apply (theta_ev event).monotone (fun value => ih value) h
      exact theta_ev_frame event (fun value => theta (next value) Q) H h hPre

/-- `theta` preserves the monad operations up to `Wp` equivalence. -/
def thetaMorphism : MonadMorphism St Wp where
  toFun := theta
  map_pure := by
    intro α value
    rfl
  map_bind := by
    intro α β m next
    induction m
    · rfl
    · rename_i γ event k ih
      change
        Wp.bind (theta_ev event) (fun value => theta (k value >>= next)) ≈
          Wp.bind (theta_ev event) (fun value =>
            Wp.bind (theta (k value)) (fun result => theta (next result)))
      exact Wp.bind_congr (by rfl) ih

/-! ## Hoare triples -/

/-- A Hoare triple interpreted by embedding its precondition and its
postcondition into the ordered weakest-precondition monad.

The triple is affine because the *assertions* are: a postcondition holds of any
heap that extends the resources it describes, so a computation may leak.  No
explicit affine top is needed for that, unlike in SLF. -/
def triple (P : SLPre) (m : St α) (Q : SLPost α) : Prop :=
  theta m ≤ pp2wp P Q

namespace SepLogic

scoped syntax:lead (name := specSyntax)
  "(" term:lead ")" " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
scoped syntax:lead (name := specSyntaxPred)
  "(" term:lead ")" " ⦃" "⇓ " term " ⦄" : term
scoped syntax:lead (name := slSpecSyntax)
  " ⦃" term " ⦄" term:lead
  " ⦃" "⇓ " Lean.Parser.Term.funBinder " => " term " ⦄" : term
scoped syntax:lead (name := slSpecSyntaxPred)
  " ⦃" term " ⦄" term:lead " ⦃" "⇓ " term " ⦄" : term

scoped macro_rules
  | `(($m) ⦃⇓ $result => $Q⦄) =>
      `(triple emp $m (fun $result => ⌜$Q⌝))
  | `(($m) ⦃⇓ $Q:term⦄) =>
      `(triple emp $m (fun _ => ⌜$Q⌝))
  | `(⦃$P⦄ $m ⦃⇓ $result => $Q⦄) =>
      `(triple iprop($P) $m (fun $result => iprop($Q)))
  | `(⦃$P⦄ $m ⦃⇓ $Q⦄) =>
      `(triple iprop($P) $m (fun _ => iprop($Q)))

end SepLogic

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
theorem triple_texan (P : SLPre) (m : St α) (Q : SLPost α) :
    triple P m Q ↔
      ∀ R : SLPost α, P ∗ (Q -∗+ R) ⊢ theta m R :=
  Iff.rfl

theorem triple_iff (P : SLPre) (m : St α) (Q : SLPost α) :
    triple P m Q ↔ P ⊢ theta m Q := by
  constructor
  · intro hTriple h hP
    exact hTriple Q h (pp2wp_conseq (fun _ => himpl_refl _) h hP)
  · intro hTriple R h hPre
    apply (theta m).monotone (qwand_cancel Q R) h
    exact theta_frame m Q (Q -∗+ R) h
      (hstar_mono hTriple (himpl_refl _) h hPre)

theorem triple_frame {P : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m Q) (H : SLProp) :
    triple (P ∗ H) m (Q ∗+ H) := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  rcases hPre with ⟨h₁, h₂, hDisjoint, hEq, hP, hH⟩
  apply theta_frame m Q H h
  exact ⟨h₁, h₂, hDisjoint, hEq,
    (triple_iff P m Q).mp hTriple h₁ hP, hH⟩

theorem triple_conseq {P' P : SLPre} {m : St α}
    {Q' Q : SLPost α}
    (hTriple : triple P' m Q') (hP : P ⊢ P')
    (hQ : Q' ⊢+ Q) :
    triple P m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  apply (theta m).monotone hQ h
  exact (triple_iff P' m Q').mp hTriple h (hP h hPre)

/-- An arbitrary postcondition resource may be discarded.  Since the logic is
affine this is an instance of the rule of consequence. -/
theorem triple_hany_post {P H : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m (Q ∗+ H)) :
    triple P m Q :=
  triple_conseq hTriple (himpl_refl P)
    (fun value => hstar_elim_right (Q value) H)

/-- An arbitrary precondition resource may be discarded. -/
theorem triple_hany_pre {P H : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m Q) :
    triple (P ∗ H) m Q :=
  triple_hany_post (triple_frame hTriple H)

theorem triple_hpure {P : Prop} {H : SLPre} {m : St α}
    {Q : SLPost α}
    (hTriple : P → triple H m Q) :
    triple (⌜P⌝ ∗ H) m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have ⟨hP, hH⟩ := (hstar_hpure_l P H h).mp hPre
  exact (triple_iff H m Q).mp (hTriple hP) h hH

/-- Copy a pure fact of the precondition into the local context *without*
consuming it.  Unlike `triple_hpure` the precondition is unchanged, so the fact
stays available to the framing of the later steps. -/
theorem triple_hpure_keep {P : Prop} {H : SLPre} {m : St α}
    {Q : SLPost α}
    (hTriple : P → triple (⌜P⌝ ∗ H) m Q) :
    triple (⌜P⌝ ∗ H) m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have ⟨hP, _⟩ := (hstar_hpure_l P H h).mp hPre
  exact (triple_iff _ m Q).mp (hTriple hP) h hPre

theorem triple_hexists {ι : Sort _} {J : ι → SLPre} {m : St α}
    {Q : SLPost α}
    (hTriple : ∀ x, triple (J x) m Q) :
    triple iprop(∃ x, J x) m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  rcases hPre with ⟨x, hJ⟩
  exact (triple_iff (J x) m Q).mp (hTriple x) h hJ

theorem triple_conseq_frame {H₂ : SLProp} {H₁ H : SLPre}
    {Q₁ Q : SLPost α}
    {m : St α}
    (hTriple : triple H₁ m Q₁)
    (hPre : H ⊢ H₁ ∗ H₂)
    (hPost : Q₁ ∗+ H₂ ⊢+ Q) :
    triple H m Q :=
  triple_conseq (triple_frame hTriple H₂) hPre hPost

theorem triple_hpure' {P : Prop} {m : St α} {Q : SLPost α}
    (hTriple : P → triple emp m Q) :
    triple ⌜P⌝ m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  exact (triple_iff hempty m Q).mp (hTriple hPre) h trivial

theorem triple_pure {P : SLPre} {Q : SLPost α} {value : α}
    (hPost : P ⊢ Q value) :
    triple P (pure value : St α) Q :=
  (triple_iff _ _ _).mpr hPost

theorem triple_bind {P : SLPre} {Q₁ : SLPost α}
    {Q : SLPost β} {m : St α} {next : α → St β}
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

theorem triple_seq {P H : SLPre} {Q : SLPost β}
    {m₁ : St α} {m₂ : St β}
    (hFirst : triple P m₁ (fun _ => H))
    (hSecond : triple H m₂ Q) :
    triple P (m₁ >>= fun _ => m₂) Q :=
  triple_bind hFirst (fun _ => hSecond)

/-- Terminal `pure`, i.e. SLF's `xval`.  Registering it as a `step` lemma is what
lets `step*` walk all the way to the `return` of a monadic function instead of
stopping just before it. -/
theorem ok.spec (value : α) :
    ⦃ emp ⦄ (FFree.ok value : St α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  triple_pure fun _ _ => rfl

/-- `ok.spec` again, stated through `Pure.pure`.  Both it and `ok.spec` remain
registered for calls in binds and ordinary ramified-frame automation.
`step` applies the direct terminal rule for a syntactic return instead. -/
theorem pure.spec (value : α) :
    ⦃ emp ⦄ (Pure.pure value : St α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  ok.spec value

/-! ## Specified monadic operations -/

def guardedModify {α : Type} (pre : Heap → Prop)
    (modify : (h : Heap) → pre h → α × Heap) : St α :=
  FFree.trigger (.GuardedModify pre modify)

def alloc {α : Type} (value : α) : St (Ptr α) :=
  guardedModify (fun _ => True) fun h _ =>
    (Ptr.freshPtr α h, Ptr.freshHeap h value)

theorem alloc.spec (value : α) :
    ⦃ emp ⦄ alloc value ⦃⇓ p => p ↦ value⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h _ frame hDisjoint
  let p := Ptr.freshPtr α (h ∪ frame)
  have hFresh := Ptr.fresh_freshPtr value (h ∪ frame)
  obtain ⟨hDisjointFresh, hFreshHeap⟩ :=
    Ptr.fresh_eq_singleton_union hFresh
  obtain ⟨hDisjointFreshH, hDisjointFreshFrame⟩ :=
    (Finmap.disjoint_union_right (Ptr.singleton p value) h frame).mp
      hDisjointFresh
  exact ⟨trivial, Ptr.singleton p value ∪ h,
    (Finmap.disjoint_union_left (Ptr.singleton p value) h frame).mpr
      ⟨hDisjointFreshFrame, hDisjoint⟩,
    hFreshHeap.trans Finmap.union_assoc.symm,
    Heap.Sub.union_left hDisjointFreshH⟩

def read {α : Type} (p : Ptr α) : St α :=
  guardedModify (fun h => Ptr.contains h p) fun h hContains =>
    (Ptr.read p h hContains, h)

theorem read.spec (p : Ptr α) (value : α) :
    ⦃ p ↦ value ⦄ read p
      ⦃⇓ result => ⌜result = value⌝ ∗ p ↦ value⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hSingle
  have hContains := Ptr.contains_of_sub hSingle
  intro frame hDisjoint
  have hContainsFrame := Ptr.contains_union_left (h₂ := frame) hContains
  have hReadFrame :
      Ptr.read p (h ∪ frame) hContainsFrame = value := by
    rw [Ptr.read_union_left hContains]
    obtain ⟨rest, hDisjointRest, rfl⟩ := hSingle
    have hContainsCell := Ptr.contains_singleton p value
    rw [show (hContains :
          Ptr.contains (Ptr.singleton p value ∪ rest) p) =
        Ptr.contains_union_left hContainsCell from Subsingleton.elim _ _,
      Ptr.read_union_left hContainsCell, Ptr.read_singleton]
  refine ⟨hContainsFrame, h, hDisjoint, rfl, ?_⟩
  exact (hstar_hpure_l _ _ h).mpr ⟨hReadFrame, hSingle⟩

def update {α : Type} (p : Ptr α) (value : α) : St Unit :=
  guardedModify (fun h => Ptr.contains h p) fun h hContains =>
    ((), Ptr.update p value h hContains)

theorem update.spec (p : Ptr α) (oldValue newValue : α) :
    ⦃ p ↦ oldValue ⦄ update p newValue ⦃⇓ p ↦ newValue⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hSingle
  have hContains := Ptr.contains_of_sub hSingle
  intro frame hDisjoint
  have hContainsFrame := Ptr.contains_union_left (h₂ := frame) hContains
  have hUpdateFrame :
      Ptr.update p newValue (h ∪ frame) hContainsFrame =
        Ptr.update p newValue h hContains ∪ frame := by
    simpa only [Ptr.update_union_left] using
      Ptr.update_union_left (h₂ := frame) p newValue hContains
  have hDisjointUpdated :
      Finmap.Disjoint (Ptr.update p newValue h hContains) frame :=
    Ptr.disjoint_update_left hDisjoint hContains
  obtain ⟨rest, hDisjointRest, rfl⟩ := hSingle
  have hContainsCell := Ptr.contains_singleton p oldValue
  have hContainsUnion := Ptr.contains_union_left (h₂ := rest) hContainsCell
  have hUpdated :
      Ptr.update p newValue (Ptr.singleton p oldValue ∪ rest) hContainsUnion =
        Ptr.singleton p newValue ∪ rest := by
    rw [Ptr.update_union_left p newValue hContainsCell, Ptr.update_singleton]
  have hDisjointRest' : Finmap.Disjoint (Ptr.singleton p newValue) rest := by
    have := Ptr.disjoint_update_left (value := newValue) hDisjointRest hContainsCell
    rwa [Ptr.update_singleton] at this
  refine ⟨hContainsFrame,
    Ptr.update p newValue (Ptr.singleton p oldValue ∪ rest) hContainsUnion,
    ?_, ?_, ?_⟩
  · exact Ptr.disjoint_update_left hDisjoint hContainsUnion
  · simpa only [show hContainsFrame =
        Ptr.contains_union_left hContainsUnion from Subsingleton.elim _ _,
      show hContains = hContainsUnion from Subsingleton.elim _ _] using hUpdateFrame
  · rw [hUpdated]
    exact Heap.Sub.union_left hDisjointRest'

def free {α : Type} (p : Ptr α) : St Unit :=
  guardedModify (fun h => Ptr.contains h p) fun h hContains =>
    ((), Ptr.free p h hContains)

theorem free.spec (p : Ptr α) (value : α) :
    ⦃ p ↦ value ⦄ free p ⦃⇓ emp⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hSingle
  have hContains := Ptr.contains_of_sub hSingle
  intro frame hDisjoint
  have hContainsFrame := Ptr.contains_union_left (h₂ := frame) hContains
  refine ⟨hContainsFrame, Ptr.free p h hContains,
    Ptr.disjoint_free_left hDisjoint hContains, ?_, trivial⟩
  simpa only [show hContainsFrame =
      Ptr.contains_union_left hContains from Subsingleton.elim _ _] using
    Ptr.free_union_left p hDisjoint hContains

def mut_to_raw {α : Type} (value : α) : St (Ptr α) :=
  alloc value

theorem mut_to_raw.spec {α : Type} (value : α) :
    ⦃ emp ⦄ mut_to_raw value ⦃⇓ p => p ↦ value⦄ := by
  exact alloc.spec value

def end_mut_to_raw {α : Type} (p : Ptr α) : St α := do
  let value ← read p
  free p
  pure value

theorem end_mut_to_raw.spec {α : Type} {value : α} (p : Ptr α) :
    ⦃ p ↦ value ⦄ end_mut_to_raw p ⦃⇓ result => ⌜result = value⌝⦄ := by
  unfold end_mut_to_raw
  apply triple_bind (read.spec p value)
  intro result
  apply triple_hpure
  intro hResult
  apply triple_seq (free.spec p value)
  exact triple_pure fun _ _ => hResult

end Aeneas.SLPoC
