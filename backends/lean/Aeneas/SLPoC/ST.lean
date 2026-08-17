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

inductive StEvents : Type → Type 1 where
  | AllocPtr {α : Type} (value : α) : StEvents (Ptr α)
  | ReadPtr {α : Type} (p : Ptr α) : StEvents α
  | UpdatePtr {α : Type} (p : Ptr α) (value : α) : StEvents Unit
  | FreePtr {α : Type} (p : Ptr α) : StEvents Unit

abbrev St := FFree StEvents

instance St.instLawfulMonad : LawfulMonad St :=
  inferInstanceAs (LawfulMonad (FFree StEvents))

/-- The operational semantics of `St`.
The transitions of the pointer events: `StEvents.Step e h result h'` holds
when the event `e`, performed on the heap `h`, may answer `result` and leave the
heap `h'`.
An event with no transition, such as a read through a dangling pointer, is stuck. -/
inductive StEvents.Step : {β : Type} → StEvents β → Heap → β → Heap → Prop where
  | alloc {β : Type} {value : β} {h h' : Heap} {p : Ptr β}
      (hFresh : Ptr.fresh h p value h') :
      Step (.AllocPtr value) h p h'
  | read {β : Type} {p : Ptr β} {h : Heap} (hContains : Ptr.contains h p) :
      Step (.ReadPtr p) h (Ptr.read p h hContains) h
  | update {β : Type} {p : Ptr β} {value : β} {h : Heap}
      (hContains : Ptr.contains h p) :
      Step (.UpdatePtr p value) h () (Ptr.update p value h hContains)
  | free {β : Type} {p : Ptr β} {h : Heap} (hContains : Ptr.contains h p) :
      Step (.FreePtr p) h () (Ptr.free p h hContains)

@[reducible]
def StEvents.machine : StateMachine StEvents := .ofStep Heap StEvents.Step

theorem StEvents.machine_resolves : StEvents.machine.Resolves :=
  StateMachine.ofStep_resolves Heap StEvents.Step

/-- Big-step relation -/
def Evaluates (m : St α) (h : Heap) (value : α) (h' : Heap) : Prop :=
  StEvents.machine.Evaluates m h value h'

/-! ## Denotation into the weakest-precondition monad -/

def theta_ev : StEvents α → Wp α
  | .AllocPtr value =>
      pp2wp emp (fun p => p ↦ value)
  | .ReadPtr p =>
      Wp.hexists fun value =>
        pp2wp (p ↦ value) (fun result => iprop(⌜result = value⌝ ∗ p ↦ value))
  | .UpdatePtr p value =>
      Wp.hexists fun oldValue =>
        pp2wp (p ↦ oldValue) (fun _ => p ↦ value)
  | .FreePtr p =>
      Wp.hexists fun value =>
        pp2wp (p ↦ value) (fun _ => emp)

theorem theta_ev_alloc_elim {value : α} {R : SLPost (Ptr α)}
    {h h' : Heap} {p : Ptr α}
    (hWp : theta_ev (.AllocPtr value) R h)
    (hFresh : Ptr.fresh h p value h') :
    R p h' := by
  obtain ⟨h₁, h₂, hDisjoint, rfl, -, hPost⟩ := pp2wp_elim hWp
  obtain ⟨hDisjointFresh, rfl⟩ := Ptr.fresh_eq_singleton_union hFresh
  obtain ⟨hDisjoint₁, hDisjoint₂⟩ :=
    (Finmap.disjoint_union_right (Ptr.singleton p value) h₁ h₂).mp hDisjointFresh
  have hApplied :=
    hPost p (Ptr.singleton p value) (Heap.Sub.refl _) hDisjoint₂
  refine (R p).up_closed hApplied ⟨h₁, ?_, ?_⟩
  · exact (Finmap.disjoint_union_left (Ptr.singleton p value) h₂ h₁).mpr
      ⟨hDisjoint₁, Finmap.Disjoint.symm _ _ hDisjoint⟩
  · rw [Finmap.union_assoc, Finmap.union_comm_of_disjoint hDisjoint]

theorem theta_ev_read_elim {p : Ptr α} {R : SLPost α} {h : Heap}
    (hWp : theta_ev (.ReadPtr p) R h) :
    ∃ hContains : Ptr.contains h p, R (Ptr.read p h hContains) h := by
  obtain ⟨value, hWp⟩ := hWp
  obtain ⟨h₁, h₂, hDisjoint, rfl, hSingle, hPost⟩ := pp2wp_elim hWp
  obtain ⟨rest, hDisjointRest, rfl⟩ := hSingle
  have hContains := Ptr.contains_singleton p value
  refine ⟨Ptr.contains_union_left (Ptr.contains_union_left hContains), ?_⟩
  rw [Ptr.read_union_left (Ptr.contains_union_left hContains),
    Ptr.read_union_left hContains, Ptr.read_singleton]
  exact hPost value (Ptr.singleton p value ∪ rest)
    ((hstar_hpure_l _ _ _).mpr ⟨rfl, Heap.Sub.union_left hDisjointRest⟩)
    hDisjoint

theorem theta_ev_update_elim {p : Ptr α} {value : α} {R : SLPost Unit}
    {h : Heap} (hWp : theta_ev (.UpdatePtr p value) R h) :
    ∃ hContains : Ptr.contains h p, R () (Ptr.update p value h hContains) := by
  obtain ⟨oldValue, hWp⟩ := hWp
  obtain ⟨h₁, h₂, hDisjoint, rfl, hSingle, hPost⟩ := pp2wp_elim hWp
  obtain ⟨rest, hDisjointRest, rfl⟩ := hSingle
  have hContains := Ptr.contains_singleton p oldValue
  have hContainsUnion := Ptr.contains_union_left (h₂ := rest) hContains
  /- Updating the cell turns the footprint into `p ↦ value`, and leaves both the
     unrelated cells the assertion owns and the frame untouched. -/
  have hUpdated :
      Ptr.update p value (Ptr.singleton p oldValue ∪ rest) hContainsUnion =
        Ptr.singleton p value ∪ rest := by
    rw [Ptr.update_union_left p value hContains, Ptr.update_singleton]
  have hDisjointUpdated : Finmap.Disjoint (Ptr.singleton p value ∪ rest) h₂ := by
    rw [← hUpdated]
    exact Ptr.disjoint_update_left hDisjoint hContainsUnion
  have hDisjointRest' : Finmap.Disjoint (Ptr.singleton p value) rest := by
    have := Ptr.disjoint_update_left (value := value) hDisjointRest hContains
    rwa [Ptr.update_singleton] at this
  refine ⟨Ptr.contains_union_left hContainsUnion, ?_⟩
  rw [Ptr.update_union_left p value hContainsUnion, hUpdated]
  exact hPost () (Ptr.singleton p value ∪ rest)
    (Heap.Sub.union_left hDisjointRest') hDisjointUpdated

theorem theta_ev_free_elim {p : Ptr α} {R : SLPost Unit} {h : Heap}
    (hWp : theta_ev (.FreePtr p) R h) :
    ∃ hContains : Ptr.contains h p, R () (Ptr.free p h hContains) := by
  obtain ⟨value, hWp⟩ := hWp
  obtain ⟨h₁, h₂, hDisjoint, rfl, hSingle, hPost⟩ := pp2wp_elim hWp
  obtain ⟨rest, hDisjointRest, rfl⟩ := hSingle
  have hContains := Ptr.contains_singleton p value
  have hContainsUnion := Ptr.contains_union_left (h₂ := rest) hContains
  have hFreed :
      Ptr.free p (Ptr.singleton p value ∪ rest) hContainsUnion = rest := by
    rw [Ptr.free_union_left p hDisjointRest hContains, Ptr.free_singleton]
    simp [empty]
  have hDisjointFreed : Finmap.Disjoint rest h₂ := by
    rw [← hFreed]
    exact Ptr.disjoint_free_left hDisjoint hContainsUnion
  refine ⟨Ptr.contains_union_left hContainsUnion, ?_⟩
  rw [Ptr.free_union_left p hDisjoint hContainsUnion, hFreed]
  exact hPost () rest trivial hDisjointFreed

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
      | AllocPtr value =>
          obtain ⟨p, h, hFresh⟩ := Ptr.exists_fresh value h₀
          exact Exec.event (M := StEvents.machine)
            ⟨p, h, .alloc hFresh,
              ih p h (theta_ev_alloc_elim hEvent hFresh)⟩
      | ReadPtr p =>
          obtain ⟨hContains, hNext⟩ := theta_ev_read_elim hEvent
          exact Exec.event (M := StEvents.machine)
            ⟨_, h₀, .read hContains, ih _ h₀ hNext⟩
      | UpdatePtr p value =>
          obtain ⟨hContains, hNext⟩ := theta_ev_update_elim hEvent
          exact Exec.event (M := StEvents.machine)
            ⟨(), _, .update hContains, ih () _ hNext⟩
      | FreePtr p =>
          obtain ⟨hContains, hNext⟩ := theta_ev_free_elim hEvent
          exact Exec.event (M := StEvents.machine)
            ⟨(), _, .free hContains, ih () _ hNext⟩

/-- The adequacy statement above, spelled out as an evaluation. -/
theorem theta_sound (m : St α) (Q : SLPost α) (h₀ : Heap)
    (hTheta : theta m Q h₀) :
    ∃ value h₁, Evaluates m h₀ value h₁ ∧ Q value h₁ := by
  obtain ⟨m', h₁, hRuns, value, rfl, hQ⟩ :=
    Exec.exists_stop StEvents.machine_resolves (theta_adequate m Q h₀ hTheta)
  exact ⟨value, h₁, hRuns, hQ⟩

theorem theta_ev_frame (event : StEvents α) (Q : SLPost α)
    (H : SLProp) :
    theta_ev event Q ∗ H ⊢ theta_ev event (Q ∗+ H) := by
  cases event with
  | AllocPtr value => exact pp2wp_frame H
  | ReadPtr p => exact Wp.hexists_frame H fun _ => pp2wp_frame H
  | UpdatePtr p value => exact Wp.hexists_frame H fun _ => pp2wp_frame H
  | FreePtr p => exact Wp.hexists_frame H fun _ => pp2wp_frame H

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
explicit `GC` is needed for that, unlike in SLF. -/
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

/-- Discard resources from the declared postcondition.  Since the logic is
affine this is an instance of the rule of consequence. -/
theorem triple_hgc_post {P : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m (Q ∗+ GC)) :
    triple P m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hP
  apply (theta m).monotone
    (fun value h => (hstar_hempty_r (Q value) h).mp) h
  exact (triple_iff P m (Q ∗+ GC)).mp hTriple h hP

theorem triple_frame {P : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m Q) (H : SLProp) :
    triple (P ∗ H) m (Q ∗+ H) := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  rcases hPre with ⟨h₁, h₂, hDisjoint, hEq, hP, hH⟩
  apply theta_frame m Q H h
  exact ⟨h₁, h₂, hDisjoint, hEq,
    (triple_iff P m Q).mp hTriple h₁ hP, hH⟩

/-- Discard resources from the precondition. -/
theorem triple_hgc_pre {P : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m Q) :
    triple (P ∗ GC) m Q :=
  triple_hgc_post (triple_frame hTriple GC)

theorem triple_conseq {P' P : SLPre} {m : St α}
    {Q' Q : SLPost α}
    (hTriple : triple P' m Q') (hP : P ⊢ P')
    (hQ : Q' ⊢+ Q) :
    triple P m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  apply (theta m).monotone hQ h
  exact (triple_iff P' m Q').mp hTriple h (hP h hPre)

/-- An arbitrary postcondition resource may be discarded. -/
theorem triple_hany_post {P H : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m (Q ∗+ H)) :
    triple P m Q :=
  triple_hgc_post (triple_conseq hTriple (himpl_refl P)
    (fun value => hstar_mono (himpl_refl (Q value)) (himpl_hgc_r H)))

/-- An arbitrary precondition resource may be discarded. -/
theorem triple_hany_pre {P H : SLPre} {m : St α} {Q : SLPost α}
    (hTriple : triple P m Q) :
    triple (P ∗ H) m Q :=
  triple_conseq (triple_hgc_pre hTriple)
    (hstar_mono (himpl_refl P) (himpl_hgc_r H))
    (fun _ => himpl_refl _)

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
`sl_pure` is the direct terminal rule for a syntactic return. -/
theorem pure.spec (value : α) :
    ⦃ emp ⦄ (Pure.pure value : St α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  ok.spec value

/-! ## Specified monadic operations -/

def alloc {α : Type} (value : α) : St (Ptr α) :=
  FFree.trigger (.AllocPtr value)

theorem alloc.spec (value : α) :
    ⦃ emp ⦄ alloc value ⦃⇓ p => p ↦ value⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hEmpty
  exact pp2wp_conseq (Q := fun p => p ↦ value)
    (fun _ => himpl_refl _) h hEmpty

def read {α : Type} (p : Ptr α) : St α :=
  FFree.trigger (.ReadPtr p)

theorem read.spec (p : Ptr α) (value : α) :
    ⦃ p ↦ value ⦄ read p
      ⦃⇓ result => ⌜result = value⌝ ∗ p ↦ value⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hSingle
  exact ⟨value, pp2wp_conseq (fun _ => himpl_refl _) h hSingle⟩

def update {α : Type} (p : Ptr α) (value : α) : St Unit :=
  FFree.trigger (.UpdatePtr p value)

theorem update.spec (p : Ptr α) (oldValue newValue : α) :
    ⦃ p ↦ oldValue ⦄ update p newValue ⦃⇓ p ↦ newValue⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hSingle
  exact ⟨oldValue, pp2wp_conseq (fun _ => himpl_refl _) h hSingle⟩

def free {α : Type} (p : Ptr α) : St Unit :=
  FFree.trigger (.FreePtr p)

theorem free.spec (p : Ptr α) (value : α) :
    ⦃ p ↦ value ⦄ free p ⦃⇓ emp⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hSingle
  exact ⟨value, pp2wp_conseq (fun _ => himpl_refl _) h hSingle⟩

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
