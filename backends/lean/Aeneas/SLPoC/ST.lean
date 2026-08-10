import Aeneas.SLPoC.FFree
import Aeneas.SLPoC.Heap
import Aeneas.SLPoC.WP

/-!
# The state monad `St` and its program logic

`St` is the freer monad over the heap events.  This file defines it, gives its
denotation `theta` into the weakest-precondition monad `Wp` of
`Aeneas.SLPoC.WP`, derives the Hoare triples from that denotation, and proves
the specifications of the primitive heap operations.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

/-! ## The state monad, its operations and operational semantics -/

inductive StEvents : Type → Type 1 where
  | Alloc {α : Type} (value : α) : StEvents (Ref α)
  | Read {α : Type} (r : Ref α) : StEvents α
  | Update {α : Type} (r : Ref α) (value : α) : StEvents Unit
  | Free {α : Type} (r : Ref α) : StEvents Unit

abbrev St := FFree StEvents

instance St.instLawfulMonad : LawfulMonad St :=
  inferInstanceAs (LawfulMonad (FFree StEvents))

inductive Evaluates : St α → Heap → α → Heap → Prop where
  | ok (value : α) (h : Heap) :
      Evaluates (.ok value) h value h
  | alloc {β : Type} {value : β} {next : Ref β → St α}
      {h₀ h₁ h₂ : Heap} {r : Ref β} {result : α}
      (hFresh : fresh h₀ r value h₁)
      (hNext : Evaluates (next r) h₁ result h₂) :
      Evaluates (.event (.Alloc value) next) h₀ result h₂
  | read {β : Type} {r : Ref β} {next : β → St α}
      {h₀ h₁ : Heap} {result : α}
      (hContains : contains h₀ r)
      (hNext : Evaluates (next (Heap.read r h₀ hContains)) h₀ result h₁) :
      Evaluates (.event (.Read r) next) h₀ result h₁
  | update {β : Type} {r : Ref β} {value : β} {next : Unit → St α}
      {h₀ h₁ : Heap} {result : α}
      (hContains : contains h₀ r)
      (hNext :
        Evaluates (next ()) (Heap.update r value h₀ hContains) result h₁) :
      Evaluates (.event (.Update r value) next) h₀ result h₁
  | free {β : Type} {r : Ref β} {next : Unit → St α}
      {h₀ h₁ : Heap} {result : α}
      (hContains : contains h₀ r)
      (hNext : Evaluates (next ()) (Heap.free r h₀ hContains) result h₁) :
      Evaluates (.event (.Free r) next) h₀ result h₁

/-! ## Monad operations -/

def alloc {α : Type} (value : α) : St (Ref α) :=
  FFree.trigger (.Alloc value)

def read {α : Type} (r : Ref α) : St α :=
  FFree.trigger (.Read r)

def update {α : Type} (r : Ref α) (value : α) : St Unit :=
  FFree.trigger (.Update r value)

def free {α : Type} (r : Ref α) : St Unit :=
  FFree.trigger (.Free r)

def mut_to_raw {α : Type} (value : α) : St (Ref α) :=
  alloc value

def end_mut_to_raw {α : Type} (r : Ref α) : St α := do
  let value ← read r
  free r
  pure value

/-! ## Denotation into the weakest-precondition monad -/

def theta_ev : StEvents α → Wp α
  | .Alloc value => {
      -- Allocation must satisfy the postcondition for every fresh reference.
      run := fun Q h =>
        ∀ r h', fresh h r value h' → Q r h'
      monotone := by
        intro Q₁ Q₂ hQ h hPre r h' hFresh
        exact hQ _ _ (hPre r h' hFresh)
    }
  | .Read r => {
      run := fun Q h =>
        ∃ hContains : contains h r, Q (Heap.read r h hContains) h
      monotone := by
        intro Q₁ Q₂ hQ h hPre
        obtain ⟨hContains, hPost⟩ := hPre
        exact ⟨hContains, hQ _ _ hPost⟩
    }
  | .Update r value => {
      run := fun Q h =>
        ∃ hContains : contains h r, Q () (Heap.update r value h hContains)
      monotone := by
        intro Q₁ Q₂ hQ h hPre
        obtain ⟨hContains, hPost⟩ := hPre
        exact ⟨hContains, hQ _ _ hPost⟩
    }
  | .Free r => {
      run := fun Q h =>
        ∃ hContains : contains h r, Q () (Heap.free r h hContains)
      monotone := by
        intro Q₁ Q₂ hQ h hPre
        obtain ⟨hContains, hPost⟩ := hPre
        exact ⟨hContains, hQ _ _ hPost⟩
    }

def theta : St α → Wp α
  | .ok value => Wp.pure value
  | .event event next =>
      Wp.bind (theta_ev event) (fun value => theta (next value))

theorem theta_sound (m : St α) (Q : SLPost α) (h₀ : Heap)
    (hTheta : theta m Q h₀) :
    ∃ value h₁, Evaluates m h₀ value h₁ ∧ Q value h₁ := by
  induction m generalizing h₀ with
  | ok value =>
      exact ⟨value, h₀, Evaluates.ok value h₀, hTheta⟩
  | event event next ih =>
      cases event with
      | Alloc value =>
          obtain ⟨r, h, hFresh⟩ := exists_fresh value h₀
          obtain ⟨result, h₁, hEvaluates, hPost⟩ :=
            ih r h (hTheta r h hFresh)
          exact ⟨result, h₁, Evaluates.alloc hFresh hEvaluates, hPost⟩
      | Read r =>
          obtain ⟨hContains, hNext⟩ := hTheta
          obtain ⟨result, h₁, hEvaluates, hPost⟩ :=
            ih (Heap.read r h₀ hContains) h₀ hNext
          exact ⟨result, h₁, Evaluates.read hContains hEvaluates, hPost⟩
      | Update r value =>
          obtain ⟨hContains, hNext⟩ := hTheta
          obtain ⟨result, h₁, hEvaluates, hPost⟩ :=
            ih () (Heap.update r value h₀ hContains) hNext
          exact ⟨result, h₁, Evaluates.update hContains hEvaluates, hPost⟩
      | Free r =>
          obtain ⟨hContains, hNext⟩ := hTheta
          obtain ⟨result, h₁, hEvaluates, hPost⟩ :=
            ih () (Heap.free r h₀ hContains) hNext
          exact ⟨result, h₁, Evaluates.free hContains hEvaluates, hPost⟩

theorem theta_ev_frame (event : StEvents α) (Q : SLPost α)
    (H : SLProp) :
    theta_ev event Q ∗ H ⊢ theta_ev event (Q ∗+ H) := by
  intro h hPre
  rcases hPre with ⟨h₁, h₂, hDisjoint, hEq, hEvent, hH⟩
  subst h
  cases event with
  | Alloc value =>
      intro r h' hFresh
      rcases fresh_frame hDisjoint hFresh with
        ⟨h₁', hFresh₁, hDisjoint', rfl⟩
      exact ⟨h₁', h₂, hDisjoint', rfl,
        hEvent r h₁' hFresh₁, hH⟩
  | Read r =>
      rcases hEvent with ⟨hContains, hPost⟩
      refine ⟨contains_union_left hContains, ?_⟩
      rw [read_union_left hContains]
      exact ⟨h₁, h₂, hDisjoint, rfl, hPost, hH⟩
  | Update r value =>
      rcases hEvent with ⟨hContains, hPost⟩
      refine ⟨contains_union_left hContains, ?_⟩
      rw [update_union_left r value hContains]
      exact ⟨Heap.update r value h₁ hContains, h₂,
        disjoint_update_left hDisjoint hContains, rfl, hPost, hH⟩
  | Free r =>
      rcases hEvent with ⟨hContains, hPost⟩
      refine ⟨contains_union_left hContains, ?_⟩
      rw [free_union_left r hDisjoint hContains]
      exact ⟨Heap.free r h₁ hContains, h₂,
        disjoint_free_left hDisjoint hContains, rfl, hPost, hH⟩

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

/-- A Hoare triple interpreted by embedding its pre/postcondition pair into
the ordered weakest-precondition monad. -/
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

theorem triple_iff (P : SLPre) (m : St α) (Q : SLPost α) :
    triple P m Q ↔ P ⊢ theta m Q := by
  constructor
  · intro hTriple h hP
    exact hTriple Q h ⟨hP, fun _ _ hQ => hQ⟩
  · intro hTriple R h hPre
    exact (theta m).monotone hPre.2 h (hTriple h hPre.1)

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

theorem triple_hpure {P : Prop} {H : SLPre} {m : St α}
    {Q : SLPost α}
    (hTriple : P → triple H m Q) :
    triple (⌜P⌝ ∗ H) m Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have ⟨hP, hH⟩ := (hstar_hpure_l P H h).mp hPre
  exact (triple_iff H m Q).mp (hTriple hP) h hH

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
  exact (triple_iff hempty m Q).mp (hTriple hPre.1) h hPre.2

theorem triple_pure {P : SLPre} {Q : SLPost α} {value : α}
    (hPost : P ⊢ Q value) :
    triple P (pure value : St α) Q := by
  apply (triple_iff _ _ _).mpr
  change P ⊢ Q value
  exact hPost

theorem triple_bind {P : SLPre} {Q₁ : SLPost α}
    {Q : SLPost β} {m : St α} {next : α → St β}
    (hFirst : triple P m Q₁)
    (hNext : ∀ value, triple (Q₁ value) (next value) Q) :
    triple P (m >>= next) Q := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have hFirst' := (triple_iff P m Q₁).mp hFirst h hPre
  have hBind :
      Wp.bind (theta m) (fun value => theta (next value)) Q h := by
    apply (theta m).monotone
      (fun value => (triple_iff (Q₁ value) (next value) Q).mp
        (hNext value))
      h
    exact hFirst'
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
  triple_pure fun _ hEmpty => ⟨rfl, hEmpty⟩

/-- `ok.spec` again, stated through `Pure.pure`.  Both statements are needed:
`step` indexes its database by the head symbol of the program, and a `pure` in
the source is only unfolded to `FFree.ok` once it has been pushed through a
`bind` by a previous step. -/
theorem pure.spec (value : α) :
    ⦃ emp ⦄ (Pure.pure value : St α) ⦃⇓ result => ⌜result = value⌝⦄ :=
  ok.spec value

theorem alloc.spec (value : α) :
    ⦃ emp ⦄ alloc value ⦃⇓ r => r ↦ value⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hEmpty
  subst h
  intro r h' hFresh
  change (r ↦ value) h'
  exact fresh_empty_eq_singleton hFresh

theorem read.spec (r : Ref α) (value : α) :
    ⦃ r ↦ value ⦄ read r
      ⦃⇓ result => ⌜result = value⌝ ∗ r ↦ value⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hSingle
  subst h
  have hContains := contains_singleton r value
  refine ⟨hContains, ?_⟩
  change (⌜Heap.read r (singleton r value) hContains = value⌝ ∗ r ↦ value)
    (singleton r value)
  apply (hstar_hpure_l _ _ _).mpr
  exact ⟨read_singleton r value hContains, rfl⟩

theorem update.spec (r : Ref α) (oldValue newValue : α) :
    ⦃ r ↦ oldValue ⦄ update r newValue ⦃⇓ r ↦ newValue⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hSingle
  subst h
  have hContains := contains_singleton r oldValue
  refine ⟨hContains, ?_⟩
  change (r ↦ newValue)
    (Heap.update r newValue (singleton r oldValue) hContains)
  exact update_singleton r oldValue newValue hContains

theorem free.spec (r : Ref α) (value : α) :
    ⦃ r ↦ value ⦄ free r ⦃⇓ emp⦄ := by
  apply (triple_iff _ _ _).mpr
  intro h hSingle
  subst h
  have hContains := contains_singleton r value
  refine ⟨hContains, ?_⟩
  change emp (Heap.free r (singleton r value) hContains)
  exact free_singleton r value hContains

theorem mut_to_raw.spec {α : Type} (value : α) :
    ⦃ emp ⦄ mut_to_raw value ⦃⇓ r => r ↦ value⦄ := by
  exact alloc.spec value

theorem end_mut_to_raw.spec {α : Type} {value : α} (r : Ref α) :
    ⦃ r ↦ value ⦄ end_mut_to_raw r ⦃⇓ result => ⌜result = value⌝⦄ := by
  unfold end_mut_to_raw
  apply triple_bind (read.spec r value)
  intro result
  apply triple_hpure
  intro hResult
  apply triple_seq (free.spec r value)
  apply triple_pure
  intro h hEmpty
  exact ⟨hResult, hEmpty⟩

end Aeneas.SLPoC
