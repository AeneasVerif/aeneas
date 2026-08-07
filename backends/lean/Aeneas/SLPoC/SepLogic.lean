import Aeneas.Control.OrderedMonad
import Aeneas.SLPoC.Computation

namespace Aeneas.SLPoC

/- Heap predicates describe heap fragments. -/
abbrev HProp := Heap → Prop

/- Postconditions describe both a returned value and a heap fragment. -/
abbrev Postcondition (α : Type) := α → HProp

def himpl (H₁ H₂ : HProp) : Prop :=
  ∀ h, H₁ h → H₂ h

def hequiv (H₁ H₂ : HProp) : Prop :=
  ∀ h, H₁ h ↔ H₂ h

def hempty : HProp :=
  fun h => h = empty

def hpure (P : Prop) : HProp :=
  fun h => P ∧ h = empty

def hsingle {α : Type} (r : ref α) (value : α) : HProp :=
  fun h => h = singleton r value

def hstar (H₁ H₂ : HProp) : HProp :=
  fun h =>
    ∃ h₁ h₂,
      Finmap.Disjoint h₁ h₂ ∧
      h = h₁ ∪ h₂ ∧
      H₁ h₁ ∧
      H₂ h₂

def hexists {α : Sort _} (J : α → HProp) : HProp :=
  fun h => ∃ x, J x h

def qstar {α : Type} (Q : Postcondition α) (H : HProp) :
    Postcondition α :=
  fun value => hstar (Q value) H

def qimpl {α : Type} (Q₁ Q₂ : Postcondition α) : Prop :=
  ∀ value, himpl (Q₁ value) (Q₂ value)

namespace SepLogic

scoped syntax:max "iprop(" term ")" : term
scoped notation "emp" => hempty
scoped syntax "⌜" term "⌝" : term
scoped macro_rules
  | `(⌜$P⌝) => `(hpure $P)
scoped macro_rules
  | `(iprop(∃ $x:ident, $H)) => `(hexists fun $x => iprop($H))
  | `(iprop(∃ $x:ident : $type, $H)) =>
      `(hexists fun ($x : $type) => iprop($H))
  | `(iprop(∃ ($x:ident : $type), $H)) =>
      `(hexists fun ($x : $type) => iprop($H))
  | `(iprop($H)) => `($H)
scoped infixr:35 " ∗ " => hstar
scoped infixr:40 " ∗+ " => qstar
scoped infix:25 " ⊢ " => himpl
scoped infix:25 " ⊢+ " => qimpl
scoped infix:25 " ⊣⊢ " => hequiv
scoped notation:52 r:53 " ↦ " value:53 => hsingle r value

end SepLogic

open scoped SepLogic

theorem hstar_assoc (H₁ H₂ H₃ : HProp) :
    (H₁ ∗ H₂) ∗ H₃ ⊣⊢ H₁ ∗ (H₂ ∗ H₃) := by
  intro h
  constructor
  · rintro ⟨h₁₂, h₃, hDisjoint₁₂₃, hEq, hStar₁₂, hH₃⟩
    rcases hStar₁₂ with ⟨h₁, h₂, hDisjoint₁₂, hEq₁₂, hH₁, hH₂⟩
    have hDisjoint₁₂₃' : Finmap.Disjoint (h₁ ∪ h₂) h₃ := by
      simpa [hEq₁₂] using hDisjoint₁₂₃
    have ⟨hDisjoint₁₃, hDisjoint₂₃⟩ :=
      (Finmap.disjoint_union_left h₁ h₂ h₃).mp hDisjoint₁₂₃'
    refine ⟨h₁, h₂ ∪ h₃, ?_, ?_, hH₁, ?_⟩
    · exact (Finmap.disjoint_union_right h₁ h₂ h₃).mpr
        ⟨hDisjoint₁₂, hDisjoint₁₃⟩
    · calc
        h = h₁₂ ∪ h₃ := hEq
        _ = (h₁ ∪ h₂) ∪ h₃ := congrArg (· ∪ h₃) hEq₁₂
        _ = h₁ ∪ (h₂ ∪ h₃) := Finmap.union_assoc
    · exact ⟨h₂, h₃, hDisjoint₂₃, rfl, hH₂, hH₃⟩
  · rintro ⟨h₁, h₂₃, hDisjoint₁₂₃, hEq, hH₁, hStar₂₃⟩
    rcases hStar₂₃ with ⟨h₂, h₃, hDisjoint₂₃, hEq₂₃, hH₂, hH₃⟩
    have hDisjoint₁₂₃' : Finmap.Disjoint h₁ (h₂ ∪ h₃) := by
      simpa [hEq₂₃] using hDisjoint₁₂₃
    have ⟨hDisjoint₁₂, hDisjoint₁₃⟩ :=
      (Finmap.disjoint_union_right h₁ h₂ h₃).mp hDisjoint₁₂₃'
    refine ⟨h₁ ∪ h₂, h₃, ?_, ?_, ?_, hH₃⟩
    · exact (Finmap.disjoint_union_left h₁ h₂ h₃).mpr
        ⟨hDisjoint₁₃, hDisjoint₂₃⟩
    · calc
        h = h₁ ∪ h₂₃ := hEq
        _ = h₁ ∪ (h₂ ∪ h₃) := congrArg (h₁ ∪ ·) hEq₂₃
        _ = (h₁ ∪ h₂) ∪ h₃ := Finmap.union_assoc.symm
    · exact ⟨h₁, h₂, hDisjoint₁₂, rfl, hH₁, hH₂⟩

theorem hstar_comm (H₁ H₂ : HProp) :
    H₁ ∗ H₂ ⊣⊢ H₂ ∗ H₁ := by
  intro h
  constructor
  · rintro ⟨h₁, h₂, hDisjoint, hEq, hH₁, hH₂⟩
    exact ⟨h₂, h₁, Finmap.Disjoint.symm h₁ h₂ hDisjoint,
      hEq.trans (Finmap.union_comm_of_disjoint hDisjoint), hH₂, hH₁⟩
  · rintro ⟨h₂, h₁, hDisjoint, hEq, hH₂, hH₁⟩
    exact ⟨h₁, h₂, Finmap.Disjoint.symm h₂ h₁ hDisjoint,
      hEq.trans (Finmap.union_comm_of_disjoint hDisjoint), hH₁, hH₂⟩

theorem hstar_hempty_l (H : HProp) :
    emp ∗ H ⊣⊢ H := by
  intro h
  constructor
  · rintro ⟨h₁, h₂, _, hEq, hEmpty, hH⟩
    change h₁ = empty at hEmpty
    subst h₁
    simp only [empty, Finmap.empty_union] at hEq
    subst h
    exact hH
  · intro hH
    exact ⟨∅, h, Finmap.disjoint_empty h, by simp, rfl, hH⟩

theorem hstar_hexists {α : Sort _} (J : α → HProp) (H : HProp) :
    iprop(∃ x, J x) ∗ H ⊣⊢ iprop(∃ x, J x ∗ H) := by
  intro h
  constructor
  · rintro ⟨h₁, h₂, hDisjoint, hEq, ⟨x, hJ⟩, hH⟩
    exact ⟨x, h₁, h₂, hDisjoint, hEq, hJ, hH⟩
  · rintro ⟨x, h₁, h₂, hDisjoint, hEq, hJ, hH⟩
    exact ⟨h₁, h₂, hDisjoint, hEq, ⟨x, hJ⟩, hH⟩

theorem hstar_hpure_l (P : Prop) (H : HProp) :
    ⌜P⌝ ∗ H ⊣⊢ fun h => P ∧ H h := by
  intro h
  constructor
  · rintro ⟨h₁, h₂, _, hEq, ⟨hP, hEmpty⟩, hH⟩
    change h₁ = empty at hEmpty
    subst h₁
    simp only [empty, Finmap.empty_union] at hEq
    subst h
    exact ⟨hP, hH⟩
  · rintro ⟨hP, hH⟩
    exact ⟨∅, h, Finmap.disjoint_empty h, by simp, ⟨hP, rfl⟩, hH⟩

/-- Monotone predicate transformers, corresponding to `Wᴾᵘʳᵉ` in
"Dijkstra Monads for All". -/
structure Wp (α : Type) where
  run : Postcondition α → HProp
  monotone :
    ∀ {Q₁ Q₂ : Postcondition α},
      (∀ value, himpl (Q₁ value) (Q₂ value)) →
      himpl (run Q₁) (run Q₂)

namespace Wp

instance : CoeFun (Wp α) (fun _ => Postcondition α → HProp) :=
  ⟨Wp.run⟩

def pure (value : α) : Wp α :=
  ⟨fun Q => Q value, fun hQ => hQ value⟩

def bind (m : Wp α) (next : α → Wp β) : Wp β :=
  ⟨fun Q => m (fun value => next value Q), fun hQ =>
    m.monotone (fun value => (next value).monotone hQ)⟩

/-- Specification weakening is reverse implication between preconditions. -/
instance : LE (Wp α) where
  le w₁ w₂ := ∀ Q, himpl (w₂ Q) (w₁ Q)

instance : Preorder (Wp α) where
  le_refl w Q h hPre := hPre
  le_trans w₁ w₂ w₃ h₁₂ h₂₃ Q h hPre :=
    h₁₂ Q h (h₂₃ Q h hPre)

/-- Equivalence of specifications induced by the `Wp` preorder. -/
def Equiv (w₁ w₂ : Wp α) : Prop :=
  w₁ ≤ w₂ ∧ w₂ ≤ w₁

instance : Setoid (Wp α) where
  r := Equiv
  iseqv := {
    refl := fun w => ⟨le_refl w, le_refl w⟩
    symm := fun h => ⟨h.2, h.1⟩
    trans := fun h₁₂ h₂₃ =>
      ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₂₃.2 h₁₂.2⟩
  }

theorem equiv_iff {w₁ w₂ : Wp α} :
    w₁ ≈ w₂ ↔ w₁ ≤ w₂ ∧ w₂ ≤ w₁ :=
  Iff.rfl

@[refl]
theorem equiv_refl (w : Wp α) : w ≈ w :=
  ⟨le_refl w, le_refl w⟩

theorem bind_mono {m₁ m₂ : Wp α} {next₁ next₂ : α → Wp β}
    (hm : m₁ ≤ m₂) (hnext : ∀ value, next₁ value ≤ next₂ value) :
    bind m₁ next₁ ≤ bind m₂ next₂ := by
  intro Q h hBind
  apply m₁.monotone (fun value => hnext value Q) h
  exact hm (fun value => next₂ value Q) h hBind

theorem bind_congr {m₁ m₂ : Wp α} {next₁ next₂ : α → Wp β}
    (hm : m₁ ≈ m₂) (hnext : ∀ value, next₁ value ≈ next₂ value) :
    bind m₁ next₁ ≈ bind m₂ next₂ :=
  ⟨bind_mono hm.1 (fun value => (hnext value).1),
    bind_mono hm.2 (fun value => (hnext value).2)⟩

end Wp

instance : Monad Wp where
  pure := Wp.pure
  bind := Wp.bind

instance : LawfulMonad Wp where
  map_const := by intros; rfl
  id_map := by intros; rfl
  seqLeft_eq := by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := by intros; rfl
  pure_bind := by intros; rfl
  bind_assoc := by intros; rfl
  bind_pure_comp := by intros; rfl
  bind_map := by intros; rfl

instance : OrderedMonad Wp where
  bind_mono := Wp.bind_mono

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
        ∃ hLive : live h r, Q (read r h hLive) h
      monotone := by
        intro Q₁ Q₂ hQ h hPre
        obtain ⟨hLive, hPost⟩ := hPre
        exact ⟨hLive, hQ _ _ hPost⟩
    }
  | .Update r value => {
      run := fun Q h =>
        ∃ hLive : live h r, Q () (update r value h hLive)
      monotone := by
        intro Q₁ Q₂ hQ h hPre
        obtain ⟨hLive, hPost⟩ := hPre
        exact ⟨hLive, hQ _ _ hPost⟩
    }
  | .Free r => {
      run := fun Q h =>
        ∃ hLive : live h r, Q () (free r h hLive)
      monotone := by
        intro Q₁ Q₂ hQ h hPre
        obtain ⟨hLive, hPost⟩ := hPre
        exact ⟨hLive, hQ _ _ hPost⟩
    }

def theta : St α → Wp α
  | .ok value => Wp.pure value
  | .event event next =>
      Wp.bind (theta_ev event) (fun value => theta (next value))

theorem theta_ev_frame (event : StEvents α) (Q : Postcondition α)
    (H : HProp) :
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
      rcases hEvent with ⟨hLive, hPost⟩
      refine ⟨live_union_left hLive, ?_⟩
      rw [read_union_left hLive]
      exact ⟨h₁, h₂, hDisjoint, rfl, hPost, hH⟩
  | Update r value =>
      rcases hEvent with ⟨hLive, hPost⟩
      refine ⟨live_union_left hLive, ?_⟩
      rw [update_union_left r value hLive]
      exact ⟨update r value h₁ hLive, h₂,
        disjoint_update_left hDisjoint hLive, rfl, hPost, hH⟩
  | Free r =>
      rcases hEvent with ⟨hLive, hPost⟩
      refine ⟨live_union_left hLive, ?_⟩
      rw [free_union_left r hLive]
      exact ⟨free r h₁ hLive, h₂,
        disjoint_free_left hDisjoint hLive, rfl, hPost, hH⟩

theorem theta_frame (m : St α) (Q : Postcondition α) (H : HProp) :
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

/-- Embed a precondition/postcondition pair into a weakest-precondition
transformer. -/
def pp2wp (P : HProp) (Q : Postcondition α) : Wp α where
  run := fun R h =>
    P h ∧ ∀ value h', Q value h' → R value h'
  monotone := by
    intro R₁ R₂ hR h hPre
    exact ⟨hPre.1, fun value h' hPost =>
      hR value h' (hPre.2 value h' hPost)⟩

/-- A Hoare triple interpreted by embedding its pre/postcondition pair into
the ordered weakest-precondition monad. -/
def triple (P : HProp) (m : St α) (Q : Postcondition α) : Prop :=
  theta m ≤ pp2wp P Q

namespace SepLogic

scoped notation:25 "{{ " P " }} " m " {{ " Q " }}" => triple P m Q

end SepLogic

theorem triple_iff (P : HProp) (m : St α) (Q : Postcondition α) :
    {{ P }} m {{ Q }} ↔ P ⊢ theta m Q := by
  constructor
  · intro hTriple h hP
    exact hTriple Q h ⟨hP, fun _ _ hQ => hQ⟩
  · intro hTriple R h hPre
    exact (theta m).monotone hPre.2 h (hTriple h hPre.1)

theorem triple_frame {P : HProp} {m : St α} {Q : Postcondition α}
    (hTriple : {{ P }} m {{ Q }}) (H : HProp) :
    {{ P ∗ H }} m {{ Q ∗+ H }} := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  rcases hPre with ⟨h₁, h₂, hDisjoint, hEq, hP, hH⟩
  apply theta_frame m Q H h
  exact ⟨h₁, h₂, hDisjoint, hEq,
    (triple_iff P m Q).mp hTriple h₁ hP, hH⟩

theorem triple_conseq {P' P : HProp} {m : St α}
    {Q' Q : Postcondition α}
    (hTriple : {{ P' }} m {{ Q' }}) (hP : P ⊢ P')
    (hQ : Q' ⊢+ Q) :
    {{ P }} m {{ Q }} := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  apply (theta m).monotone hQ h
  exact (triple_iff P' m Q').mp hTriple h (hP h hPre)

theorem triple_hpure {P : Prop} {H : HProp} {m : St α}
    {Q : Postcondition α}
    (hTriple : P → {{ H }} m {{ Q }}) :
    {{ ⌜P⌝ ∗ H }} m {{ Q }} := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  have ⟨hP, hH⟩ := (hstar_hpure_l P H h).mp hPre
  exact (triple_iff H m Q).mp (hTriple hP) h hH

theorem triple_hexists {ι : Sort _} {J : ι → HProp} {m : St α}
    {Q : Postcondition α}
    (hTriple : ∀ x, {{ J x }} m {{ Q }}) :
    {{ iprop(∃ x, J x) }} m {{ Q }} := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  rcases hPre with ⟨x, hJ⟩
  exact (triple_iff (J x) m Q).mp (hTriple x) h hJ

theorem triple_conseq_frame {H₂ H₁ H : HProp} {Q₁ Q : Postcondition α}
    {m : St α}
    (hTriple : {{ H₁ }} m {{ Q₁ }})
    (hPre : H ⊢ H₁ ∗ H₂)
    (hPost : Q₁ ∗+ H₂ ⊢+ Q) :
    {{ H }} m {{ Q }} :=
  triple_conseq (triple_frame hTriple H₂) hPre hPost

theorem triple_hpure' {P : Prop} {m : St α} {Q : Postcondition α}
    (hTriple : P → {{ emp }} m {{ Q }}) :
    {{ ⌜P⌝ }} m {{ Q }} := by
  apply (triple_iff _ _ _).mpr
  intro h hPre
  exact (triple_iff hempty m Q).mp (hTriple hPre.1) h hPre.2

end Aeneas.SLPoC
