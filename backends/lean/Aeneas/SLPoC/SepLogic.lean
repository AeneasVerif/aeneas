import Aeneas.Control.OrderedMonad
import Aeneas.SLPoC.Computation

namespace Aeneas.SLPoC

/- Heap predicates describe heap fragments. -/
abbrev SLProp := Heap → Prop

/- Preconditions are separation-logic propositions. -/
abbrev SLPre := SLProp

/- Postconditions describe both a returned value and a heap fragment. -/
abbrev SLPost (α : Type) := α → SLProp

def himpl (H₁ H₂ : SLProp) : Prop :=
  ∀ h, H₁ h → H₂ h

def hequiv (H₁ H₂ : SLProp) : Prop :=
  ∀ h, H₁ h ↔ H₂ h

def hempty : SLProp :=
  fun h => h = empty

def hpure (P : Prop) : SLProp :=
  fun h => P ∧ h = empty

def hsingle {α : Type} (r : Ref α) (value : α) : SLProp :=
  fun h => h = singleton r value

def hstar (H₁ H₂ : SLProp) : SLProp :=
  fun h =>
    ∃ h₁ h₂,
      Finmap.Disjoint h₁ h₂ ∧
      h = h₁ ∪ h₂ ∧
      H₁ h₁ ∧
      H₂ h₂

def hexists {α : Sort _} (J : α → SLProp) : SLProp :=
  fun h => ∃ x, J x h

def qstar {α : Type} (Q : SLPost α) (H : SLProp) :
    SLPost α :=
  fun value => hstar (Q value) H

def qimpl {α : Type} (Q₁ Q₂ : SLPost α) : Prop :=
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

theorem himpl_refl (H : SLProp) : H ⊢ H :=
  fun _ hH => hH

theorem himpl_trans {P Q R : SLProp} (hPQ : P ⊢ Q) (hQR : Q ⊢ R) :
    P ⊢ R :=
  fun h hP => hQR h (hPQ h hP)

theorem himpl_of_eq {P Q : SLProp} (hEq : P = Q) : P ⊢ Q := by
  subst Q
  exact himpl_refl P

theorem hequiv_eq {P Q : SLProp} (hEquiv : P ⊣⊢ Q) : P = Q := by
  funext h
  exact propext (hEquiv h)

theorem hstar_assoc (H₁ H₂ H₃ : SLProp) :
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

theorem hstar_comm (H₁ H₂ : SLProp) :
    H₁ ∗ H₂ ⊣⊢ H₂ ∗ H₁ := by
  intro h
  constructor
  · rintro ⟨h₁, h₂, hDisjoint, hEq, hH₁, hH₂⟩
    exact ⟨h₂, h₁, Finmap.Disjoint.symm h₁ h₂ hDisjoint,
      hEq.trans (Finmap.union_comm_of_disjoint hDisjoint), hH₂, hH₁⟩
  · rintro ⟨h₂, h₁, hDisjoint, hEq, hH₂, hH₁⟩
    exact ⟨h₁, h₂, Finmap.Disjoint.symm h₂ h₁ hDisjoint,
      hEq.trans (Finmap.union_comm_of_disjoint hDisjoint), hH₁, hH₂⟩

theorem hstar_assoc_eq (H₁ H₂ H₃ : SLProp) :
    ((H₁ ∗ H₂) ∗ H₃) = (H₁ ∗ (H₂ ∗ H₃)) :=
  hequiv_eq (hstar_assoc H₁ H₂ H₃)

theorem hstar_comm_eq (H₁ H₂ : SLProp) :
    (H₁ ∗ H₂) = (H₂ ∗ H₁) :=
  hequiv_eq (hstar_comm H₁ H₂)

instance : Std.Associative hstar where
  assoc := hstar_assoc_eq

instance : Std.Commutative hstar where
  comm := hstar_comm_eq

theorem hstar_mono {P₁ P₂ Q₁ Q₂ : SLProp}
    (hP : P₁ ⊢ P₂) (hQ : Q₁ ⊢ Q₂) :
    P₁ ∗ Q₁ ⊢ P₂ ∗ Q₂ := by
  intro h
  rintro ⟨h₁, h₂, hDisjoint, hEq, hP₁, hQ₁⟩
  exact ⟨h₁, h₂, hDisjoint, hEq, hP h₁ hP₁, hQ h₂ hQ₁⟩

theorem hstar_hempty_l (H : SLProp) :
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

theorem hstar_hempty_r (H : SLProp) :
    H ∗ emp ⊣⊢ H := by
  intro h
  exact (hstar_comm H emp h).trans (hstar_hempty_l H h)

theorem hstar_hempty_l_eq (H : SLProp) :
    (emp ∗ H) = H :=
  hequiv_eq (hstar_hempty_l H)

theorem hstar_hempty_r_eq (H : SLProp) :
    (H ∗ emp) = H :=
  hequiv_eq (hstar_hempty_r H)

instance : Std.LawfulIdentity hstar hempty where
  left_id := hstar_hempty_l_eq
  right_id := hstar_hempty_r_eq

theorem hstar_hexists {α : Sort _} (J : α → SLProp) (H : SLProp) :
    iprop(∃ x, J x) ∗ H ⊣⊢ iprop(∃ x, J x ∗ H) := by
  intro h
  constructor
  · rintro ⟨h₁, h₂, hDisjoint, hEq, ⟨x, hJ⟩, hH⟩
    exact ⟨x, h₁, h₂, hDisjoint, hEq, hJ, hH⟩
  · rintro ⟨x, h₁, h₂, hDisjoint, hEq, hJ, hH⟩
    exact ⟨h₁, h₂, hDisjoint, hEq, ⟨x, hJ⟩, hH⟩

theorem hstar_hpure_l (P : Prop) (H : SLProp) :
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

theorem hpure_hstar_intro {P : Prop} (H : SLProp) (hP : P) :
    H ⊢ ⌜P⌝ ∗ H := by
  intro h hH
  exact ⟨∅, h, Finmap.disjoint_empty h, by simp, ⟨hP, rfl⟩, hH⟩

theorem hpure_elim (P : Prop) :
    ⌜P⌝ ⊢ emp :=
  fun _ hP => hP.2

theorem hstar_to_emp {P Q : SLProp}
    (hP : P ⊢ emp) (hQ : Q ⊢ emp) :
    P ∗ Q ⊢ emp :=
  himpl_trans (hstar_mono hP hQ)
    (fun h => (hstar_hempty_l emp h).mp)

theorem hstar_elim_right {P F : SLProp} (hF : F ⊢ emp) :
    P ∗ F ⊢ P :=
  himpl_trans (hstar_mono (himpl_refl P) hF)
    (fun h => (hstar_hempty_r P h).mp)

/-- Monotone predicate transformers, corresponding to `Wᴾᵘʳᵉ` in
"Dijkstra Monads for All". -/
structure Wp (α : Type) where
  run : SLPost α → SLPre
  monotone :
    ∀ {Q₁ Q₂ : SLPost α},
      (∀ value, himpl (Q₁ value) (Q₂ value)) →
      himpl (run Q₁) (run Q₂)

namespace Wp

instance : CoeFun (Wp α) (fun _ => SLPost α → SLPre) :=
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

/-- Embed a precondition/postcondition pair into a weakest-precondition
transformer. -/
def pp2wp (P : SLPre) (Q : SLPost α) : Wp α where
  run := fun R h =>
    P h ∧ ∀ value h', Q value h' → R value h'
  monotone := by
    intro R₁ R₂ hR h hPre
    exact ⟨hPre.1, fun value h' hPost =>
      hR value h' (hPre.2 value h' hPost)⟩

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
    ⦃ r ↦ oldValue ⦄ update r newValue
      ⦃⇓ r ↦ newValue⦄ := by
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

def mut_to_raw {α : Type} (value : α) : St (Ref α) :=
  alloc value

def end_mut_to_raw {α : Type} (r : Ref α) : St α := do
  let value ← read r
  free r
  pure value

theorem mut_to_raw.spec {α : Type} (value : α) :
    ⦃ emp ⦄ mut_to_raw value ⦃⇓ r => r ↦ value⦄ := by
  exact alloc.spec value

theorem end_mut_to_raw.spec {α : Type} {value : α} (r : Ref α) :
    ⦃ r ↦ value ⦄ end_mut_to_raw r
      ⦃⇓ result => ⌜result = value⌝⦄ := by
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
