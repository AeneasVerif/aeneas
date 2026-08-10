import Aeneas.Control.OrderedMonad
import Aeneas.SLPoC.Heap

/-!
# Separation-logic assertions and the weakest-precondition monad

Heap predicates (`SLProp`) with the usual separation-logic connectives — the
separating conjunction and the magic wand included — and the monad `Wp` of
monotone predicate transformers they live in.  Nothing here mentions the state
monad: its denotation into `Wp` and the Hoare triples it induces are in
`Aeneas.SLPoC.ST`.
-/

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

/-- Extraction of a pure fact from the left-hand side of an entailment.  This is
SLF's `himpl_hstar_hpure_l`, the workhorse of `xpull`. -/
theorem himpl_hpure_l {P : Prop} {H H' : SLProp} (h : P → H ⊢ H') :
    ⌜P⌝ ∗ H ⊢ H' := by
  intro heap hStar
  have ⟨hP, hH⟩ := (hstar_hpure_l P H heap).mp hStar
  exact h hP heap hH

/-- Introduction of an existential quantifier on the left-hand side of an
entailment (SLF's `himpl_hexists_l`). -/
theorem himpl_hexists_l {ι : Sort _} {H : SLProp} {J : ι → SLProp}
    (h : ∀ x, J x ⊢ H) : hexists J ⊢ H :=
  fun heap hJ => h hJ.choose heap hJ.choose_spec

/-- Instantiation of an existential quantifier on the right-hand side of an
entailment (SLF's `himpl_hexists_r`).  `xsimpl` uses it with a metavariable for
`x`, which the cancellation phase then instantiates by unification. -/
theorem himpl_hexists_r {ι : Sort _} {H : SLProp} {J : ι → SLProp} (x : ι)
    (h : H ⊢ J x) : H ⊢ hexists J :=
  fun heap hH => ⟨x, h heap hH⟩

/-- Float an existential out of the left factor of a separating conjunction. -/
theorem hstar_hexists_l_eq {ι : Sort _} (J : ι → SLProp) (H : SLProp) :
    (hexists J ∗ H) = iprop(∃ x, J x ∗ H) :=
  hequiv_eq (hstar_hexists J H)

/-- Float an existential out of the right factor of a separating conjunction. -/
theorem hstar_hexists_r_eq {ι : Sort _} (H : SLProp) (J : ι → SLProp) :
    (H ∗ hexists J) = iprop(∃ x, H ∗ J x) := by
  rw [hstar_comm_eq, hstar_hexists_l_eq]
  exact hequiv_eq fun _ => ⟨fun ⟨x, hx⟩ => ⟨x, (hstar_comm _ _ _).mp hx⟩,
    fun ⟨x, hx⟩ => ⟨x, (hstar_comm _ _ _).mp hx⟩⟩

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

/-! ## The magic wand

`H₁ -∗ H₂` describes the heap fragments that, extended with a fragment
satisfying `H₁`, satisfy `H₂`.  Following SLF it is *defined* in terms of the
other connectives rather than semantically, which makes all of its properties
provable from the algebraic laws alone. -/

/-- Universal quantification over heap predicates. -/
def hforall {ι : Sort _} (J : ι → SLProp) : SLProp :=
  fun h => ∀ x, J x h

/-- The magic wand of SLF (`\-*`). -/
def hwand (H₁ H₂ : SLProp) : SLProp :=
  hexists fun H₀ => iprop(H₀ ∗ ⌜H₁ ∗ H₀ ⊢ H₂⌝)

/-- The magic wand between postconditions (SLF's `\--*`).  Note that it is a
heap predicate, not a postcondition. -/
def qwand {α : Type} (Q₁ Q₂ : SLPost α) : SLProp :=
  hforall fun value => hwand (Q₁ value) (Q₂ value)

namespace SepLogic

@[inherit_doc hwand] scoped infixr:33 " -∗ " => hwand
@[inherit_doc qwand] scoped infixr:33 " -∗∗ " => qwand
@[inherit_doc hforall] scoped notation "∀ˢ " x ", " J => hforall (fun x => J)

end SepLogic

theorem hforall_intro {ι : Sort _} {H : SLProp} {J : ι → SLProp}
    (h : ∀ x, H ⊢ J x) : H ⊢ hforall J :=
  fun heap hH x => h x heap hH

theorem hforall_specialize {ι : Sort _} {J : ι → SLProp} (x : ι) :
    hforall J ⊢ J x :=
  fun _ hJ => hJ x

/-- SLF's `hwand_equiv`: the wand is the right adjoint of the separating
conjunction.  Every other property of the wand follows from it. -/
theorem hwand_equiv (H₀ H₁ H₂ : SLProp) :
    (H₀ ⊢ H₁ -∗ H₂) ↔ (H₁ ∗ H₀ ⊢ H₂) := by
  constructor
  · intro h heap hStar
    obtain ⟨h₁, h₀, hDisjoint, hEq, hH₁, hH₀⟩ := hStar
    obtain ⟨H, hH⟩ := h h₀ hH₀
    obtain ⟨hA, hB, hDisjoint', hEq', hHA, hPure⟩ := hH
    have hB' : hB = empty := hPure.2
    subst hB'
    simp only [empty, Finmap.union_empty] at hEq'
    subst hEq'
    exact hPure.1 heap ⟨h₁, h₀, hDisjoint, hEq, hH₁, hHA⟩
  · intro h heap hH₀
    exact ⟨H₀, heap, ∅, (Finmap.disjoint_empty heap).symm, by simp, hH₀, h, rfl⟩

/-- SLF's `himpl_hwand_r`, the introduction rule of the wand. -/
theorem hwand_intro {H₀ H₁ H₂ : SLProp} (h : H₁ ∗ H₀ ⊢ H₂) : H₀ ⊢ H₁ -∗ H₂ :=
  (hwand_equiv H₀ H₁ H₂).mpr h

/-- SLF's `hwand_cancel`, the elimination rule of the wand. -/
theorem hwand_cancel (H₁ H₂ : SLProp) : H₁ ∗ (H₁ -∗ H₂) ⊢ H₂ :=
  (hwand_equiv (H₁ -∗ H₂) H₁ H₂).mp (himpl_refl _)

theorem hwand_mono {H₁ H₁' H₂ H₂' : SLProp} (h₁ : H₁' ⊢ H₁) (h₂ : H₂ ⊢ H₂') :
    (H₁ -∗ H₂) ⊢ (H₁' -∗ H₂') :=
  hwand_intro (himpl_trans (hstar_mono h₁ (himpl_refl _))
    (himpl_trans (hwand_cancel H₁ H₂) h₂))

/-- SLF's `qwand_equiv`. -/
theorem qwand_equiv {α : Type} (H : SLProp) (Q₁ Q₂ : SLPost α) :
    (H ⊢ Q₁ -∗∗ Q₂) ↔ (Q₁ ∗+ H ⊢+ Q₂) := by
  constructor
  · intro h value
    exact himpl_trans (hstar_mono (himpl_refl _)
      (himpl_trans h (hforall_specialize value)))
      (hwand_cancel (Q₁ value) (Q₂ value))
  · intro h
    exact hforall_intro fun value =>
      hwand_intro (h value)

/-- SLF's `qwand_intro`. -/
theorem qwand_intro {α : Type} {H : SLProp} {Q₁ Q₂ : SLPost α}
    (h : Q₁ ∗+ H ⊢+ Q₂) : H ⊢ Q₁ -∗∗ Q₂ :=
  (qwand_equiv H Q₁ Q₂).mpr h

/-- SLF's `qwand_cancel`. -/
theorem qwand_cancel {α : Type} (Q₁ Q₂ : SLPost α) :
    Q₁ ∗+ (Q₁ -∗∗ Q₂) ⊢+ Q₂ :=
  (qwand_equiv (Q₁ -∗∗ Q₂) Q₁ Q₂).mp (himpl_refl _)

/-- SLF's `qwand_specialize`: a postcondition wand yields a heap wand at every
value. -/
theorem qwand_specialize {α : Type} {Q₁ Q₂ : SLPost α} (value : α) :
    (Q₁ -∗∗ Q₂) ⊢ (Q₁ value -∗ Q₂ value) :=
  hforall_specialize value

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

/-- Embed a precondition/postcondition pair into a weakest-precondition
transformer. -/
def pp2wp (P : SLPre) (Q : SLPost α) : Wp α where
  run := fun R h =>
    P h ∧ ∀ value h', Q value h' → R value h'
  monotone := by
    intro R₁ R₂ hR h hPre
    exact ⟨hPre.1, fun value h' hPost =>
      hR value h' (hPre.2 value h' hPost)⟩

end Aeneas.SLPoC
