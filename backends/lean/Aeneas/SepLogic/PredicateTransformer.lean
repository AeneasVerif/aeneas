import Aeneas.Data.OrderedMonad
import Aeneas.SepLogic.Basic

/-!
# Predicate transformers over separation-logic assertions

`Wp α` is the type of *monotone* predicate transformers from an `IPost α` to an
`IPre`, corresponding to `Wᴾᵘʳᵉ` in "Dijkstra Monads for All".  It is the
specification monad the event rules of the state monad are stated in, and
`pp2wp` is the transformer a precondition/postcondition pair denotes.

The assertions themselves are in `Aeneas.SepLogic.Basic`.
-/

namespace Aeneas.SepLogic

open Aeneas.Std (Heap)

/-- Monotone predicate transformers, corresponding to `Wᴾᵘʳᵉ` in
"Dijkstra Monads for All". -/
structure Wp (α : Type) where
  wp : IPost α → IPre
  monotone :
    ∀ {Q₁ Q₂ : IPost α},
      (∀ value, Entails (Q₁ value) (Q₂ value)) →
      Entails (wp Q₁) (wp Q₂)

namespace Wp

instance : CoeFun (Wp α) (fun _ => IPost α → IPre) :=
  ⟨Wp.wp⟩

def pure (value : α) : Wp α :=
  ⟨fun Q => Q value, fun hQ => hQ value⟩

def bind (m : Wp α) (next : α → Wp β) : Wp β :=
  ⟨fun Q => m (fun value => next value Q), fun hQ =>
    m.monotone (fun value => (next value).monotone hQ)⟩

/-- Specification weakening is reverse implication between preconditions. -/
instance : LE (Wp α) where
  le w₁ w₂ := ∀ Q, Entails (w₂ Q) (w₁ Q)

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

instance : Aeneas.OrderedMonad Wp where
  bind_mono := Wp.bind_mono

/-- Embed a precondition/postcondition pair into a weakest-precondition
transformer.  The encoding is local: `P` is required to describe only part of
the heap, and the postcondition is handed to the continuation through a wand,
so that the frame is threaded automatically. -/
def pp2wp (P : IPre) (Q : IPost α) : Wp α where
  wp := fun R => P ∗ (Q -∗+ R)
  monotone := by
    intro R₁ R₂ hR
    exact sep_mono (entails_refl P)
      (postWand_intro fun value =>
        entails_trans (postWand_cancel Q R₁ value) (hR value))

def Wp.exists {ι : Sort _} (f : ι → Wp α) : Wp α where
  wp := fun R => iexists (fun x => f x R)
  monotone := by
    rintro R₁ R₂ hR h ⟨x, hx⟩
    exact ⟨x, (f x).monotone hR h hx⟩

theorem pp2wp_conseq {P : IPre} {Q R : IPost α} (hPost : Q ⊢+ R) :
    P ⊢ pp2wp P Q R :=
  entails_trans (entails_of_eq (sep_emp_r_eq P).symm)
    (sep_mono (entails_refl P)
      (postWand_intro fun value =>
        entails_trans (entails_of_eq (sep_emp_r_eq (Q value))) (hPost value)))

theorem pp2wp_frame {P : IPre} {Q R : IPost α} (H : IProp) :
    pp2wp P Q R ∗ H ⊢ pp2wp P Q (R ∗+ H) :=
  entails_trans (entails_of_eq (sep_assoc_eq P (Q -∗+ R) H))
    (sep_mono (entails_refl P)
      (postWand_intro fun value =>
        entails_trans (entails_of_eq (sep_assoc_eq (Q value) (Q -∗+ R) H).symm)
          (sep_mono (postWand_cancel Q R value) (entails_refl H))))

/-- The elimination principle of `pp2wp`: the heap splits into the footprint
described by `P` and a frame, and the continuation accepts any heap the
postcondition describes, put back next to that frame. -/
theorem pp2wp_elim {P : IPre} {Q R : IPost α} {h : Heap}
    (hWp : pp2wp P Q R h) :
    ∃ h₁ h₂,
      PartialCommMonoid.Compatible h₁ h₂ ∧
      h = h₁ ∪ h₂ ∧
      P h₁ ∧
      ∀ value h', Q value h' →
        PartialCommMonoid.Compatible h' h₂ →
        R value (h' ∪ h₂) := by
  obtain ⟨h₁, h₂, hDisjoint, hEq, hP, hWand⟩ := hWp
  exact ⟨h₁, h₂, hDisjoint, hEq, hP, fun value h' hQ hDisjoint' =>
    postWand_cancel Q R value (h' ∪ h₂) ⟨h', h₂, hDisjoint', rfl, hQ, hWand⟩⟩

theorem Wp.exists_frame {ι : Sort _} {f : ι → Wp α} {Q : IPost α}
    (H : IProp) (hFrame : ∀ x, f x Q ∗ H ⊢ f x (Q ∗+ H)) :
    Wp.exists f Q ∗ H ⊢ Wp.exists f (Q ∗+ H) := by
  rintro h ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hx⟩, hH⟩
  exact ⟨x, hFrame x _ ⟨h₁, h₂, hDisjoint, rfl, hx, hH⟩⟩

end Aeneas.SepLogic
