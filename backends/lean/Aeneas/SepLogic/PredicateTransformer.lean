import Aeneas.Data.OrderedMonad
import Aeneas.SepLogic.Basic

/-!
# Predicate transformers over separation-logic assertions

`Wp α` is the type of *monotone* predicate transformers from an `IPost α` to an
`IPre`, corresponding to `Wᴾᵘʳᵉ` in "Dijkstra Monads for All".  It is the
specification monad the event rules of the state monad are stated in.

The assertions themselves are in `Aeneas.SepLogic.Basic`.
-/

namespace Aeneas.SepLogic

open Aeneas.Std (Heap)

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

def Wp.exists {ι : Sort _} (f : ι → Wp α) : Wp α where
  wp := fun R => iexists (fun x => f x R)
  monotone := by
    rintro R₁ R₂ hR h ⟨x, hx⟩
    exact ⟨x, (f x).monotone hR h hx⟩

theorem Wp.exists_frame {ι : Sort _} {f : ι → Wp α} {Q : IPost α}
    (H : IProp) (hFrame : ∀ x, f x Q ∗ H ⊢ f x (Q ∗+ H)) :
    Wp.exists f Q ∗ H ⊢ Wp.exists f (Q ∗+ H) := by
  rintro h ⟨h₁, h₂, hDisjoint, rfl, ⟨x, hx⟩, hH⟩
  exact ⟨x, hFrame x _ ⟨h₁, h₂, hDisjoint, rfl, hx, hH⟩⟩

end Aeneas.SepLogic
