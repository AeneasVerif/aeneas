/- Arrays/Slices -/
import Aeneas.Std.Scalar.Core
import Aeneas.Data.List.List

namespace Aeneas.Std

open Result WP

/-!
# Notations for `List`
-/
instance {α : Type u} : GetElem (List α) Usize α (fun l i => i.val < l.length) where
  getElem l i h := getElem l i.val h

instance {α : Type u} : GetElem? (List α) Usize α (fun l i => i < l.length) where
  getElem? l i := getElem? l i.val

/-
# Theorems
-/
def List.mapM_with_length {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) (as : List α)
  : m ({ l : List β // l.length = as.length}) :=
  match as with
  | [] => pure ⟨[], by trivial⟩
  | a :: as => do
    let ⟨l, len⟩ ← List.mapM_with_length f as
    let a' ← f a
    pure ⟨a' :: l, by grind⟩

theorem List.mapM_with_length_spec{post : Nat → β → Prop} {f : α → Result β} {l : List α}
  (h : ∀ i (hi : i < l.length), f l[i] ⦃ post i ⦄) :
  exists l', (List.mapM_with_length f l = .ok l')
    ∧ (l'.val.map ok = l.map f)
    := by
  induction l generalizing post with
  | nil => simp [mapM_with_length, pure]
  | cons a as ih =>
    have ih := ih (post := fun n => post n.succ)
    have : ∀ (i : ℕ) (hi : i < as.length), f as[i] ⦃ post i.succ ⦄ := by
      intros i hi
      apply h i.succ (by grind)
    obtain ⟨lih, propih⟩ := ih this
    have fa := h 0 (by grind)
    cases hfa : (f a) <;> simp_all
    rename_i r
    exists (r :: lih)
    constructor
    · constructor
      · simp [mapM_with_length]
        simp [*]
        simp [Functor.map]
      · grind
    · grind

def List.clone (clone : α → Result α) (l : List α) : Result ({ l' : List α // l'.length = l.length}) :=
  List.mapM_with_length clone l

@[step]
theorem List.clone_spec {clone : α → Result α} {l : List α} (h : ∀ x ∈ l, clone x = ok x) :
  List.clone clone l ⦃ l' => l'.val = l ∧ l'.val.length = l.length ⦄ := by
  simp only [List.clone]
  induction l with
  | nil => simp [mapM_with_length, pure]
  | cons a as ih =>
    simp [mapM_with_length, pure]
    have : ∀ x ∈ as, clone x = ok x := by grind
    have ih := ih this
    apply spec_bind ih; intros h2 h3
    simp [*]

end Aeneas.Std
