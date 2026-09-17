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

/- Stated as a `spec`, not as "it returns an `ok`": the recursion then composes
with `spec_bind`, and no separate returning hypothesis is needed. -/
theorem List.mapM_with_length_spec {post : Nat → β → Prop} {f : α → Result β} {l : List α}
  (h : ∀ i (hi : i < l.length), f l[i] ⦃ post i ⦄) :
  List.mapM_with_length f l ⦃ l' => ∀ i (hi : i < l'.val.length), post i l'.val[i] ⦄ := by
  induction l generalizing post with
  | nil => simp [mapM_with_length, pure]
  | cons a as ih =>
    simp only [mapM_with_length]
    apply spec_bind (ih (post := fun n => post n.succ) (by intro i hi; exact h i.succ (by grind)))
    intro l hl
    apply spec_bind (h 0 (by grind))
    intro a' ha'
    simp only [pure, spec_ok]
    intro i hi
    cases i with
    | zero => simpa using ha'
    | succ j => simpa using hl j (by simp at hi; grind)

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
