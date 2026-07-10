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
theorem List.mapM_clone_eq {T : Type u} {clone : T → Result T} {l : List T}
  (h : ∀ x ∈ l, clone x = ok x) :
  List.mapM clone l = ok l := by
  have hind (l acc : List T) (h : ∀ x ∈ l, clone x = ok x) :
    List.mapM.loop clone l acc = ok (List.reverse acc ++ l) := by
    revert acc
    induction l <;> intro acc <;> simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      List.append_nil, List.mem_cons, or_true, forall_const, forall_eq_or_imp] <;> unfold List.mapM.loop
    . simp only [pure]
    . rename_i hd tl ih
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
        bind_tc_ok, h, ih]
  apply hind
  apply h

def List.clone (clone : α → Result α) (l : List α) : Result ({ l' : List α // l'.length = l.length}) :=
  -- TODO: clean this up
  -- match h :List.mapM clone l with
  -- | ok v => ok ⟨ v, by have := List.mapM_Result_length h; scalar_tac ⟩
  -- | fail e => fail e
  -- | div => div
  -- (List.mapM clone l).match_dep
  Result.match_dep' (motive := fun l => _) (List.mapM clone l)
  (fun v h => ok ⟨ v, by have := List.mapM_Result_length h; scalar_tac ⟩)
  (fun e _h => fail e)
  (fun _h => div)

@[step]
def List.clone_spec {clone : α → Result α} {l : List α} (h : ∀ x ∈ l, clone x = ok x) :
  List.clone clone l ⦃ l' => l'.val = l ∧ l'.val.length = l.length ⦄ := by
  simp only [List.clone]
  have := List.mapM_clone_eq h
  simp [this]

end Aeneas.Std
