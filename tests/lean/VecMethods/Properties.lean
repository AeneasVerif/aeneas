module
public import Aeneas
public import VecMethods.VecMethods
public section

open Aeneas Aeneas.Std Result

/-! Proofs for `Vec::is_empty` examples. -/

namespace vec_methods

/-- A new vector is empty… -/
theorem new_is_empty_spec : new_is_empty ⦃ b => b = true ⦄ := by
  unfold new_is_empty
  step*

/-- …and is not empty after a `push`. -/
theorem pushed_is_empty_spec : pushed_is_empty ⦃ b => b = false ⦄ := by
  unfold pushed_is_empty
  step*

/-- `is_empty` guarding an index: its spec gives the bound needed to index the vector. -/
theorem first_or_spec (v : alloc.vec.Vec Std.U32) (d : Std.U32) :
    first_or v d ⦃ x => x = v.val.headD d ⦄ := by
  unfold first_or
  step*
  · simp_all
  · subst_vars
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_eq_getElem]
    rfl

end vec_methods
