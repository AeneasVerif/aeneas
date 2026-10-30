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
    first_or v d ⦃ x => x = if v.length = 0 then d else v.val[0]! ⦄ := by
  unfold first_or
  step*
  grind

end vec_methods
