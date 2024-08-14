import Base
open Primitives
open Result

namespace Tutorial

mutual

divergent def even (n : U32) : Result Bool :=
  if n = 0#u32 then ok true
  else do
    let n ← n - 1#u32
    odd n

divergent def odd (n : U32) : Result Bool :=
  if n = 0#u32 then ok false
  else do
    let n ← n - 1#u32
    even n

end

mutual

-- TODO: progress automatically decomposes the post-condition
theorem even_spec (n : U32) :
  ∃ b, even n = ok b ∧ (b ↔ Even n.val) := by
  rw [even]
  split
  . simp [*]
  . progress as ⟨ n' .. ⟩
    progress as ⟨ b .. ⟩
    simp [*]
    simp [Int.even_sub]
termination_by n.val.toNat
decreasing_by simp_wf; scalar_tac

theorem odd_spec (n : U32) :
  ∃ b, odd n = ok b ∧ (b ↔ Odd n.val) := by
  rw [odd]
  split
  . simp [*]
  . progress as ⟨ n' .. ⟩
    progress as ⟨ b .. ⟩
    simp [*]
    simp [Int.even_sub]
termination_by n.val.toNat
decreasing_by simp_wf; scalar_tac

end


end Tutorial
