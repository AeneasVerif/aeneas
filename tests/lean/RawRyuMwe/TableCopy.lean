module

public import RawRyuMwe.Copy

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe

namespace raw_ryu_mwe

def pairs : List U8 := [48#u8, 48#u8, 49#u8, 55#u8]

def pair_offset (pair : Usize) : Result Usize := do
  massert (pair < 2#usize)
  2#usize * pair

@[step]
theorem pair_offset.spec (pair : Usize) (bound : pair.val < 2) :
    pair_offset pair ⦃ (offset : Usize) => offset.val = 2 * pair.val ⦄ := by
  unfold pair_offset
  step*

def copy_table (pair : Usize) (sourceAddress destinationAddress : BasePtr) :
    Result (List Aeneas.Std.Byte) := do
  let offset ← pair_offset pair
  copy_scoped pairs (List.replicate 2 (.data 0#u8))
    sourceAddress destinationAddress offset 0#usize 2

/-- **Spec theorem for `raw_ryu_mwe::copy_table`**
    Includes the assertion, checked index multiplication, both materializations,
    exact two-byte copy, snapshot and both returns. -/
theorem copy_table.spec (pair : Usize) (sourceAddress destinationAddress : BasePtr)
    (bound : pair.val < 2)
    (apart : sourceAddress.val + 4 ≤ destinationAddress.val ∨
      destinationAddress.val + 2 ≤ sourceAddress.val)
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (copy_table pair sourceAddress destinationAddress)
      (fun result s₁ => result = ((pairs.drop (2 * pair.val)).take 2).map Byte.data ∧
        s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  unfold copy_table
  apply HeapWP.Spec.bind (HeapWP.Spec.of_spec (pair_offset.spec pair bound) s₀)
  rintro offset s₁ ⟨offsetVal, stateEq⟩
  subst s₁
  have run := copy_scoped.spec pairs (List.replicate 2 (.data 0#u8))
    sourceAddress destinationAddress offset 0#usize 2 (by decide)
    (by simp [pairs]; agrind) (by simp) (by simp; scalar_tac) F s₀ hm hi
  simpa [copiedBytes, offsetVal] using run

end raw_ryu_mwe
