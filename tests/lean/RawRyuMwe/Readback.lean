module

public import RawRyuMwe.ByteOps
public import Aeneas.Std.Heap.RangeRestoration
import all Aeneas.Std.Slice

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace raw_ryu_mwe

def read_two (bytes : Slice U8) : Result (U8 × U8) := do
  let a ← Slice.index_usize bytes 0#usize
  let b ← Slice.index_usize bytes 1#usize
  pure (a, b)

theorem read_two.spec (bytes : Slice U8) (a b : U8) (contents : bytes.val = [a, b]) :
    read_two bytes ⦃ (x : U8) (y : U8) => x = a ∧ y = b ⦄ := by
  unfold read_two
  step with Slice.index_usize_spec bytes 0#usize (by simp [Slice.length, contents])
  step with Slice.index_usize_spec bytes 1#usize (by simp [Slice.length, contents])
  · simp [contents] at *
    agrind

def read_prefix (p : RawPtr U8) : Result (U8 × U8) := do
  let (bytes, back) ← core.slice.raw.from_raw_parts Repr.u8 p 2#usize
  let result ← read_two bytes
  back
  pure result

/-- Read exactly the initialized prefix through the actual shared slice
    conversion, and execute its matching return before exposing the result. -/
theorem read_prefix.spec (p : RawPtr U8) (base : BasePtr) (a b : U8) :
    ⦃ pointsToRange Repr.u8 p base #v[a, b] 0 ⦄ read_prefix p
    ⦃ (x : U8) (y : U8) => fun h =>
      x = a ∧ y = b ∧ pointsToRange Repr.u8 p base #v[a, b] 0 h ⦄ := by
  intro h F s₀ hp hd hm hi
  have forward : HeapWP.Spec (core.slice.raw.from_raw_parts Repr.u8 p 2#usize)
      (fun result s₁ => result.1.val = [a, b] ∧
        HeapWP.Spec result.2 (fun _ s₂ => s₂ = s₀) s₁) s₀ := by
    unfold core.slice.raw.from_raw_parts
    apply HeapWP.Spec.bind
      (HeapWP.shareRange_return.spec Repr.u8 p base #v[a, b] 0 (by decide) (by decide)
        h F s₀ hp hd hm hi)
    rintro values s₁ ⟨rfl, returning⟩
    have size : (#v[a, b]).toList.length ≤ Usize.max := by scalar_tac
    rw [dite_eq_left size]
    exact (HeapWP.Spec.pure _ _ _).mpr ⟨rfl, returning⟩
  unfold read_prefix
  apply HeapWP.Spec.bind forward
  rintro ⟨bytes, back⟩ s₁ ⟨contents, returning⟩
  dsimp only [Aeneas.Std.uncurry]
  apply HeapWP.Spec.bind (HeapWP.Spec.of_spec (read_two.spec bytes a b contents) s₁)
  rintro ⟨x, y⟩ s₂ ⟨⟨rfl, rfl⟩, rfl⟩
  apply HeapWP.Spec.bind returning
  rintro _ s₂ rfl
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨h, hd, hm, hi, rfl, rfl, hp⟩

end raw_ryu_mwe
