module

public import RawZmijMwe.Formatter

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace raw_zmij_mwe

/- Recover the statically sized buffer after the handwritten adapter's list
   return. The length check is proved redundant, not assumed by the caller. -/
def DecimalBuffer.restore (bytes : List Aeneas.Std.Byte) :
    Result (Vector Aeneas.Std.Byte 4) :=
  if h : bytes.length = 4 then .ok ⟨bytes.toArray, by simpa using h⟩
  else .fail .undef

def formattedBuffer (old : Vector Aeneas.Std.Byte 4) (value : U8) :
    Vector Aeneas.Std.Byte 4 :=
  ⟨(formattedBytes old value).toArray, by simp⟩

@[simp]
theorem DecimalBuffer.restore_formatted (old : Vector Aeneas.Std.Byte 4) (value : U8) :
    restore (formattedBytes old value) = .ok (formattedBuffer old value) := by
  simp [restore, formattedBuffer]

/- The first slice is a pure snapshot: a Rust caller must copy it before the
   second mutable borrow. This does not model two simultaneously live &strs. -/
def DecimalBuffer.format_twice (old : Vector Aeneas.Std.Byte 4) (first second : U8)
    (address : BasePtr) : Result (Slice U8 × Slice U8 × List Aeneas.Std.Byte) := do
  let (a, updated) ← format_and_return old first address
  let buffer ← restore updated
  let (b, updated) ← format_and_return buffer second address
  .ok (a, b, updated)

/-- Two complete formatter scopes preserve both snapshots and return the exact
    final buffer, including bytes left over from the first call. -/
@[step]
theorem DecimalBuffer.format_twice.spec (old : Vector Aeneas.Std.Byte 4)
    (first second : U8) (address : BasePtr) :
    ⦃ empty ⦄ format_twice old first second address
    ⦃ (a : Slice U8) (b : Slice U8) (updated : List Aeneas.Std.Byte) => fun h =>
      a.val = decimalDigits first ∧ b.val = decimalDigits second ∧
      updated = formattedBytes (formattedBuffer old first) second ∧ empty h ⦄ := by
  intro h F s₀ hp hd hm hi
  unfold format_twice
  apply HeapWP.Spec.bind (format_and_return.spec old first address h F s₀ hp hd hm hi)
  rintro ⟨a, updated⟩ s₁ ⟨h₁, hd₁, hm₁, hi₁, ha, rfl, hp₁⟩
  dsimp only [Aeneas.Std.uncurry]
  rw [restore_formatted, bind_ok]
  apply HeapWP.Spec.bind
    (format_and_return.spec (formattedBuffer old first) second address h₁ F s₁ hp₁ hd₁ hm₁ hi₁)
  rintro ⟨b, updated⟩ s₂ ⟨h₂, hd₂, hm₂, hi₂, hb, hu, hp₂⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨h₂, hd₂, hm₂, hi₂, ha, hb, hu, hp₂⟩

end raw_zmij_mwe
