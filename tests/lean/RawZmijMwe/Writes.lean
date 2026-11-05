module

public import RawRyuMwe.ByteOps

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace raw_zmij_mwe

/- Handwritten models of the raw bodies. The caller's byte array is already
   resident in the heap; these are not emitted safe-wrapper translations. -/
def write_digits (buffer : RawPtr U8) (digits : U64) : Result Unit :=
  write_at u64Repr buffer 1#usize digits

/-- **Spec theorem for `raw_zmij_mwe::write_digits`**
    Write all eight little-endian lanes at offset one, preserving both neighbors. -/
@[step]
theorem write_digits.spec (buffer : RawPtr U8) (base : BasePtr)
    (old : Vector Aeneas.Std.Byte 10) (digits : U64) :
    ⦃ bytesAt buffer base old.toList ⦄ write_digits buffer digits
    ⦃ _ => bytesAt buffer base
      (old.toList.take 1 ++ (bytes64 digits).toList.map Byte.data ++ old.toList.drop 9) ⦄ := by
  exact write_at.spec u64Repr bytes64 (fun _ _ => Iff.rfl) buffer base old.toList
    1#usize digits (by simp [u64Repr, codec]) (by decide) (u64_noPointers digits)

def write_exponent (buffer : RawPtr U8) (digits sign : U16) (overlap : Bool) : Result Unit := do
  write_at u16Repr buffer (if overlap then 1#usize else 2#usize) digits
  RawPtr.write_unaligned u16Repr (buffer.cast U16) sign

def exponentBytes (old : List Aeneas.Std.Byte) (digits sign : U16) (overlap : Bool) :
    List Aeneas.Std.Byte :=
  let offset := if overlap then 1 else 2
  (bytes16 sign).toList.map Byte.data ++
    (old.take offset ++ (bytes16 digits).toList.map Byte.data ++ old.drop (offset + 2)).drop 2

/-- **Spec theorem for `raw_zmij_mwe::write_exponent`**
    The second store wins on overlap; all bytes outside the two windows survive. -/
@[step]
theorem write_exponent.spec (buffer : RawPtr U8) (base : BasePtr)
    (old : Vector Aeneas.Std.Byte 5) (digits sign : U16) (overlap : Bool) :
    ⦃ bytesAt buffer base old.toList ⦄ write_exponent buffer digits sign overlap
    ⦃ _ => bytesAt buffer base (exponentBytes old.toList digits sign overlap) ⦄ := by
  let offset : Usize := if overlap then 1#usize else 2#usize
  have offsetBound : offset.val + u16Repr.size ≤ old.toList.length := by
    cases overlap
    · simp [offset, u16Repr, codec]
    · simp [offset, u16Repr, codec]
  let afterDigits := old.toList.take offset.val ++
    (bytes16 digits).toList.map Byte.data ++ old.toList.drop (offset.val + 2)
  have size : afterDigits.length = 5 := by
    simp only [afterDigits, List.length_append, List.length_take, List.length_map,
      Vector.length_toList, List.length_drop]
    have : offset.val + 2 ≤ 5 := by simpa [u16Repr, codec] using offsetBound
    agrind
  unfold write_exponent
  apply HeapWP.Triple.bind (write_at.spec u16Repr bytes16 (fun _ _ => Iff.rfl)
    buffer base old.toList offset digits offsetBound (by decide) (u16_noPointers digits))
  intro _
  have last := write_window.spec u16Repr bytes16 (fun _ _ => Iff.rfl)
    buffer buffer base afterDigits 0 sign (by simp [size, u16Repr, codec]) (by decide)
    (u16_noPointers sign) rfl (by simp)
  cases overlap
  · simpa [afterDigits, offset, exponentBytes, u16Repr, codec] using last
  · simpa [afterDigits, offset, exponentBytes, u16Repr, codec] using last

end raw_zmij_mwe
