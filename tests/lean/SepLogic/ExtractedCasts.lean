import RawPointerCasts

open Aeneas
open Aeneas.SepLogic
open Aeneas.Std
open Aeneas.Std.WP
open raw_pointer_casts

namespace SepLogic.ExtractedCasts

theorem bytes_of_words.spec (data : Slice U32) :
    ⦃ emp ⦄ bytes_of_words data
      ⦃⇓ p => p ↦* (data.val.flatMap ByteRepr.encode).map (UScalar.mk (ty := .U8))⦄ := by
  unfold bytes_of_words
  step as ⟨p⟩
  step with RawPtr.cast_scalar.spec_range p data.val _ (UScalar.flatMap_encode_u8 _).symm
    (by intro _ _; simp [RawPtr.Aligned])

theorem mut_bytes_of_words.spec (data : Slice U32) :
    ⦃ emp ⦄ mut_bytes_of_words data ⦃⇓ r => ⌜r.2 = data⌝⦄ := by
  unfold mut_bytes_of_words
  step*

theorem const_bytes_of_mut_words.spec (data : Slice U32) :
    ⦃ emp ⦄ const_bytes_of_mut_words data ⦃⇓ r => ⌜r.2 = data⌝⦄ := by
  unfold const_bytes_of_mut_words
  step*

theorem signed_of_unsigned.spec (data : Slice U16) :
    ⦃ emp ⦄ signed_of_unsigned data ⦃⇓ r => ⌜r.2 = data⌝⦄ := by
  unfold signed_of_unsigned
  step*

theorem words_of_bytes.spec (data : Slice U8) :
    ⦃ emp ⦄ words_of_bytes data ⦃⇓ q => (q.retype : ConstRawPtr U8) ↦* data.val⦄ := by
  unfold words_of_bytes
  step*

theorem write_read_unaligned.spec (buf : Array U8 3#usize) (v : U16) :
    ⦃ emp ⦄ write_read_unaligned buf v
      ⦃⇓ r => ⌜r.1 = v ∧
        r.2.val = buf.val[0]! :: (ByteRepr.encode v).map (UScalar.mk (ty := .U8))⌝⦄ := by
  obtain ⟨b0, b1, b2, hBuf⟩ : ∃ b0 b1 b2, buf.val = [b0, b1, b2] := by
    have h := buf.property
    match hv : buf.val, h with
    | [b0, b1, b2], _ => exact ⟨b0, b1, b2, rfl⟩
  unfold write_read_unaligned
  step as ⟨s, back, hs, hBack⟩
  step as ⟨p⟩
  step as ⟨p1, hp1⟩
  step as ⟨q, hq⟩
  subst hp1 hq
  step with MutRawPtr.writeUnaligned.spec ((p.add 1).retype : MutRawPtr U16) [b1, b2] v (by simp)
  simp only [RawPtr.bytesPtr_retype, RawPtr.pointsToRange_retype_eq]
  step with RawPtr.readUnaligned.spec ((p.add 1).retype : MutRawPtr U16) v
  simp only [RawPtr.bytesPtr_retype, RawPtr.pointsToRange_retype_eq]
  step with Slice.end_as_mut_ptr.spec s p (b0 :: (ByteRepr.encode v).map (UScalar.mk (ty := .U8)))
    (by simp [hs, hBuf])
  apply (ispec_ok _).2
  iintro
  subst hBack
  simp [i_post, s1_post, hBuf, Array.from_slice]

theorem zero_prefix.spec (buf : Array U8 4#usize) :
    ⦃ emp ⦄ zero_prefix buf
      ⦃⇓ r => ⌜r.val = [0#u8, 0#u8, buf.val[2]!, buf.val[3]!]⌝⦄ := by
  obtain ⟨b0, b1, b2, b3, hBuf⟩ : ∃ b0 b1 b2 b3, buf.val = [b0, b1, b2, b3] := by
    have h := buf.property
    match hv : buf.val, h with
    | [b0, b1, b2, b3], _ => exact ⟨b0, b1, b2, b3, rfl⟩
  unfold zero_prefix
  step as ⟨s, back, hs, hBack⟩
  step as ⟨p⟩
  simp only [hs, hBuf]
  step with RawPtr.writeBytes.spec p 0#u8 2#usize [b0, b1] (by simp)
  simp only [RawPtr.bytesPtr, RawPtr.retype_self]
  step with Slice.end_as_mut_ptr.spec s p [0#u8, 0#u8, b2, b3] (by simp [hs, hBuf])
  apply (ispec_ok _).2
  iintro
  subst hBack
  simp [s1_post, Array.from_slice]

end SepLogic.ExtractedCasts