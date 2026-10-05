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

end SepLogic.ExtractedCasts
