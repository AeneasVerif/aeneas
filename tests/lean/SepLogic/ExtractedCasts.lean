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
    ⦃ emp ⦄ mut_bytes_of_words data
      ⦃⇓ r => ⌜r.2 = data⌝ ∗
        r.1 ↦* (data.val.flatMap ByteRepr.encode).map (UScalar.mk (ty := .U8))⦄ := by
  unfold mut_bytes_of_words
  step as ⟨p, data1, hData⟩
  step with RawPtr.cast_scalar.spec_range p data.val _ (UScalar.flatMap_encode_u8 _).symm
    (by intro _ _; simp [RawPtr.Aligned])
  step*

theorem const_bytes_of_mut_words.spec (data : Slice U32) :
    ⦃ emp ⦄ const_bytes_of_mut_words data
      ⦃⇓ r => ⌜r.2 = data⌝ ∗
        r.1 ↦* (data.val.flatMap ByteRepr.encode).map (UScalar.mk (ty := .U8))⦄ := by
  unfold const_bytes_of_mut_words
  step as ⟨p, data1, hData⟩
  step with RawPtr.cast_scalar.spec_range p data.val _ (UScalar.flatMap_encode_u8 _).symm
    (by intro _ _; simp [RawPtr.Aligned])
  step*

theorem signed_of_unsigned.spec (data : Slice U16) :
    ⦃ emp ⦄ signed_of_unsigned data
      ⦃⇓ r => ⌜r.2 = data⌝ ∗ r.1 ↦* data.val.map fun x => (⟨x.bv⟩ : I16)⦄ := by
  unfold signed_of_unsigned
  step as ⟨p, data1, hData⟩
  step with RawPtr.cast_scalar.spec_range (M' := .Mut) p data.val
    (data.val.map fun x => (⟨x.bv⟩ : I16))
    (by simp only [List.flatMap_map]; rfl)
    (by
      intro hAligned hNonEmpty
      have := hAligned (by simpa using hNonEmpty)
      exact RawPtr.aligned_retype_of_dvd (Nat.dvd_refl _) this)
  step*

end SepLogic.ExtractedCasts
