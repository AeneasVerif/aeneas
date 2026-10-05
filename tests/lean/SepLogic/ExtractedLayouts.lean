import RawPointerLayouts

open Aeneas
open Aeneas.SepLogic
open Aeneas.Std
open Aeneas.Std.WP
open raw_pointer_layouts

namespace SepLogic.ExtractedLayouts

/-- The table is allocated at an address aligned to 2, so it can be read as
`u16`s: the `i`-th one is made of the bytes `2 * i` and `2 * i + 1`. -/
theorem digits2.spec (value : Usize) (h : value.val < 2) :
    ⦃ emp ⦄ digits2 value
      ⦃⇓ r => ⌜r = [0x3130#u16, 0x3230#u16][value.val]!⌝ ∗
        iprop(∃ q : ConstRawPtr U16, q ↦* [0x3130#u16, 0x3230#u16])⦄ := by
  unfold digits2
  step as ⟨s, hs⟩
  step as ⟨p, hAlign⟩
  step as ⟨p1, hp1⟩
  -- View the bytes of the table as two `u16`s
  have hWords : p ↦* (Array.to_slice DIGITS2).val ⊢ p1 ↦* [0x3130#u16, 0x3230#u16] := by
    subst hp1
    apply RawPtr.pointsToRange_retype
    · simp [DIGITS2, BitVec.toLEBytes]
    · intro _
      exact RawPtr.aligned_of_alignedTo (by simpa using hAlign) (by decide)
  subst hp1
  apply WP.ispec_mono (Pm := (RawPtr.retype p : ConstRawPtr U16) ↦* [0x3130#u16, 0x3230#u16]) ?_
    (entails_trans hWords (entails_sep_postWand _ (fun _ => entails_refl _)))
  step as ⟨p2, hp2⟩
  subst hp2
  step with RawPtr.read.spec_range (RawPtr.retype p : ConstRawPtr U16) [0x3130#u16, 0x3230#u16]
    value.val (by simpa using h)
  subst r_post
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
  rfl

end SepLogic.ExtractedLayouts
