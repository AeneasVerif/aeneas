import RawPointerLayouts

open Aeneas
open Aeneas.SepLogic
open Aeneas.Std
open Aeneas.Std.WP
open raw_pointer_layouts

namespace SepLogic.ExtractedLayouts

theorem ispec_pre {α : Type} {P P' : IProp} {m : Result α} {Q : α → IProp}
    (hEnt : P ⊢ P') (h : ispec P' m Q) : ispec P m Q :=
  entails_trans hEnt h

/-- The table is allocated at an address aligned to 2, so it can be read as
`u16`s: the `i`-th one is made of the bytes `2 * i` and `2 * i + 1`. -/
theorem digits2.spec (value : Usize) (h : value.val < 2) :
    ⦃ emp ⦄ digits2 value ⦃⇓ r => ⌜r = [0x3130#u16, 0x3230#u16][value.val]!⌝⦄ := by
  unfold digits2
  step as ⟨s, hs⟩
  step as ⟨p, hAlign⟩
  step as ⟨p1, hp1⟩
  have hBytes : (Array.to_slice DIGITS2).val.flatMap ByteRepr.encode =
      [0x3130#u16, 0x3230#u16].flatMap ByteRepr.encode := by
    simp [DIGITS2, BitVec.toLEBytes]
  -- View the bytes of the table as two `u16`s
  have hWords : p ↦* (Array.to_slice DIGITS2).val ⊢ p1 ↦* [0x3130#u16, 0x3230#u16] := by
    subst hp1
    apply RawPtr.pointsToRange_retype _ _ _ hBytes
    intro _
    exact RawPtr.aligned_of_alignedTo (by simpa using hAlign) (by decide)
  subst hp1 hs
  apply ispec_pre hWords
  step as ⟨p2, hp2⟩
  subst hp2
  step with RawPtr.read.spec_range (RawPtr.retype p : ConstRawPtr U16) [0x3130#u16, 0x3230#u16]
    value.val (by simpa using h) as ⟨r, hr⟩
  -- View the `u16`s as bytes again, to free the table
  have hBack : (RawPtr.retype p : ConstRawPtr U16) ↦* [0x3130#u16, 0x3230#u16] ⊢
      p ↦* (Array.to_slice DIGITS2).val := by
    have := RawPtr.pointsToRange_retype (M' := .Const) (RawPtr.retype p : ConstRawPtr U16)
      [0x3130#u16, 0x3230#u16] (Array.to_slice DIGITS2).val hBytes.symm
      (by intro _; simp [RawPtr.Aligned])
    simpa using this
  apply ispec_pre hBack
  step*
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h), hr]
  rfl

end SepLogic.ExtractedLayouts
