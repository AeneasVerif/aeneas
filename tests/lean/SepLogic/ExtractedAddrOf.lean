import RawPointerAddrOf

open Aeneas
open Aeneas.SepLogic
open Aeneas.Std
open Aeneas.Std.WP
open raw_pointer_addr_of

namespace SepLogic.ExtractedAddrOf

theorem ispec_pre {α : Type} {P P' : IProp} {m : Result α} {Q : α → IProp}
    (hEnt : P ⊢ P') (h : ispec P' m Q) : ispec P m Q :=
  entails_trans hEnt h

theorem local_through_raw.spec :
    ⦃ emp ⦄ local_through_raw ⦃⇓ r => ⌜r = 2#u32⌝⦄ := by
  unfold local_through_raw
  step*

theorem incr_through_raw.spec (x : U32) (h : x.val + 1 ≤ U32.max) :
    ⦃ emp ⦄ incr_through_raw x ⦃⇓ r => ⌜r.val = x.val + 1⌝⦄ := by
  unfold incr_through_raw
  step*

theorem field_through_raw.spec (x : U32 × U16) :
    ⦃ emp ⦄ field_through_raw x ⦃⇓ r => ⌜r = (x.2, x)⌝⦄ := by
  obtain ⟨a, b⟩ := x
  unfold field_through_raw
  step*

theorem write_bytes_of.spec (v : U64) (buffer : MutRawPtr U8) (old : List U8)
    (hOld : old.length = 5) :
    ⦃ buffer ↦* old ⦄ write_bytes_of v buffer
      ⦃⇓ buffer ↦* ((ByteRepr.encode v).map (UScalar.mk (ty := .U8))).take 5⦄ := by
  unfold write_bytes_of
  step as ⟨p⟩
  apply ispec_pre (sep_mono (RawPtr.pointsTo_aligned p v) (entails_refl _))
  rw [sep_assoc_eq]
  apply WP.ispec_ipure.mpr
  intro hAl
  have hBytes : [v].flatMap ByteRepr.encode =
      ((ByteRepr.encode v).map (UScalar.mk (ty := .U8))).flatMap ByteRepr.encode := by
    rw [UScalar.flatMap_encode_u8]; simp
  have hLen : ((ByteRepr.encode v).map (UScalar.mk (ty := .U8))).length = 8 := by
    simp
  rw [RawPtr.pointsTo_eq_range]
  simp only [core.ptr.const_ptr.RawPtrConstT.cast]
  step with RawPtr.cast_scalar.spec_range p [v] ((ByteRepr.encode v).map (UScalar.mk (ty := .U8)))
    hBytes (by intro _ _; simp [RawPtr.Aligned])
  generalize hbytes : (ByteRepr.encode v).map (UScalar.mk (ty := .U8)) = bytes at *
  have hSplit : p1 ↦* bytes ⊢
      p1 ↦* bytes.take 5 ∗ (p1.add (bytes.take 5).length) ↦* bytes.drop 5 := by
    conv => lhs; rw [← List.take_append_drop 5 bytes]
    exact (RawPtr.pointsToRange_append _ _ _).1
  apply ispec_pre (sep_mono hSplit (entails_refl _))
  step with core.ptr.copy_nonoverlapping.spec p1 buffer 5#usize (bytes.take 5) old
    (by simp [hLen]) (by simp [hOld])
  subst p1_post
  have hBack : (RawPtr.retype p : RawPtr U8 .Const) ↦* bytes.take 5 ∗
      (RawPtr.retype p : RawPtr U8 .Const).add (bytes.take 5).length ↦* bytes.drop 5 ⊢
      p ↦ v := by
    refine entails_trans (RawPtr.pointsToRange_append _ _ _).2 ?_
    rw [List.take_append_drop, RawPtr.pointsTo_eq_range]
    have := RawPtr.pointsToRange_retype (M' := .Const) (RawPtr.retype p : RawPtr U8 .Const)
      bytes [v] hBytes.symm (by intro _; simpa using hAl)
    simpa using this
  apply ispec_pre (sep_mono (entails_refl _) hBack)
  step*

end SepLogic.ExtractedAddrOf
