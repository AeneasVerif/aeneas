import RawPointerOffsets

open Aeneas
open Aeneas.SepLogic
open Aeneas.Std
open Aeneas.Std.WP
open raw_pointer_offsets

namespace SepLogic.ExtractedOffsets

theorem write3.spec (p : MutRawPtr U8) (a b c : U8) (rest : List U8) :
    ⦃ p ↦* (a :: b :: c :: rest) ⦄ write3 p
      ⦃⇓ q => ⌜q = p.add 3⌝ ∗ p ↦* (1#u8 :: 2#u8 :: 3#u8 :: rest)⦄ := by
  unfold write3
  have h0 := MutRawPtr.write.spec_range p (a :: b :: c :: rest) 0 1#u8 (by simp)
  simp only [RawPtr.add_zero] at h0
  step with h0
  step as ⟨p1, hp1⟩
  subst hp1
  simp only [RawPtr.add_add, RawPtr.pointsToRange_cons]
  step*

theorem written_len.spec (buf : Array U8 8#usize) :
    ⦃ emp ⦄ written_len buf
      ⦃⇓ r => ⌜r.1.val = 3 ∧ r.2.val = 1#u8 :: 2#u8 :: 3#u8 :: buf.val.drop 3⌝⦄ := by
  obtain ⟨b0, b1, b2, rest, hBuf⟩ : ∃ b0 b1 b2 rest, buf.val = b0 :: b1 :: b2 :: rest := by
    have h := buf.property
    match hv : buf.val, h with
    | b0 :: b1 :: b2 :: rest, _ => exact ⟨b0, b1, b2, rest, rfl⟩
  have hLen : rest.length = 5 := by
    have := buf.property
    simp [hBuf] at this
    omega
  unfold written_len
  step as ⟨s, back, hs, hBack⟩
  step as ⟨p⟩
  simp only [hs, hBuf]
  step with write3.spec p b0 b1 b2 rest
  step with Slice.sync_as_mut_ptr.spec s p (1#u8 :: 2#u8 :: 3#u8 :: rest)
    (by simp [hs, hBuf])
  step as ⟨s2, hs2⟩
  step with Slice.as_ptr_reuse.spec p s2 (1#u8 :: 2#u8 :: 3#u8 :: rest)
    (by simp [Array.from_slice, *])
  step with RawPtr.offsetFrom.spec «end» p1 3 (by simp [*]) (by simp) (by simp [*])
    (by simp [IScalar.inBounds]; cases System.Platform.numBits_eq <;> simp [*])
  subst p1_post hs2
  simp only [lift]
  step with Slice.free_as_ptr.spec
  apply (ispec_ok _).2
  apply (entails_emp_ipure_iff _).mpr
  constructor
  · simp only [IScalar.hcast_val_eq, i_post]
    cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *]
  · simp [hBack, Array.from_slice, s1_post, hLen]

end SepLogic.ExtractedOffsets
