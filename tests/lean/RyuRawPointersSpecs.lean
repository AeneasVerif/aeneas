import RyuRawPointers

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace ryu_raw_pointers

/-- Negative exponent: writes `'-'` then the digit `c = '0' - k`. -/
theorem write_exponent.spec_neg (k : Isize) (result : MutRawPtr U8) (vs : List U8) (c : U8)
    (hk : -10 < k.val) (hneg : k.val < 0) (hc : c.val = 48 + (-k.val).toNat)
    (hlen : 2 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ write_exponent k result
      ⦃ n => ⌜n = 2#usize⌝ ∗ result ↦* ((vs.set 0 45#u8).set 1 c) ⦄ := by
  unfold write_exponent
  rw [if_pos (by scalar_tac)]
  step with MutRawPtr.write.spec_head result vs 45#u8 (by scalar_tac)
  step* 2
  subst_vars
  step* 1
  have hi : i.val = (-k.val).toNat := by
    rw [i_post, IScalar.hcast_val_eq, x_post, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  step* 1
  have : i1 = c := by scalar_tac
  subst this
  step with MutRawPtr.write.spec_range result (vs.set 0 45#u8) 1 i1 (by simp; scalar_tac)
  step*

/-- Nonnegative exponent: writes the digit `c = '0' + k`. -/
theorem write_exponent.spec_nonneg (k : Isize) (result : MutRawPtr U8) (vs : List U8) (c : U8)
    (hk0 : 0 ≤ k.val) (hk : k.val < 10) (hc : c.val = 48 + k.val.toNat)
    (hlen : 1 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ write_exponent k result
      ⦃ n => ⌜n = 1#usize⌝ ∗ result ↦* vs.set 0 c ⦄ := by
  unfold write_exponent
  rw [if_neg (by scalar_tac)]
  step* 2
  have hi : i.val = k.val.toNat := by
    rw [i_post, IScalar.hcast_val_eq, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  have : i1 = c := by scalar_tac
  subst this
  step with MutRawPtr.write.spec_head result vs i1 (by scalar_tac)
  step*

theorem add_shift.spec {T : Type} {M} (q : RawPtr T M) (vs : List T) (i : Nat) (c : Usize)
    (h : i + c.val ≤ vs.length) :
    ⦃ q ↦* vs ⦄ (q.shift i).add c ⦃ r => ⌜r = q.shift (i + c.val)⌝ ∗ q ↦* vs ⦄ := by
  have hSplit := RawPtr.pointsToRange_split q vs i
  rw [show (vs.take i).length = i by simp; omega] at hSplit
  rw [hSplit]
  apply ispec_mono (RawPtr.add.spec (q.shift i) (vs.drop i) c (by simp; omega))
  · iframe
  · rw [RawPtr.shift_shift]; iframe

theorem DIGIT_TABLE_spec (j : Nat) (hj : j < 10) :
    (DIGIT_TABLE.to_slice.val)[j * 2]'(by simp; omega) = 48#u8 ∧
      ((DIGIT_TABLE.to_slice.val)[j * 2 + 1]'(by simp; omega)).val = 48 + j := by
  unfold DIGIT_TABLE
  rcases j with _|_|_|_|_|_|_|_|_|_|j <;> simp [Array.to_slice]
  omega

theorem write_two_digits.spec (k : Usize) (result : MutRawPtr U8) (vs : List U8) (c : U8)
    (hk : k.val < 10) (hc : c.val = 48 + k.val) (hlen : 2 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ write_two_digits k result ⦃ result ↦* ((vs.set 0 48#u8).set 1 c) ⦄ := by
  unfold write_two_digits
  step* 4
  subst_vars
  step with RawPtr.read.spec_range p DIGIT_TABLE.to_slice.val i.val (by simp; scalar_tac)
  step with MutRawPtr.write.spec_head result vs _ (by scalar_tac)
  step with add_shift.spec p DIGIT_TABLE.to_slice.val i.val 1#usize (by simp; scalar_tac)
  subst_vars
  step with RawPtr.read.spec_range p DIGIT_TABLE.to_slice.val (i.val + 1) (by simp; scalar_tac)
  step* 1
  subst_vars
  step with MutRawPtr.write.spec_range result (vs.set 0 _) 1 _ (by simp; scalar_tac)
  step*
  obtain ⟨h0, h1⟩ := DIGIT_TABLE_spec k.val hk
  apply entails_of_eq
  congr 1
  simp only [i_post]
  rw [h0]
  congr 1
  exact UScalar.eq_of_val_eq (by rw [h1, hc])

/-- The bytes `write_exponent k` writes, where `c` is the digit `'0' + |k|`. -/
def expBytes (k : Isize) (c : U8) : List U8 := if k.val < 0 then [45#u8, c] else [c]

@[step]
theorem write_exponent.spec (k : Isize) (result : MutRawPtr U8) (vs : List U8) (c : U8)
    (hk : -10 < k.val ∧ k.val < 10) (hc : c.val = 48 + k.val.natAbs) (hlen : 2 ≤ vs.length) :
    ⦃ result ↦* vs ⦄ write_exponent k result
      ⦃ n => ⌜n.val = (expBytes k c).length⌝ ∗
        result ↦* (expBytes k c ++ vs.drop (expBytes k c).length) ⦄ := by
  obtain _ | ⟨a, _ | ⟨b, rest⟩⟩ := vs
  · simp at hlen
  · simp at hlen
  by_cases hneg : k.val < 0
  · apply ispec_mono (write_exponent.spec_neg k result _ c (by omega) hneg (by omega) hlen)
    · iframe
    · simp [expBytes, hneg]; iframe
  · apply ispec_mono (write_exponent.spec_nonneg k result (a :: b :: rest) c (by omega) (by omega)
      (by omega) (by simp))
    · iframe
    · simp [expBytes, hneg]; iframe

@[step]
theorem Buffer.new.spec : ⦃ emp ⦄ Buffer.new ⦃ b => ⌜b.bytes.val = List.replicate 24 0#u8⌝ ⦄ := by
  unfold Buffer.new
  step*
  simp

/-- `format_exponent` returns the exponent bytes; its back computation (ending the borrow of
`self`) gives back the buffer with these bytes written at its start. -/
theorem Buffer.format_exponent.spec (self : Buffer) (k : Isize) (c : U8)
    (hk : -10 < k.val ∧ k.val < 10) (hc : c.val = 48 + k.val.natAbs) :
    ⦃ emp ⦄ Buffer.format_exponent self k
      ⦃ (s, back) => ⌜s.val = expBytes k c⌝ ∗ iprop(∃ R, R ∗
        ⌜⦃ R ⦄ back ⦃ b => ⌜b.bytes.val =
          expBytes k c ++ self.bytes.val.drop (expBytes k c).length⌝ ⦄⌝) ⦄ := by
  unfold Buffer.format_exponent
  step* 2
  subst_vars
  step with write_exponent.spec k p s.val c hk hc (by scalar_tac)
  simp only [s_post]
  have hE : (expBytes k c).length ≤ 2 := by unfold expBytes; split <;> simp
  have hLen : self.bytes.val.length = 24 := by simp
  step with Slice.end_as_mut_ptr.spec s p
    (expBytes k c ++ self.bytes.val.drop (expBytes k c).length) (by simp [s_post]; omega)
  step* 2
  step with core.slice.raw.from_raw_parts.spec_prefix p1 n s2.val (by simp [s2_post]; omega)
  have hs2 : s2.val.length = 24 := by simp [s2_post]
  have hfs : (self.bytes.from_slice s1).val = s1.val :=
    Std.Array.from_slice_val _ _ (by simp [s1_post]; omega)
  have hTake : (s2.val.take n.val).length = n.val := by simp; omega
  have hSplit := RawPtr.pointsToRange_split p1 s2.val n.val
  rw [hTake] at hSplit
  apply (WP.ispec_ok _).2
  apply entails_exists_r (iprop(p1 ↦† n.val ∗ RawPtr.shift p1 n.val ↦* s2.val.drop n.val ∗
    p1.freeable s2.length .view))
  refine entails_trans (pure_sep_intro _ ?hs3) (sep_mono (entails_refl _)
    (entails_trans (pure_sep_intro _ ?hT) (entails_of_eq (sep_comm_eq _ _))))
  case hs3 =>
    simp [s3_post, s2_post, Std.Array.to_slice, hfs, s1_post, n_post]
  case hT =>
    subst from_raw_parts_back_post as_ptr_back_post
    apply WP.ispec_bind (RawPtr.endBorrowRange.spec_len p1 s3.val n.val (by rw [s3_post]; exact hTake))
    · iframe
    · intro _
      apply WP.ispec_bind (Slice.end_as_ptr.spec s2 p1)
      · rw [hSplit, s3_post]; iframe
      · intro _
        apply (WP.ispec_ok _).2
        exact fun _ _ => by simp [hfs, s1_post]

/-- `c` is the digit `'0' + |k|`. -/
theorem first_char_of_exponent.spec (k : Isize) (c : U8)
    (hk : -10 < k.val ∧ k.val < 10) (hc : c.val = 48 + k.val.natAbs) :
    ⦃ emp ⦄ first_char_of_exponent k ⦃ r => ⌜r = if k.val < 0 then 45#u8 else c⌝ ⦄ := by
  unfold first_char_of_exponent
  step* 1
  step with Buffer.format_exponent.spec buf k c hk hc
  have hE : 0 < s.length := by rw [Slice.length, s_post, expBytes]; split <;> simp
  step* 1
  step with s_post1
  step*
  by_cases hneg : k.val < 0
  · have : s.val = [45#u8, c] := by simp [s_post, expBytes, hneg]
    simp [i_post, this, hneg]
  · have : s.val = [c] := by simp [s_post, expBytes, hneg]
    simp [i_post, this, hneg]

end ryu_raw_pointers
