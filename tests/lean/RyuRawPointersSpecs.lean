import RyuRawPointers

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace ryu_raw_pointers

/-! The digits are written to a buffer which may be uninitialized: the specifications of the
functions writing through `result` are stated on cells (`↦*?`). -/

/-- Negative exponent: writes `'-'` then the digit `c = '0' - k`. -/
theorem write_exponent.spec_neg (k : Isize) (result : MutRawPtr U8) (cs : List (Option U8)) (c : U8)
    (hk : -10 < k.val) (hneg : k.val < 0) (hc : c.val = 48 + (-k.val).toNat)
    (hlen : 2 ≤ cs.length) :
    ⦃ result ↦*? cs ⦄ write_exponent k result
      ⦃ n => ⌜n = 2#usize⌝ ∗ result ↦*? ((cs.set 0 (some 45#u8)).set 1 (some c)) ⦄ := by
  unfold write_exponent
  rw [if_pos (by scalar_tac)]
  have h0 := MutRawPtr.write.spec_cells result cs 0 45#u8 (by omega) (by simp)
  simp only [RawPtr.shift_zero] at h0
  step with h0
  step with RawPtr.add.spec_cells result (cs.set 0 (some 45#u8)) 1#usize (by simp; omega)
  step* 1
  subst_vars
  step* 1
  have hi : i.val = (-k.val).toNat := by
    rw [i_post, IScalar.hcast_val_eq, x_post, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  step* 1
  have : i1 = c := by scalar_tac
  subst this
  have h1 := MutRawPtr.write.spec_cells result (cs.set 0 (some 45#u8)) 1 i1 (by simp; omega)
    (by simp)
  step with h1
  step*

/-- Nonnegative exponent: writes the digit `c = '0' + k`. -/
theorem write_exponent.spec_nonneg (k : Isize) (result : MutRawPtr U8) (cs : List (Option U8))
    (c : U8) (hk0 : 0 ≤ k.val) (hk : k.val < 10) (hc : c.val = 48 + k.val.toNat)
    (hlen : 1 ≤ cs.length) :
    ⦃ result ↦*? cs ⦄ write_exponent k result
      ⦃ n => ⌜n = 1#usize⌝ ∗ result ↦*? cs.set 0 (some c) ⦄ := by
  unfold write_exponent
  rw [if_neg (by scalar_tac)]
  step* 2
  have hi : i.val = k.val.toNat := by
    rw [i_post, IScalar.hcast_val_eq, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  have : i1 = c := by scalar_tac
  subst this
  have h0 := MutRawPtr.write.spec_cells result cs 0 i1 (by omega) (by simp)
  simp only [RawPtr.shift_zero] at h0
  step with h0
  step*

theorem add_shift.spec {T : Type} [Pointee T] [Pointee.Lawful T] {M} (q : RawPtr T M) (vs : List T) (i : Nat) (c : Usize)
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
theorem write_exponent.spec (k : Isize) (result : MutRawPtr U8) (cs : List (Option U8)) (c : U8)
    (hk : -10 < k.val ∧ k.val < 10) (hc : c.val = 48 + k.val.natAbs) (hlen : 2 ≤ cs.length) :
    ⦃ result ↦*? cs ⦄ write_exponent k result
      ⦃ n => ⌜n.val = (expBytes k c).length⌝ ∗
        result ↦*? ((expBytes k c).map some ++ cs.drop (expBytes k c).length) ⦄ := by
  obtain _ | ⟨a, _ | ⟨b, rest⟩⟩ := cs
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

/-- `mul_shift_all` initializes the cells `vp` and `vm` point to. -/
@[step]
theorem mul_shift_all.spec (m : U64) (vp vm : MutRawPtr U64) (mm_shift : U32) (cp cm : Option U64)
    (hm : 4 * m.val + 2 ≤ U64.max) (hshift : 1 + mm_shift.val ≤ 4 * m.val) (hvp : vp.Aligned)
    (hvm : vm.Aligned) :
    ⦃ vp ↦? cp ∗ vm ↦? cm ⦄ mul_shift_all m vp vm mm_shift
      ⦃ r => ⌜r.val = 4 * m.val⌝ ∗ (∃ a, ⌜a.val = 4 * m.val + 2⌝ ∗ vp ↦ a) ∗
        (∃ b, ⌜b.val = 4 * m.val - 1 - mm_shift.val⌝ ∗ vm ↦ b) ⦄ := by
  unfold mul_shift_all
  step* 2
  step with MutRawPtr.write.spec_opt vp cp i1 hvp
  step* 3
  step with MutRawPtr.write.spec_opt vm cm i4 hvm
  step*

/-- The outputs of `mul_shift_all` are initialized: `assume_init` succeeds. -/
theorem d2d_bounds.spec (m : U64) (mm_shift : U32)
    (hm : 4 * m.val + 2 ≤ U64.max) (hshift : 1 + mm_shift.val ≤ 4 * m.val) :
    ⦃ emp ⦄ d2d_bounds m mm_shift
      ⦃ r => ⌜r.1.val = 4 * m.val ∧ r.2.1.val = 4 * m.val + 2 ∧
        r.2.2.val = 4 * m.val - 1 - mm_shift.val⌝ ⦄ := by
  unfold d2d_bounds
  step*
  subst_vars
  step with core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr.spec _ (some a)
  simp only [MaybeUninit.ofOption_some] at *
  subst_vars
  step
  step with core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr.spec _ (some b)
  simp only [MaybeUninit.ofOption_some] at *
  subst_vars
  step*

@[step]
theorem Buffer.new.spec :
    ⦃ emp ⦄ Buffer.new ⦃ b => ⌜b.bytes.val = List.replicate 24 .uninit⌝ ⦄ := by
  unfold Buffer.new
  step*
  subst_vars
  simp

/-- `format_exponent` returns the exponent bytes; its back computation (ending the borrow of
`self`) gives back the buffer with these bytes written (initialized) at its start. -/
theorem Buffer.format_exponent.spec (self : Buffer) (k : Isize) (c : U8)
    (hk : -10 < k.val ∧ k.val < 10) (hc : c.val = 48 + k.val.natAbs) :
    ⦃ emp ⦄ Buffer.format_exponent self k
      ⦃ (s, back) => ⌜s.val = expBytes k c⌝ ∗ iprop(∃ R, R ∗
        ⌜⦃ R ⦄ back ⦃ b => ⌜b.bytes.val =
          (expBytes k c).map MaybeUninit.init ++ self.bytes.val.drop (expBytes k c).length⌝ ⦄⌝) ⦄ := by
  unfold Buffer.format_exponent
  step* 2
  have hs : s.val.length = 24 := by simp [s_post]
  have hE : (expBytes k c).length ≤ 2 := by unfold expBytes; split <;> simp
  rw [MaybeUninit.pointsToRange_eq]
  step with write_exponent.spec k (p.cast U8) (s.val.map MaybeUninit.toOption) c hk hc
    (by simp; omega)
  have hcells : (expBytes k c).map some ++
      (s.val.map MaybeUninit.toOption).drop (expBytes k c).length =
      ((expBytes k c).map MaybeUninit.init ++ s.val.drop (expBytes k c).length).map MaybeUninit.toOption := by
    simp [List.map_drop, Function.comp_def]
  rw [hcells, ← MaybeUninit.pointsToRange_eq]
  subst as_mut_ptr_back_post
  step with Slice.end_as_mut_ptr.spec s p
    ((expBytes k c).map MaybeUninit.init ++ s.val.drop (expBytes k c).length) (by simp; omega)
  step* 2
  have hfs : (self.bytes.from_slice s1).val = s1.val :=
    Std.Array.from_slice_val _ _ (by simp [s1_post]; omega)
  subst to_slice_mut_back_post
  have hs2 : s2.val = (expBytes k c).map MaybeUninit.init ++ self.bytes.val.drop (expBytes k c).length := by
    simp [s2_post, Std.Array.to_slice, hfs, s1_post, s_post]
  rw [hs2, MaybeUninit.pointsToRange_init]
  have hn : 0 < n.val * Pointee.size U8 := by
    rw [n_post]; simp only [expBytes]; split <;> simp
  step with core.slice.raw.from_raw_parts.spec (p2.cast U8) n (expBytes k c) n_post
    (hNotNull := RawPtr.notNull_of_pos hn)
  apply (WP.ispec_ok _).2
  rw [s3_post]
  apply entails_exists_r (iprop((p2.cast U8) ↦† (expBytes k c).length ∗
    ((p2.cast U8).shift (expBytes k c).length) ↦*?
      (self.bytes.val.drop (expBytes k c).length).map MaybeUninit.toOption ∗
    p2.freeable s2.length .view))
  refine entails_trans (pure_sep_intro _ s3_post) (sep_mono (entails_refl _)
    (entails_trans (pure_sep_intro _ ?_) (entails_of_eq (sep_comm_eq _ _))))
  subst from_raw_parts_back_post as_ptr_back_post
  apply WP.ispec_bind (RawPtr.endBorrowRange.spec_len _ s3.val (expBytes k c).length
    (by simp [s3_post]))
  · iframe
  · intro _
    apply WP.ispec_bind (Slice.end_as_ptr.spec s2 p2)
    · rw [hs2, MaybeUninit.pointsToRange_init, s3_post]
      iframe
    · intro _
      apply (WP.ispec_ok _).2
      exact fun _ _ => by simp [hfs, s1_post, s_post]

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
