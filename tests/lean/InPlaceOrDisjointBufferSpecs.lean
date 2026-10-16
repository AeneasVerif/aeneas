import InPlaceOrDisjointBuffer

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace in_place_or_disjoint_buffer

/-- `new_in_place` hands over the slots of `buffer`; its back function ends the `as_mut_ptr`
borrow, turning the slots back into the slice. -/
@[step]
theorem InPlaceOrDisjointBuffer.new_in_place.spec {T : Type} [Pointee T] [Pointee.Lawful T]
    (buffer : Slice T) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.new_in_place buffer
      ⦃ (b, back) => ⌜b.len = buffer.len ∧ b.src = b.dst.cast_const ∧
        (∀ b', back b' = Slice.end_as_mut_ptr buffer b.dst) ∧ b.dst.Aligned⌝ ∗ b.dst ↦* buffer.val ∗
        b.dst.freeable buffer.length .view ⦄ := by
  unfold InPlaceOrDisjointBuffer.new_in_place
  step*

/-- `new_disjoint` hands over the slots of `src` and `dst`; its back function ends both
`as_mut_ptr` borrows. -/
@[step]
theorem InPlaceOrDisjointBuffer.new_disjoint.spec {T : Type} [Pointee T] [Pointee.Lawful T]
    (src dst : Slice T)
    (h : src.length = dst.length) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.new_disjoint src dst
      ⦃ (b, back) => ⌜b.len = src.len ∧ (∀ b', back b' = (do
          let s ← Slice.end_as_mut_ptr src ⟨b.src.loc⟩
          let d ← Slice.end_as_mut_ptr dst b.dst
          ok (s, d))) ∧ b.src.Aligned ∧ b.dst.Aligned⌝ ∗ b.src ↦* src.val ∗
        b.src.freeable src.length .view ∗
        b.dst ↦* dst.val ∗ b.dst.freeable dst.length .view ⦄ := by
  unfold InPlaceOrDisjointBuffer.new_disjoint
  step*
  exact ⟨fun _ => by subst_vars; rfl, p_post, p2_post⟩

@[step]
theorem InPlaceOrDisjointBuffer.impl.len.spec {T : Type} (self : InPlaceOrDisjointBuffer T) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.impl.len self ⦃ r => ⌜r = self.len⌝ ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.len
  step*

@[step]
theorem InPlaceOrDisjointBuffer.impl.src.spec {T : Type} [Pointee T] [Pointee.Lawful T]
    (self : InPlaceOrDisjointBuffer T)
    (vs : List T) (h : self.len.val = vs.length) (hAlign : self.src.Aligned)
    (hNotNull : self.src.NotNull (self.len.val * Pointee.size T)) :
    ⦃ self.src ↦* vs ⦄ InPlaceOrDisjointBuffer.impl.src self
      ⦃ (s, back) => ⌜s.val = vs ∧ back = self.src.endBorrowRange vs⌝ ∗ self.src ↦† vs.length ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.src
  step*
  subst_vars
  iframe

@[step]
theorem InPlaceOrDisjointBuffer.impl.dst.spec {T : Type} [Pointee T] [Pointee.Lawful T]
    (self : InPlaceOrDisjointBuffer T)
    (vs : List T) (h : self.len.val = vs.length) (hAlign : self.dst.Aligned)
    (hNotNull : self.dst.NotNull (self.len.val * Pointee.size T)) :
    ⦃ self.dst ↦* vs ⦄ InPlaceOrDisjointBuffer.impl.dst self
      ⦃ (s, back, _) => ⌜s.val = vs⌝ ∗ self.dst ↦† vs.length ∗
        ⌜∀ s', s'.length = vs.length →
          ⦃ self.dst ↦† vs.length ⦄ back s' ⦃ b => ⌜b = self⌝ ∗ self.dst ↦* s'.val ⦄⌝ ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.dst
  step*
  subst vs_post
  rw [← h]
  have hBack : ∀ s' : Slice T, s'.length = self.len.val →
      ⦃ self.dst ↦† self.len.val ⦄ (do
        from_raw_parts_mut_back s'
        ok ({ src := self.src, dst := self.dst, len := self.len, _phantom := () } :
          InPlaceOrDisjointBuffer T))
      ⦃ b => ⌜b = self⌝ ∗ self.dst ↦* s'.val ⦄ := by
    intro s' hs'
    subst from_raw_parts_mut_back_post
    step*
  iframe

theorem zero_first_in_place.spec (buf : Slice U8) (h : 0 < buf.length) :
    ⦃ emp ⦄ zero_first_in_place buf ⦃ r => ⌜r = (buf.len, buf.set 0#usize 0#u8)⌝ ⦄ := by
  unfold zero_first_in_place
  step*
  iterate 2 (try (case hNotNull => apply RawPtr.notNull_of_pos; simp_all); try step*)
  rw [b_post2]
  step with Slice.end_as_mut_ptr.spec buf b.dst d1.val (by simp [d1_post, d_post])
  step*
  refine ⟨by simp [i_post, b1_post, b_post], Slice.ext _ _ ?_⟩
  simp [buf1_post, d1_post, d_post]

theorem copy_first.spec (src dst : Slice U8) (h : src.length = dst.length)
    (h0 : 0 < src.length) :
    ⦃ emp ⦄ copy_first src dst ⦃ r => ⌜r = (src, dst.set 0#usize (src.val[0]'h0))⌝ ⦄ := by
  unfold copy_first
  step*
  iterate 2 (try (case hNotNull => apply RawPtr.notNull_of_pos; simp_all); try step*)
  rw [src_back_post]
  step with RawPtr.endBorrowRange.spec b.src src.val
  step*
  case hNotNull => apply RawPtr.notNull_of_pos; simp [b_post]; scalar_tac
  step*
  rw [b_post1]
  step*
  exact ⟨Slice.ext _ _ s_post, Slice.ext _ _ (by simp_all)⟩

theorem increment_first_in_place.spec (buf : Slice U8) (h : 0 < buf.length) :
    ⦃ emp ⦄ increment_first_in_place buf
      ⦃ r => ⌜r = buf.set 0#usize (core.num.U8.wrapping_add (buf.val[0]'h) 1#u8)⌝ ⦄ := by
  unfold increment_first_in_place
  step* 1
  obtain ⟨src, dst, len, ph⟩ := b
  simp only at b_post b_post1 b_post2
  subst b_post1
  step*
  iterate 2 (try (case hNotNull => apply RawPtr.notNull_of_pos; simp_all); try step*)
  rw [src_back_post]
  step with RawPtr.endBorrowRange.spec (RawPtr.cast_const dst) buf.val
  rw [RawPtr.pointsToRange_cast_const]
  step*
  iterate 2 (try (case hNotNull => apply RawPtr.notNull_of_pos; simp_all); try step*)
  rw [b_post2]
  step with Slice.end_as_mut_ptr.spec buf dst s2.val (by simp [s2_post, s1_post])
  apply Slice.ext
  rw [r_post, s2_post, i_post, x_post, List.getElem_of_eq s_post]
  simp [s1_post]

end in_place_or_disjoint_buffer
