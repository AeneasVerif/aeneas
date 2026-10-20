import MaybeUninit

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace maybe_uninit

theorem init_with_write.spec : ⦃ emp ⦄ init_with_write ⦃ r => ⌜r = 7#u32⌝ ⦄ := by
  unfold init_with_write
  step*
  subst_vars
  step*

/-- `assume_init` on an uninitialized value fails. -/
theorem assume_init_uninit.fails (Q : IPost U64) : ¬ ispec emp assume_init_uninit Q := by
  apply not_ispec_of_ifails_emp
  unfold assume_init_uninit
  simp only [core.mem.maybe_uninit.MaybeUninit.uninit, Std.bind_ok]
  exact core.mem.maybe_uninit.MaybeUninit.assume_init.fails_uninit

/-- Reading uninitialized memory through a raw pointer fails. -/
theorem read_uninit.fails (Q : IPost U64) : ¬ ispec emp read_uninit Q := by
  apply not_ispec_of_ifails_emp
  unfold read_uninit
  simp only [core.mem.maybe_uninit.MaybeUninit.uninit, Std.bind_ok]
  refine ifails_bind (core.mem.maybe_uninit.MaybeUninit.as_ptr.spec _) fun ⟨p, back⟩ => ?_
  simp only [Std.uncurry, MaybeUninit.toOption_uninit]
  refine ifails_ipure fun _ => ifails_bind_left ?_
  exact ifails_mono (by iframe) (RawPtr.read.fails_uninit p)

@[step]
theorem Buffer.new.spec : ⦃ emp ⦄ Buffer.new ⦃ b => ⌜b.bytes.val = List.replicate 4 .uninit⌝ ⦄ := by
  unfold Buffer.new
  step*
  subst_vars
  simp

theorem Buffer.fill.spec (self : Buffer) :
    ⦃ emp ⦄ Buffer.fill self
      ⦃ (s, back) => ⌜s.val = [111#u8, 107#u8]⌝ ∗ iprop(∃ R, R ∗
        ⌜⦃ R ⦄ back ⦃ b => ⌜b.bytes.val =
          [.init 111#u8, .init 107#u8] ++ self.bytes.val.drop 2⌝ ⦄⌝) ⦄ := by
  unfold Buffer.fill
  step* 2
  have hs : s.val.length = 4 := by simp [s_post]
  have h0 := MaybeUninit.write_cast.spec_range p s.val 0 111#u8 (by omega)
  simp only [RawPtr.shift_zero] at h0
  step with h0
  step with MaybeUninit.add_cast.spec p (s.val.set 0 (.init 111#u8)) 1#usize (by simp; omega)
  subst_vars
  step with MaybeUninit.write_cast.spec_range p (s.val.set 0 (.init 111#u8)) 1 107#u8
    (by simp; omega)
  step with Slice.end_as_mut_ptr.spec s p ((s.val.set 0 (.init 111#u8)).set 1 (.init 107#u8))
    (by simp)
  step* 2
  have hfs : (self.bytes.from_slice s1).val = s1.val :=
    Std.Array.from_slice_val _ _ (by simp [s1_post, hs])
  have hs2 : s2.val = [111#u8, 107#u8].map MaybeUninit.init ++ self.bytes.val.drop 2 := by
    rw [s2_post]
    simp only [Std.Array.to_slice, hfs, s1_post, s_post]
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_append, List.getElem_drop]
    rcases j with _ | _ | j <;> simp <;> (congr 1; omega)
  rw [hs2, MaybeUninit.pointsToRange_init]
  step with core.slice.raw.from_raw_parts.spec (p3.cast U8) 2#usize [111#u8, 107#u8] rfl
  apply (WP.ispec_ok _).2
  rw [s3_post]
  apply entails_exists_r (iprop((p3.cast U8) ↦† 2 ∗
    ((p3.cast U8).shift 2) ↦*? (self.bytes.val.drop 2).map MaybeUninit.toOption ∗
    p3.freeable s2.length .view))
  refine entails_trans (pure_sep_intro _ s3_post) (sep_mono (entails_refl _)
    (entails_trans (pure_sep_intro _ ?_) (entails_of_eq (sep_comm_eq _ _))))
  subst from_raw_parts_back_post as_ptr_back_post
  apply WP.ispec_bind (RawPtr.endBorrowRange.spec_len _ s3.val 2 (by simp [s3_post]))
  · iframe
  · intro _
    apply WP.ispec_bind (Slice.end_as_ptr.spec s2 p3)
    · rw [hs2, MaybeUninit.pointsToRange_init, s3_post]
      iframe
    · intro _
      apply (WP.ispec_ok _).2
      refine fun _ _ => ?_
      simp only [pure_holds]
      rw [hfs, s1_post, s_post]
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp only [List.getElem_set, List.getElem_append, List.getElem_drop]
      rcases j with _ | _ | j <;> simp <;> (congr 1; omega)

theorem fill_first.spec : ⦃ emp ⦄ fill_first ⦃ r => ⌜r = 107#u8⌝ ⦄ := by
  unfold fill_first
  step* 1
  step with Buffer.fill.spec buf
  step* 1
  step with s_post1
  step*
  simp [i_post, s_post]

/-- Reading two bytes when only one was initialized fails. -/
theorem Buffer.fill_too_much.fails (self : Buffer)
    (h : self.bytes.val = List.replicate 4 .uninit) (Q : IPost (Slice U8 × Result Buffer)) :
    ¬ ispec emp (Buffer.fill_too_much self) Q := by
  apply not_ispec_of_ifails_emp
  unfold Buffer.fill_too_much
  simp only [lift, Std.bind_ok]
  rcases hts : self.bytes.to_slice_mut with ⟨s, tb⟩
  have hs : s.val = List.replicate 4 .uninit := by
    have := congrArg (fun x => x.1.val) hts
    simp only [Std.Array.to_slice_mut, Std.Array.to_slice] at this
    rw [← this]
    simp [h]
  refine ifails_bind (Slice.as_mut_ptr.spec s) fun ⟨p, ab⟩ => ?_
  simp only [Std.uncurry]
  refine ifails_ipure fun hab => ifails_ipure fun hAlign => ?_
  subst hab
  have h0 := MaybeUninit.write_cast.spec_range p s.val 0 111#u8 (by simp [hs]) hAlign
  simp only [RawPtr.shift_zero] at h0
  refine ifails_bind (ispec_frame h0 (p.freeable s.length .view)) fun _ => ?_
  refine ifails_bind (Slice.end_as_mut_ptr.spec s p _ (by simp)) fun s1 => ?_
  refine ifails_mono (entails_of_eq (sep_emp_r_eq _).symm) (ifails_ipure fun hs1 => ?_)
  refine ifails_bind (Slice.as_ptr.spec _) fun ⟨p2, ab2⟩ => ?_
  simp only [Std.uncurry]
  refine ifails_ipure fun _ => ifails_bind_left ?_
  have hs2 : (tb s1).to_slice.val =
      [111#u8].map MaybeUninit.init ++ [.uninit, .uninit, .uninit] := by
    have htb : tb = self.bytes.from_slice := by
      have := congrArg Prod.snd hts
      simp only [Std.Array.to_slice_mut] at this
      exact this.symm
    have hfs : (self.bytes.from_slice s1).val = s1.val :=
      Std.Array.from_slice_val _ _ (by simp [hs1, hs])
    simp only [Std.Array.to_slice, htb, hfs, hs1, hs]
    rfl
  rw [hs2, MaybeUninit.pointsToRange_init]
  refine ifails_mono ?_ (core.slice.raw.from_raw_parts.fails (p2.cast U8) 2#usize [111#u8]
    (Pointee.optCells none) (by simp) Pointee.UninitInvalid.ofCells_uninit (by simp))
  simp only [List.map, RawPtr.pointsToOpts_cons, RawPtr.pointsToOpt_eq]
  iframe

end maybe_uninit
