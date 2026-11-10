import Aeneas

/-! Regression tests for the specifications of the exposures of `MaybeUninit` values and slices,
`ptr::from_ref` and the reborrows of raw pointers (`Aeneas/Std/ExposureSpecs.lean`), on small
programs written directly in Lean, with the shape of the extraction of the memory idioms of Ryu and
Zmij (`MaybeUninit` out-parameters, and `Buffer::format_finite` on `[MaybeUninit<u8>; N]`). -/

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result core.mem.maybe_uninit

namespace exposure_specs_tests

/-- `MaybeUninit` out-parameters: `as_mut_ptr`, `ptr::write`, the end of the borrow, and
`assume_init`. -/
def initialized_outputs (placement : Placement) : Result (U32 × U32) := do
  let a ← MaybeUninit.uninit U32
  let b ← MaybeUninit.uninit U32
  let (pa, a_back) ← MaybeUninit.as_mut_ptr (placement.addr 0) ⟨a⟩
  MutRawPtr.write pa 1#u32
  let a ← a_back
  let (pb, b_back) ← MaybeUninit.as_mut_ptr (placement.addr 1) ⟨b⟩
  MutRawPtr.write pb 2#u32
  let b ← b_back
  let x ← MaybeUninit.assume_init a
  let y ← MaybeUninit.assume_init b
  ok (x, y)

theorem initialized_outputs.spec (placement : Placement) :
    ⦃ emp ⦄ initialized_outputs placement ⦃ r => ⌜r = (1#u32, 2#u32)⌝ ⦄ := by
  unfold initialized_outputs
  step
  step
  subst a_post b_post
  step
  subst a_back_post
  have hw := MutRawPtr.write.spec_uninit pa [⟨none⟩] 0 1#u32 (by simp)
  simp only [RawPtr.elem_zero] at hw
  step with hw
  step
  -- the value read back is `⟨some _⟩` (`MaybeUninit.refines_singleton_some_iff`)
  subst a_post
  step
  subst b_back_post
  have hw := MutRawPtr.write.spec_uninit pb [⟨none⟩] 0 2#u32 (by simp)
  simp only [RawPtr.elem_zero] at hw
  step with hw
  step
  subst b_post
  step*

/-- `Buffer::format_finite`: the digits are written through `as_mut_ptr` on a buffer of
`MaybeUninit<u8>` (cast to `*mut u8`), and the initialized prefix is borrowed by `from_raw_parts`
through `as_ptr`. -/
def format (placement : Placement) (buf : Slice (MaybeUninit U8)) :
    Result (List U8 × Slice (MaybeUninit U8)) := do
  let (p, back) ← Slice.as_mut_ptr (placement.addr 0) ⟨buf⟩
  let q ← RawPtr.ptr_cast U8 p
  MutRawPtr.write q 49#u8
  let q1 ← RawPtr.add q 1#usize
  MutRawPtr.write q1 46#u8
  let out ← back
  let (p2, back2) ← Slice.as_ptr (placement.addr 1) ⟨out⟩
  let q2 ← RawPtr.ptr_cast U8 p2
  let (s, sback) ← core.slice.raw.from_raw_parts q2 2#usize
  sback
  back2
  ok (s.val.val, out)

theorem format.spec (placement : Placement) (buf : Slice (MaybeUninit U8))
    (hbuf : buf.val = List.replicate 4 ⟨none⟩) :
    ⦃ emp ⦄ format placement buf
      ⦃ r => ⌜r.1 = [49#u8, 46#u8]⌝ ∗
        ⌜MaybeUninit.Refines r.2.val [⟨some 49#u8⟩, ⟨some 46#u8⟩, ⟨none⟩, ⟨none⟩]⌝ ⦄ := by
  unfold format
  step with Slice.as_mut_ptr.spec_uninit (placement.addr 0) ⟨buf⟩ (by simp [hbuf])
  step
  subst q_post
  have hw := MutRawPtr.write.spec_uninit (p.cast U8) buf.val 0 49#u8 (by simp [hbuf])
  simp only [RawPtr.elem_zero] at hw
  step with hw
  have ha := RawPtr.add.spec_uninit (p.cast U8) (buf.val.set 0 ⟨some 49#u8⟩)
    0 1#usize (by simp [hbuf]) (by simp [hbuf])
  simp only [RawPtr.elem_zero] at ha
  step with ha
  subst q1_post
  step with MutRawPtr.write.spec_uninit (p.cast U8) (buf.val.set 0 ⟨some 49#u8⟩) (0 + 1) 46#u8
    (by simp [hbuf])
  subst back_post
  step with MaybeUninit.end_slice_as_mut_ptr.spec buf p
    ((buf.val.set 0 ⟨some 49#u8⟩).set (0 + 1) ⟨some 46#u8⟩) (by simp [Slice.length]) (by simp [hbuf])
  have hset : (buf.val.set 0 ⟨some 49#u8⟩).set
      (0 + 1) ⟨some 46#u8⟩ = [⟨some 49#u8⟩, ⟨some 46#u8⟩, ⟨none⟩, ⟨none⟩] := by
    simp [hbuf, List.replicate_succ]
  rw [hset] at out_post
  have heq : out.val = [49#u8, 46#u8].map (fun v => ⟨some v⟩) ++ out.val.drop 2 :=
    MaybeUninit.Refines.eq_append (xs := [49#u8, 46#u8])
    (ys := [⟨none⟩, ⟨none⟩]) out_post
  have hlen := out_post.1
  step with Slice.as_ptr.spec_uninit (placement.addr 1) ⟨out⟩ (by simp at hlen ⊢; omega)
  step
  subst q2_post
  have hf := core.slice.raw.from_raw_parts.spec_uninitShared_prefix (p2.cast U8) 2#usize 1
    [49#u8, 46#u8] (out.val.drop 2) (by simp) (by simp)
  rw [← heq] at hf
  step with hf
  subst sback_post
  step with RawPtr.endShareRange.spec_readable (p2.cast U8) 1 [49#u8, 46#u8] (by simp) (by simp)
  subst back2_post
  -- Merge the prefix back, and end the shared exposure.
  rw [ispec_exists]
  intro _
  have hm := (uninitShared_merge (p2.cast U8) 1 ([49#u8, 46#u8].map fun v => ⟨some v⟩)
    (out.val.drop 2)).frame ((p2.cast U8).exposure out.length)
  rw [List.length_map, ← heq, uninitShared_some] at hm
  rw [← sep_assoc_eq]
  refine ispec_realEntails_pre_u hm ?_
  step with RawPtr.endSharedUninitExposure.spec p2 out.val (by simp at hlen ⊢; omega)
    (fun _ => Repr.uscalar_decode_uninit _)
  step*

/-- Reads an initialized `MaybeUninit` value through `as_ptr`. -/
def read_init (placement : Placement) (x : MaybeUninit U32) : Result U32 := do
  let (p, back) ← MaybeUninit.as_ptr (placement.addr 0) ⟨x⟩
  let y ← RawPtr.read p
  back
  ok y

theorem read_init.spec (placement : Placement) (v : U32) :
    ⦃ emp ⦄ read_init placement ⟨some v⟩ ⦃ r => ⌜r = v⌝ ⦄ := by
  unfold read_init
  step with MaybeUninit.as_ptr.spec_some (placement.addr 0) ⟨⟨some v⟩⟩ v rfl
  step with RawPtr.read.spec_readable_head p 1 [v] (by simp)
  subst back_post
  step with MaybeUninit.end_as_ptr.spec_some p v
  step*

/-- `&raw const x`, a shared reborrow `&*p` of the place, and the ends of both borrows. -/
def deref_ref (placement : Placement) (x : U32) : Result U32 := do
  let (p, back) ← core.ptr.from_ref_model (placement.addr 0) ⟨x⟩
  let (r, rback) ← RawPtr.as_ref_unchecked p
  rback
  back
  ok r.val

theorem deref_ref.spec (placement : Placement) (x : U32) :
    ⦃ emp ⦄ deref_ref placement x ⦃ r => ⌜r = x⌝ ⦄ := by
  unfold deref_ref
  step with core.ptr.from_ref_model.spec_at (placement.addr 0) ⟨x⟩
  step with RawPtr.as_ref_unchecked.spec_readable p 1 x
  subst rback_post
  step with RawPtr.endShareRange.spec_readable p 1 [x] (by simp) (by simp)
  subst back_post
  step with core.ptr.from_ref_model.end_spec p x
  step*

/-- `&mut *p` on a cell of an exposure: the cell is borrowed. -/
example (q : MutRawPtr U32) (v : U32) :
    ⦃ q ↦ v ∗ q.exposure 1 ⦄ RawPtr.as_mut_unchecked q
      ⦃ (r, back) => ⌜r.val = v⌝ ∗
        ⌜back = fun v' => q.endBorrow (Pointee.repr (T := U32)) v'⌝ ∗ q ↦† 1 ∗ q.exposure 1 ⦄ := by
  refine ispec_conseq (ispec_frame (RawPtr.as_mut_unchecked.spec q v) (q.exposure 1))
    (entails_refl _) (fun r => ?_)
  obtain ⟨r, back⟩ := r
  simp only [postSep, uncurry_apply_pair]
  iframe

/-- `&*p` on an initialized element of a buffer. -/
example (p : RawPtr U8) (a b : U8) :
    ⦃ p ↦?* [⟨some a⟩, ⟨some b⟩, ⟨none⟩] ⦄ RawPtr.as_ref_unchecked (p.elem 1)
      ⦃ (r, back) => ⌜r.val = b⌝ ∗
        ⌜back = (p.elem 1).endShareRange (Pointee.repr (T := U8)) [b]⌝ ∗
        (p ↦?* [⟨some a⟩] ∗ (p.elem 1).readable 1 [b] ∗ (p.elem 2) ↦?* [⟨none⟩]) ⦄ :=
  RawPtr.as_ref_unchecked.spec_uninit p _ 1 b (by simp) rfl

#print axioms initialized_outputs.spec
#print axioms format.spec
#print axioms read_init.spec
#print axioms deref_ref.spec
#print axioms MaybeUninit.allocExposure.spec
#print axioms MaybeUninit.allocSharedExposure.spec
#print axioms RawPtr.endUninitExposure.spec
#print axioms RawPtr.endSharedUninitExposure.spec
#print axioms MaybeUninit.end_as_mut_ptr.spec
#print axioms MaybeUninit.end_slice_as_mut_ptr.spec
#print axioms Slice.as_mut_ptr.spec_uninit_at
#print axioms Slice.as_ptr.spec_uninit_at
#print axioms core.mem.maybe_uninit.MaybeUninit.as_mut_ptr.spec_at
#print axioms core.mem.maybe_uninit.MaybeUninit.as_ptr.spec_at
#print axioms core.slice.raw.from_raw_parts.spec_uninit_prefix
#print axioms core.slice.raw.from_raw_parts.spec_uninitShared_prefix
#print axioms core.ptr.from_ref_model.spec_at
#print axioms RawPtr.as_ref_unchecked.spec_uninit
#print axioms RawPtr.as_mut_unchecked.spec

end exposure_specs_tests
