import RawPointers

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace raw_pointers

/-- Read through the pointer to the first slot of a range. -/
theorem read_head.spec {T : Type} [Pointee T] [Pointee.Sized T] (q : RawPtr T) (values : List T)
    (h : 0 < values.length) :
    ⦃ q ↦* values ⦄ q.read ⦃ r => ⌜r = values[0]⌝ ∗ q ↦* values ⦄ := by
  simpa using RawPtr.read.spec_range q values 0 h

/-- Write through the pointer to the first slot of a range. -/
theorem write_head.spec {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.NoPointers T]
    (q : MutRawPtr T) (values : List T) (v : T) (h : 0 < values.length) :
    ⦃ q ↦* values ⦄ MutRawPtr.write q v ⦃ q ↦* values.set 0 v ⦄ := by
  simpa using MutRawPtr.write.spec_range q values 0 v h

theorem read_via_ptr.spec (placement : Placement) (data : Array U16 8#usize) :
    ⦃ emp ⦄ read_via_ptr placement (SharedBorrow.mk data) ⦃ r => ⌜r = data[1]!⌝ ⦄ := by
  unfold read_via_ptr
  step* 2
  · subst s_post; simp [Array.as_slice, Slice.length]
  have hs : s.val.val = data.val := by simp [s_post, Array.as_slice]
  step with RawPtr.add.spec_readable ptr 1 s.val.val 1#usize (by simp [hs]) (by simp [hs])
  subst p_post
  step with RawPtr.read.spec_readable ptr 1 s.val.val 1 (by simp [hs])
  subst as_ptr_back_post
  step with Slice.end_as_ptr.spec s.val ptr (by simp [Slice.length, hs])
  step*
  simp [i_post, hs]

theorem write_via_ptr.spec (placement : Placement) (data : Array U16 8#usize) :
    ⦃ emp ⦄ write_via_ptr placement (MutBorrow.mk data) ⦃ r => ⌜r = data.set 2#usize 42#u16⌝ ⦄ := by
  unfold write_via_ptr
  step* 2
  have hlen : s.val.val.length = 8 := by simp [s_post]
  step with RawPtr.add.spec ptr s.val.val 2#usize (by simp [hlen]) (by simp [hlen])
  subst p_post
  step with MutRawPtr.write.spec_range ptr s.val.val 2 42#u16 (by simp [hlen])
  subst as_mut_ptr_back_post
  step with Slice.end_as_mut_ptr.spec s.val ptr (s.val.val.set 2 42#u16) (by simp [Slice.length]) (by simp [hlen])
  step*
  subst as_mut_slice_back_post
  rw [Std.Array.eq_iff, Std.Array.from_slice_val _ _ (by simp [s1_post, s_post])]
  simp [s1_post, s_post]

theorem write_then_read.spec (placement : Placement) (data : Slice U32) (h : 0 < data.length) :
    ⦃ emp ⦄ write_then_read placement (MutBorrow.mk data)
      ⦃ r => ⌜r = (1#u32, data.set 0#usize 1#u32)⌝ ⦄ := by
  unfold write_then_read
  step* 1
  step with write_head.spec p data.val 1#u32 h
  subst as_mut_ptr_back_post
  step with Slice.end_as_mut_ptr.spec data p (data.val.set 0 1#u32) (by simp [Slice.length])
    (by simpa using h)
  step*
  refine ⟨?_, Slice.ext _ _ ?_⟩
  · rw [i_post, Slice.getElem_Nat_eq, List.getElem_of_eq data1_post]
    · simp
    · simpa [data1_post] using h
  · simp [data1_post]

theorem local_array.spec (placement : Placement) :
    ⦃ emp ⦄ local_array placement ⦃ r => ⌜r = 7#u8⌝ ⦄ := by
  unfold local_array
  step* 2
  have hs : s.val.val = [0#u8, 0#u8, 0#u8, 0#u8] := by simp [s_post, Array.repeat]
  step with RawPtr.add.spec p s.val.val 3#usize (by simp [hs]) (by simp [hs])
  subst p1_post
  step with MutRawPtr.write.spec_range p s.val.val 3 7#u8 (by simp [hs])
  subst as_mut_ptr_back_post
  step with Slice.end_as_mut_ptr.spec s.val p (s.val.val.set 3 7#u8) (by simp [Slice.length])
    (by simp [hs])
  step*
  simp_all [Array.from_slice]

/-- `first_ptr` hands the slice back unchanged; the returned pointer dangles (its exposure is
retired). -/
theorem first_ptr.spec (placement : Placement) (data : Slice U8) (h : 0 < data.length) :
    ⦃ emp ⦄ first_ptr placement (MutBorrow.mk data) ⦃ r => ⌜r.2 = data⌝ ⦄ := by
  unfold first_ptr
  step* 1
  subst as_mut_ptr_back_post
  step with Slice.end_as_mut_ptr.spec data p data.val rfl h
  step*

@[step]
theorem write_through.spec (p : MutRawPtr U8) (v old : U8) :
    ⦃ p ↦ old ⦄ write_through p v ⦃ p ↦ v ⦄ := by
  unfold write_through
  step*

theorem write_through.spec_head (p : MutRawPtr U8) (v : U8) (values : List U8)
    (h : 0 < values.length) :
    ⦃ p ↦* values ⦄ write_through p v ⦃ p ↦* values.set 0 v ⦄ := by
  unfold write_through
  simpa using MutRawPtr.write.spec_range p values 0 v h

theorem swap_through_ptrs.spec (placement : Placement) (x : Slice U64) (h : 2 ≤ x.length) :
    ⦃ emp ⦄ swap_through_ptrs placement (MutBorrow.mk x)
      ⦃ r => ⌜r = (x.set 0#usize x[1]!).set 1#usize x[0]!⌝ ⦄ := by
  unfold swap_through_ptrs
  step* 1
  step with read_head.spec p x.val (by scalar_tac)
  step with RawPtr.add.spec p x.val 1#usize (by scalar_tac) (by scalar_tac)
  subst b_post
  step with RawPtr.read.spec_range p x.val 1 (by scalar_tac)
  step with write_head.spec p x.val _ (by scalar_tac)
  step with RawPtr.add.spec p (x.val.set 0 b1) 1#usize (by simp; scalar_tac) (by simp; scalar_tac)
  subst p1_post
  step with MutRawPtr.write.spec_range p (x.val.set 0 b1) 1 a (by simp; scalar_tac)
  subst as_mut_ptr_back_post
  step with Slice.end_as_mut_ptr.spec x p ((x.val.set 0 b1).set 1 a) (by simp [Slice.length])
    (by simp; scalar_tac)
  apply Slice.ext
  rw [r_post, a_post, b1_post]
  simp only [Slice.set_val_eq, Slice.getElem!_Nat_eq]
  rw [getElem!_pos (↑x : List U64) 1 (by scalar_tac), getElem!_pos (↑x : List U64) 0 (by scalar_tac)]
  simp

/-- `sum_via_slice` from a range which is already shared (`0 < depth`): the share made by
`from_raw_parts` is then ended by its backward function. (From an exclusive range, `p ↦* vs`,
ending the share would need `RawPtr.endShareRange` back to depth `0`, which the model does not
provide.) -/
theorem sum_via_slice.spec (p : ConstRawPtr U8) (len : Usize) (depth : Nat) (vs : List U8)
    (hdepth : 0 < depth) (h : len.val = vs.length) (h2 : 2 ≤ vs.length) :
    ⦃ p.range depth vs ⦄ sum_via_slice p len
      ⦃ r => ⌜r.val = (vs[0].val + vs[1].val) % 256⌝ ∗ p.range depth vs ⦄ := by
  unfold sum_via_slice
  step with core.slice.raw.from_raw_parts.spec p len depth vs h (by omega)
  step* 3
  subst from_raw_parts_back_post
  step with RawPtr.endShareRange.spec p depth vs hdepth (by omega)
  step*
  subst vs_post
  simp [*, U8.size, U8.numBits]
  rfl

/- `set_via_slice` is not specified: its backward function `from_raw_parts_mut.back`, which writes
the slice back to the borrowed range (`p ↦† len`), has no specification in
`Aeneas.Std.RawPtrSpecs`. -/

theorem boxed.spec : ⦃ emp ⦄ boxed ⦃ r => ⌜r = 4#u32⌝ ⦄ := by
  unfold boxed
  step*

theorem call_write_through.spec (placement : Placement) (data : Slice U8) (h : 0 < data.length) :
    ⦃ emp ⦄ call_write_through placement (MutBorrow.mk data) ⦃ r => ⌜r = data.set 0#usize 9#u8⌝ ⦄ := by
  unfold call_write_through
  step* 1
  step with write_through.spec_head p 9#u8 data.val h
  subst as_mut_ptr_back_post
  step with Slice.end_as_mut_ptr.spec data p (data.val.set 0 9#u8) (by simp [Slice.length])
    (by simpa using h)
  exact Slice.ext _ _ (by simp [*])

end raw_pointers
