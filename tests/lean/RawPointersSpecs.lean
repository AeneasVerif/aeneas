import RawPointers

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace raw_pointers

/-- Read through the pointer to the first slot of a range. -/
theorem read_head.spec {T : Type} [Pointee T] [Pointee.Lawful T] {M} (q : RawPtr T M)
    (values : List T) (h : 0 < values.length) (hAlign : q.Aligned) :
    ⦃ q ↦* values ⦄ q.read ⦃ r => ⌜r = values[0]⌝ ∗ q ↦* values ⦄ := by
  simpa using RawPtr.read.spec_range q values 0 h hAlign

theorem read_via_ptr.spec (data : Array U16 8#usize) :
    ⦃ emp ⦄ read_via_ptr data ⦃ r => ⌜r = data[1]!⌝ ⦄ := by
  unfold read_via_ptr
  step* 3
  subst_vars
  step with RawPtr.read.spec_range ptr data.to_slice.val 1 (by simp)
  step*
  simp [i_post]

theorem write_via_ptr.spec (data : Array U16 8#usize) :
    ⦃ emp ⦄ write_via_ptr data ⦃ r => ⌜r = data.set 2#usize 42#u16⌝ ⦄ := by
  unfold write_via_ptr
  step* 3
  subst_vars
  step with MutRawPtr.write.spec_range ptr s.val 2 42#u16 (by simp [s_post])
  step*
  rw [Std.Array.eq_iff, Std.Array.from_slice_val _ _ (by simp [s1_post, s_post])]
  simp [s1_post, s_post]

theorem write_then_read.spec (data : Slice U32) (h : 0 < data.length) :
    ⦃ emp ⦄ write_then_read data ⦃ r => ⌜r = (1#u32, data.set 0#usize 1#u32)⌝ ⦄ := by
  unfold write_then_read
  step* 1
  subst_vars
  step with MutRawPtr.write.spec_head p data.val 1#u32 (by simpa using h)
  step*
  refine ⟨?_, Slice.ext _ _ ?_⟩
  · rw [i_post, List.getElem_of_eq data1_post]; simp
  · simp [data1_post]

theorem local_array.spec : ⦃ emp ⦄ local_array ⦃ r => ⌜r = 7#u8⌝ ⦄ := by
  unfold local_array
  step* 3
  subst_vars
  step with MutRawPtr.write.spec_range p s.val 3 7#u8 (by simp [s_post])
  step*
  simp [Std.Array.from_slice, s1_post, s_post]

/-- `first_ptr` hands the slice back unchanged; the returned pointer dangles (its slots are dead). -/
theorem first_ptr.spec (data : Slice U8) :
    ⦃ emp ⦄ first_ptr data ⦃ r => ⌜r.2 = data⌝ ⦄ := by
  unfold first_ptr
  step* 1
  subst_vars
  step*

@[step]
theorem write_through.spec (p : MutRawPtr U8) (v old : U8) :
    ⦃ p ↦ old ⦄ write_through p v ⦃ p ↦ v ⦄ := by
  unfold write_through
  step*

theorem write_through.spec_head (p : MutRawPtr U8) (v : U8) (values : List U8)
    (h : 0 < values.length) :
    ⦃ p ↦* values ⦄ write_through p v ⦃ p ↦* values.set 0 v ⦄ := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_length_pos h
  rw [List.set_cons_zero, RawPtr.pointsToRange_cons, RawPtr.pointsToRange_cons]
  apply ispec_mono (write_through.spec p v x) <;> iframe

theorem swap_through_ptrs.spec (x : Slice U64) (h : 2 ≤ x.length) :
    ⦃ emp ⦄ swap_through_ptrs x ⦃ r => ⌜r = (x.set 0#usize x[1]!).set 1#usize x[0]!⌝ ⦄ := by
  unfold swap_through_ptrs
  step* 1
  subst_vars
  step with read_head.spec p x.val (by scalar_tac)
  step* 1
  subst_vars
  step with RawPtr.read.spec_range p x.val 1 (by scalar_tac)
  step with MutRawPtr.write.spec_head p x.val _ (by scalar_tac)
  step* 1
  subst_vars
  step with MutRawPtr.write.spec_range p ((↑x : List U64).set 0 (x.val[1]'(by scalar_tac))) 1 _
    (by simp; scalar_tac)
  step*
  apply Slice.ext
  rw [r_post]
  simp only [Slice.set_val_eq, Slice.getElem!_Nat_eq]
  rw [getElem!_pos (↑x : List U64) 1 (by scalar_tac), getElem!_pos (↑x : List U64) 0 (by scalar_tac)]
  simp

theorem set_via_slice.spec (p : MutRawPtr U8) (len : Usize) (v : U8) (vs : List U8)
    (h : (v :: vs).length = len.val) :
    ⦃ p ↦* (v :: vs) ⦄ set_via_slice p len ⦃ p ↦* (1#u8 :: vs) ⦄ := by
  unfold set_via_slice
  step* 1
  case hNotNull => apply RawPtr.notNull_of_pos; simp; scalar_tac
  step* 1
  subst_vars
  rw [show (1#u8 :: vs) = (s.set 0#usize 1#u8).val by simp [s_post]]
  step with core.slice.raw.from_raw_parts_mut.back.spec p len (s.set 0#usize 1#u8)
    (by simp [s_post, ← h])

theorem sum_via_slice.spec (p : ConstRawPtr U8) (len : Usize) (vs : List U8)
    (h : len.val = vs.length) (h2 : 2 ≤ vs.length) :
    ⦃ p ↦* vs ⦄ sum_via_slice p len
      ⦃ r => ⌜r.val = (vs[0].val + vs[1].val) % 256⌝ ∗ p ↦* vs ⦄ := by
  unfold sum_via_slice
  step* 4
  try (case hNotNull => apply RawPtr.notNull_of_pos; simp; scalar_tac)
  try step* 1
  subst from_raw_parts_back_post
  rw [vs_post]
  step*
  subst vs_post
  simp [*, U8.size, U8.numBits]

theorem boxed.spec : ⦃ emp ⦄ boxed ⦃ r => ⌜r = 4#u32⌝ ⦄ := by
  unfold boxed
  step*

theorem call_write_through.spec (data : Slice U8) (h : 0 < data.length) :
    ⦃ emp ⦄ call_write_through data ⦃ r => ⌜r = data.set 0#usize 9#u8⌝ ⦄ := by
  unfold call_write_through
  step* 1
  subst_vars
  step with write_through.spec_head p 9#u8 data.val (by scalar_tac)
  step*
  exact Slice.ext _ _ (by simp [r_post])

end raw_pointers
