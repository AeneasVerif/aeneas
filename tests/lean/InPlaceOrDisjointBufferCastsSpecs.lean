import InPlaceOrDisjointBufferCasts

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace in_place_or_disjoint_buffer_casts

/-- The cells of `n` values are the cells of the array of these values: a pointer to them can be
cast to a pointer to the array. -/
theorem pointsToRange_eq_array {T : Type} [Pointee T] {M : Mutability} (q : RawPtr T M)
    (vs : List T) {n : Usize} (h : vs.length = n.val) :
    (q ↦* vs) = ((q.cast (Std.Array T n)) ↦ Std.Array.from vs h) := by
  rw [RawPtr.pointsToRange_eq_cells, RawPtr.pointsTo_eq, RawPtr.pointsToCells_eq_array,
    RawPtr.pointsToCells_eq_array]
  show owns (Heap.array q.loc _) = owns (Heap.array q.loc ((Std.Array.from vs h).val.flatMap _))
  rw [Std.Array.from_val]

/-- A 16-byte block, as read/written by `loadu_block`/`storeu_block`. -/
abbrev Block := Std.Array U8 16#usize

/-- Splitting a range of bytes around a 16-byte block at `offset`. -/
theorem pointsToRange_split_block {M : Mutability} (q : RawPtr U8 M) (vs : List U8) (offset : Nat)
    (b : Block) (hb : b.val = (vs.drop offset).take 16) (h : offset + 16 ≤ vs.length) :
    (q ↦* vs) = iprop(q ↦* vs.take offset ∗ (q.shift offset).cast Block ↦ b ∗
      (q.shift (offset + 16)) ↦* vs.drop (offset + 16)) := by
  have hBlock : ((vs.drop offset).take 16).length = (16#usize : Usize).val := by
    simp; omega
  have hEq : b = Std.Array.from _ hBlock := Std.Array.ext _ _ (by simp [hb])
  rw [hEq, RawPtr.pointsToRange_split q vs offset,
    RawPtr.pointsToRange_split (q.shift _) (vs.drop offset) 16,
    ← pointsToRange_eq_array _ _ hBlock, RawPtr.shift_shift, List.drop_drop]
  have h1 : (vs.take offset).length = offset := by grind
  have h2 : ((vs.drop offset).take 16).length = 16 := by grind
  rw [h1, h2]

/-- `loadu_block` reads the 16 bytes from `offset` on, through a `[u8; 16]` pointer. -/
theorem InPlaceOrDisjointBuffer.loadu_block_src.spec (self : InPlaceOrDisjointBuffer U8)
    (vs : List U8) (offset : Usize) (h : offset.val + 16 ≤ vs.length) :
    ⦃ self.src ↦* vs ⦄ InPlaceOrDisjointBuffer.loadu_block_src self offset
      ⦃ r => ⌜r.val = (vs.drop offset.val).take 16⌝ ∗ self.src ↦* vs ⦄ := by
  unfold InPlaceOrDisjointBuffer.loadu_block_src
  have hBlock : ((vs.drop offset.val).take 16).length = (16#usize : Usize).val := by
    simp; omega
  apply WP.ispec_bind (RawPtr.add.spec self.src vs offset (by omega))
  · iframe
  · intro p
    rw [sep_emp_r_eq, ispec_ipure]; intro _
    subst_vars
    rw [pointsToRange_split_block self.src vs offset.val (Std.Array.from _ hBlock) (by simp) h]
    apply WP.ispec_mono (RawPtr.read_unaligned.spec _ (Std.Array.from _ hBlock) (by simp))
    · iframe
    · apply postWand_intro
      intro r
      iintro hr
      subst hr
      simp only [Std.Array.from_val]
      iframe

/-- `storeu_block` overwrites the 16 bytes from `offset` on, through a `[u8; 16]` pointer. -/
theorem InPlaceOrDisjointBuffer.storeu_block.spec (self : InPlaceOrDisjointBuffer U8)
    (vs : List U8) (offset : Usize) (value : Block) (h : offset.val + 16 ≤ vs.length) :
    ⦃ self.dst ↦* vs ⦄ InPlaceOrDisjointBuffer.storeu_block self offset value
      ⦃ r => ⌜r.1 = self⌝ ∗
        self.dst ↦* (vs.take offset.val ++ value.val ++ vs.drop (offset.val + 16)) ⦄ := by
  unfold InPlaceOrDisjointBuffer.storeu_block
  have hv : value.val.length = 16 := by simp
  have hTake : offset.val ≤ (vs.take offset.val).length := by simp; omega
  have ht : (vs.take offset.val ++ value.val ++ vs.drop (offset.val + 16)).take offset.val =
      vs.take offset.val := by
    rw [List.append_assoc, List.take_left' (by simp; omega)]
  have hd : (vs.take offset.val ++ value.val ++ vs.drop (offset.val + 16)).drop
      (offset.val + 16) = vs.drop (offset.val + 16) := List.drop_left' (by simp; omega)
  have hNew := pointsToRange_split_block self.dst
    (vs.take offset.val ++ value.val ++ vs.drop (offset.val + 16)) offset.val value
    (by simp [List.drop_append_of_le_length hTake, hv]) (by simp; omega)
  rw [ht, hd] at hNew
  rw [hNew]
  apply WP.ispec_bind (RawPtr.add.spec self.dst vs offset (by omega))
  · iframe
  · intro p
    rw [sep_emp_r_eq, ispec_ipure]; intro _
    subst_vars
    have hB : ((vs.drop offset.val).take 16).length = (16#usize : Usize).val := by simp; omega
    rw [pointsToRange_split_block self.dst vs offset.val (Std.Array.from _ hB) (by simp) h]
    apply WP.ispec_bind (MutRawPtr.write_unaligned.spec _ _ value (by simp))
    · iframe
    · intro _
      apply (WP.ispec_ok _).2
      iframe

end in_place_or_disjoint_buffer_casts
