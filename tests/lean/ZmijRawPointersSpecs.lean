import ZmijRawPointers

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace zmij_raw_pointers

theorem pow10_minor.spec (i : Usize) (h : i.val < 4) :
    ⦃ emp ⦄ pow10_minor i ⦃ r => ⌜r = POW10_MINOR.val[i.val]'(by scalar_tac)⌝ ⦄ := by
  unfold pow10_minor
  step* 3
  subst_vars
  step with RawPtr.read.spec_range p POW10_MINOR.to_slice.val i.val (by scalar_tac)
  step*

theorem pow10_major.spec (i : Usize) (h : i.val < 2) :
    ⦃ emp ⦄ pow10_major i ⦃ r => ⌜r = POW10_MAJOR.val[i.val]'(by scalar_tac)⌝ ⦄ := by
  unfold pow10_major
  step* 3
  subst_vars
  step with RawPtr.read.spec_range p POW10_MAJOR.to_slice.val i.val (by scalar_tac)
  step*

theorem write_zeros_loop.spec (p : MutRawPtr U8) (n : Usize) (k : Nat) :
    ∀ (i : Usize) (vs : List U8), n.val - i.val = k → i.val ≤ n.val → n.val ≤ vs.length →
    ⦃ p ↦* vs ⦄ write_zeros_loop p n i
      ⦃ p ↦* vs.mapIdx (fun j x => if i.val ≤ j ∧ j < n.val then 48#u8 else x) ⦄ := by
  induction k with
  | zero =>
    intro i vs hk hi hn
    rw [write_zeros_loop, loop, write_zeros_loop.body, if_neg (by scalar_tac)]
    step*
    rw [show List.mapIdx (fun j x => if i.val ≤ j ∧ j < n.val then 48#u8 else x) vs = vs from
      List.ext_getElem (by simp) (fun j _ _ => by simp; omega)]
    iframe
  | succ k ih =>
    intro i vs hk hi hn
    rw [write_zeros_loop, loop, write_zeros_loop.body, if_pos (by scalar_tac)]
    step* 1
    subst_vars
    step with MutRawPtr.write.spec_range p vs i.val 48#u8 (by scalar_tac)
    step* 1
    have heq : List.mapIdx (fun j y => if i.val ≤ j ∧ j < n.val then 48#u8 else y) vs =
        List.mapIdx (fun j y => if x.val ≤ j ∧ j < n.val then 48#u8 else y)
          (vs.set i.val 48#u8) := by
      apply List.ext_getElem (by simp)
      intro j _ _
      simp only [List.getElem_mapIdx, List.getElem_set]
      split_ifs <;> first | rfl | scalar_tac
    rw [heq]
    exact ih x _ (by scalar_tac) (by scalar_tac) (by simp; scalar_tac)

/-- `write_zeros (q.shift o) n` writes `'0'` to the slots `o, …, o + n - 1` of the range of `q`. -/
@[step]
theorem write_zeros.spec (q : MutRawPtr U8) (o : Nat) (n : Usize) (vs : List U8)
    (h : o + n.val ≤ vs.length) :
    ⦃ q ↦* vs ⦄ write_zeros (q.shift o) n
      ⦃ q ↦* vs.mapIdx (fun j x => if o ≤ j ∧ j < o + n.val then 48#u8 else x) ⦄ := by
  have hSplit := RawPtr.pointsToRange_split q vs o
  have hTake : (vs.take o).length = o := by simp; omega
  rw [hTake] at hSplit
  have hPost := RawPtr.pointsToRange_split q
    (vs.mapIdx (fun j x => if o ≤ j ∧ j < o + n.val then 48#u8 else x)) o
  have hTake' : ((vs.mapIdx (fun j x => if o ≤ j ∧ j < o + n.val then 48#u8 else x)).take o).length
      = o := by simp; omega
  have hHead : (vs.mapIdx (fun j x => if o ≤ j ∧ j < o + n.val then 48#u8 else x)).take o
      = vs.take o := by
    apply List.ext_getElem (by simp)
    intro j _ _
    simp only [List.getElem_take, List.getElem_mapIdx]
    split_ifs <;> first | rfl | (simp at *; omega)
  have hTail : (vs.mapIdx (fun j x => if o ≤ j ∧ j < o + n.val then 48#u8 else x)).drop o
      = (vs.drop o).mapIdx (fun j x => if 0 ≤ j ∧ j < n.val then 48#u8 else x) := by
    apply List.ext_getElem (by simp)
    intro j _ _
    simp only [List.getElem_drop, List.getElem_mapIdx]
    split_ifs <;> first | rfl | omega
  rw [hTake', hHead, hTail] at hPost
  rw [hSplit, hPost]
  apply ispec_mono (write_zeros_loop.spec (q.shift o) n _ 0#usize (vs.drop o) rfl
    (by simp) (by simp; omega)) <;> iframe

/-- `c` is the digit character `'0' + d`. The cells may be uninitialized. -/
theorem write_digit_dot.spec_cells (p : MutRawPtr U8) (d c : U8) (cs : List (Option U8))
    (hc : c.val = 48 + d.val) (hlen : 2 ≤ cs.length) :
    ⦃ p ↦*? cs ⦄ write_digit_dot p d
      ⦃ q => ⌜q = p.shift 2⌝ ∗ p ↦*? ((cs.set 0 (some c)).set 1 (some 46#u8)) ⦄ := by
  unfold write_digit_dot
  step* 1
  have : i = c := by scalar_tac
  subst this
  have h0 := MutRawPtr.write.spec_cells p cs 0 i (by omega) (by simp)
  simp only [RawPtr.shift_zero] at h0
  step with h0
  step with RawPtr.add.spec_cells p (cs.set 0 (some i)) 1#usize (by simp; omega)
  subst_vars
  have h1 := MutRawPtr.write.spec_cells p (cs.set 0 (some i)) 1 46#u8 (by simp; omega) (by simp)
  step with h1
  step with RawPtr.add.spec_cells p ((cs.set 0 (some i)).set 1 (some 46#u8)) 2#usize
    (by simp; omega)

@[step]
theorem write_digit_dot.spec (p : MutRawPtr U8) (d c : U8) (vs : List U8)
    (hc : c.val = 48 + d.val) (hlen : 2 ≤ vs.length) :
    ⦃ p ↦* vs ⦄ write_digit_dot p d
      ⦃ q => ⌜q = p.shift 2⌝ ∗ p ↦* ((vs.set 0 c).set 1 46#u8) ⦄ := by
  have h := write_digit_dot.spec_cells p d c (vs.map some) hc (by simpa)
  simp only [← List.map_set] at h
  rw [RawPtr.pointsToRange_eq]
  simpa only [RawPtr.pointsToRange_eq] using h

theorem format_small.spec (d c : U8) (buf : Array U8 8#usize) (hc : c.val = 48 + d.val) :
    ⦃ emp ⦄ format_small d buf
      ⦃ r => ⌜r = (4#usize,
        (((buf.set 0#usize c).set 1#usize 46#u8).set 2#usize 48#u8).set 3#usize 48#u8)⌝ ⦄ := by
  unfold format_small
  step* 3
  subst_vars
  simp only [s_post]
  step with write_zeros.spec start 2 2#usize (((↑buf : List U8).set 0 c).set 1 46#u8) (by simp)
  step*
  case hLen => simp [s_post]
  rw [Std.Array.eq_iff, Std.Array.from_slice_val _ _ (by simp [s1_post])]
  simp only [s1_post, Std.Array.set_val_eq]
  apply List.ext_getElem (by simp)
  intro j _ _
  simp only [List.getElem_mapIdx, List.getElem_set]
  split_ifs <;> first | rfl | scalar_tac

@[step]
theorem Buffer.new.spec :
    ⦃ emp ⦄ Buffer.new ⦃ b => ⌜b.bytes.val = List.replicate 8 .uninit⌝ ⦄ := by
  unfold Buffer.new
  step*
  subst_vars
  simp

/-- `format_digit` writes `d.` (with `c = '0' + d`) to the uninitialized buffer and reads it back. -/
theorem Buffer.format_digit.spec (self : Buffer) (d c : U8) (hc : c.val = 48 + d.val) :
    ⦃ emp ⦄ Buffer.format_digit self d ⦃ (s, _) => ⌜s.val = [c, 46#u8]⌝ ⦄ := by
  unfold Buffer.format_digit
  step* 2
  have hs : s.val.length = 8 := by simp [s_post]
  rw [MaybeUninit.pointsToRange_eq]
  step with write_digit_dot.spec_cells (p.cast U8) d c (s.val.map MaybeUninit.toOption) hc
    (by simp [hs])
  have hcells : ((s.val.map MaybeUninit.toOption).set 0 (some c)).set 1 (some 46#u8) =
      ([c, 46#u8].map MaybeUninit.init ++ s.val.drop 2).map MaybeUninit.toOption := by
    rcases hl : s.val with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [hl] at hs ⊢
  rw [hcells, ← MaybeUninit.pointsToRange_eq]
  subst as_mut_ptr_back_post
  step with Slice.end_as_mut_ptr.spec s p ([c, 46#u8].map MaybeUninit.init ++ s.val.drop 2)
    (by simp; omega)
  step* 2
  subst to_slice_mut_back_post
  have hs2 : s2.val = [c, 46#u8].map MaybeUninit.init ++ self.bytes.val.drop 2 := by
    have hfs : (self.bytes.from_slice s1).val = s1.val :=
      Std.Array.from_slice_val _ _ (by simp [s1_post]; omega)
    simp [s2_post, Std.Array.to_slice, hfs, s1_post, s_post]
  rw [hs2, MaybeUninit.pointsToRange_init]
  step with core.slice.raw.from_raw_parts.spec (p2.cast U8) 2#usize [c, 46#u8] rfl
  step*

end zmij_raw_pointers
