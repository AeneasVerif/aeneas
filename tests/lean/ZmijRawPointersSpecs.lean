import ZmijRawPointers

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace zmij_raw_pointers

/-- `uint128` is not zero-sized: its fields (`u64`) aren't (its layout is unspecified, see
`Repr.unspecified`). -/
instance : Pointee.Sized uint128 := ⟨Repr.unspecified_sized (by
  show 0 < Repr.prodSize (Pointee.repr (T := U64)) (Pointee.repr (T := U64))
  have := Repr.prodEnd_le (Pointee.repr (T := U64)) (Pointee.repr (T := U64))
  have := Pointee.Sized.pos (T := U64)
  omega)⟩

/-- Write through the pointer to the first slot of a range. -/
theorem write_head.spec {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.NoPointers T]
    (q : MutRawPtr T) (values : List T) (v : T) (h : 0 < values.length) :
    ⦃ q ↦* values ⦄ MutRawPtr.write q v ⦃ q ↦* values.set 0 v ⦄ := by
  simpa using MutRawPtr.write.spec_range q values 0 v h

theorem pow10_minor.spec (placement : Placement) (i : Usize) (h : i.val < 4) :
    ⦃ emp ⦄ pow10_minor placement i ⦃ r => ⌜r = POW10_MINOR.val[i.val]'(by scalar_tac)⌝ ⦄ := by
  unfold pow10_minor
  step* 2
  · subst s_post; simp [Array.as_slice, Slice.length]
  have hs : s.val.val = POW10_MINOR.val := by simp [s_post, Array.as_slice]
  step with RawPtr.add.spec_readable p 1 s.val.val i (by simp [hs]) (by simp [hs]; omega)
  subst p1_post
  step with RawPtr.read.spec_readable p 1 s.val.val i.val (by simp [hs]; omega)
  subst as_ptr_back_post
  step with Slice.end_as_ptr.spec s.val p (by simp [Slice.length, hs])
  step*

theorem pow10_major.spec (placement : Placement) (i : Usize) (h : i.val < 2) :
    ⦃ emp ⦄ pow10_major placement i ⦃ r => ⌜r = POW10_MAJOR.val[i.val]'(by scalar_tac)⌝ ⦄ := by
  unfold pow10_major
  step* 2
  · subst s_post; simp [Array.as_slice, Slice.length]
  have hs : s.val.val = POW10_MAJOR.val := by simp [s_post, Array.as_slice]
  step with RawPtr.add.spec_readable p 1 s.val.val i (by simp [hs]) (by simp [hs]; omega)
  subst p1_post
  step with RawPtr.read.spec_readable p 1 s.val.val i.val (by simp [hs]; omega)
  subst as_ptr_back_post
  step with Slice.end_as_ptr.spec s.val p (by simp [Slice.length, hs])
  step*

theorem write_zeros_loop.spec (p : MutRawPtr U8) (n : Usize) (k : Nat) :
    ∀ (i : Usize) (vs : List U8), n.val - i.val = k → i.val ≤ n.val → n.val ≤ vs.length →
    0 < vs.length →
    ⦃ p ↦* vs ⦄ write_zeros_loop p n i
      ⦃ p ↦* vs.mapIdx (fun j x => if i.val ≤ j ∧ j < n.val then 48#u8 else x) ⦄ := by
  induction k with
  | zero =>
    intro i vs hk hi hn hne
    have hc : ¬ i < n := by scalar_tac
    rw [write_zeros_loop, loop, write_zeros_loop.body]
    simp only [hc, ↓reduceIte]
    step*
    rw [show List.mapIdx (fun j x => if i.val ≤ j ∧ j < n.val then 48#u8 else x) vs = vs from
      List.ext_getElem (by simp) (fun j _ _ => by simp; omega)]
    iframe
  | succ k ih =>
    intro i vs hk hi hn hne
    have hc : i < n := by scalar_tac
    rw [write_zeros_loop, loop, write_zeros_loop.body]
    simp only [hc, ↓reduceIte]
    step with RawPtr.add.spec p vs i hne (by scalar_tac)
    subst p1_post
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
    exact ih x _ (by scalar_tac) (by scalar_tac) (by simp; scalar_tac) (by simpa using hne)

/-- `write_zeros p n` writes `'0'` to the first `n` slots of the range of `p`. -/
@[step]
theorem write_zeros.spec (p : MutRawPtr U8) (n : Usize) (vs : List U8)
    (h : n.val ≤ vs.length) (hne : 0 < vs.length) :
    ⦃ p ↦* vs ⦄ write_zeros p n
      ⦃ p ↦* vs.mapIdx (fun j x => if j < n.val then 48#u8 else x) ⦄ := by
  have := write_zeros_loop.spec p n n.val 0#usize vs (by simp) (by simp) h hne
  simpa using this

/-- `c` is the digit character `'0' + d`. -/
@[step]
theorem write_digit_dot.spec (p : MutRawPtr U8) (d c : U8) (vs : List U8)
    (hc : c.val = 48 + d.val) (hlen : 2 ≤ vs.length) :
    ⦃ p ↦* vs ⦄ write_digit_dot p d
      ⦃ q => ⌜q = p.elem 2⌝ ∗ p ↦* ((vs.set 0 c).set 1 46#u8) ⦄ := by
  unfold write_digit_dot
  step* 1
  have : i = c := by scalar_tac
  subst this
  step with write_head.spec p vs i (by scalar_tac)
  step with RawPtr.add.spec p (vs.set 0 i) 1#usize (by simp; scalar_tac) (by simp; scalar_tac)
  subst p1_post
  step with MutRawPtr.write.spec_range p (vs.set 0 i) 1 46#u8 (by simp; scalar_tac)
  step with RawPtr.add.spec p ((vs.set 0 i).set 1 46#u8) 2#usize (by simp; scalar_tac)
    (by simp; scalar_tac)

/- `format_small` is not specified: it calls `write_zeros` on `start.elem 2`, a pointer into the
middle of the range of `start`. This needs either a splitting rule for ranges
(`p ↦* vs ⊣⊢ p ↦* vs.take i ∗ p.elem i ↦* vs.drop i`) or a specification of `RawPtr.add` from a
pointer into a range, neither of which `Aeneas.Std.RawPtrSpecs` provides (the splitting rule needs
`p.address + i * size` not to overflow, which the points-to assertion does not record). -/

end zmij_raw_pointers
