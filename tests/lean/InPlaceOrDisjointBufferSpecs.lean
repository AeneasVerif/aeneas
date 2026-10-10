import InPlaceOrDisjointBuffer

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace in_place_or_disjoint_buffer

/-- `new_in_place` exposes the cells of `buffer`; its back function retires the exposure of
`as_mut_ptr`, turning the cells back into the slice. -/
@[step]
theorem InPlaceOrDisjointBuffer.new_in_place.spec {T : Type} [Pointee T] [Pointee.Sized T]
    [Pointee.Calibrated T] (placement : Placement) (buffer : Slice T) (h : 0 < buffer.length) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.new_in_place placement (MutBorrow.mk buffer)
      ⦃ (b, back) => ⌜b.len.val = buffer.length ∧ b.src = b.dst.cast_const ∧
        ∀ b', back b' = Slice.end_as_mut_ptr (Pointee.repr (T := T)) buffer b.dst⌝ ∗
        b.dst ↦* buffer.val ∗ b.dst.exposure buffer.length ⦄ := by
  unfold InPlaceOrDisjointBuffer.new_in_place
  step*

/-- `new_disjoint` exposes the cells of `src` and `dst`; its back function retires both
exposures. -/
@[step]
theorem InPlaceOrDisjointBuffer.new_disjoint.spec {T : Type} [Pointee T] [Pointee.Sized T]
    [Pointee.Calibrated T] (placement : Placement) (src dst : Slice T) (h : src.length = dst.length)
    (h0 : 0 < src.length) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.new_disjoint placement (MutBorrow.mk src) (MutBorrow.mk dst)
      ⦃ (b, back) => ⌜b.len.val = src.length ∧ ∀ b', back b' = (do
          let s ← Slice.end_as_mut_ptr (Pointee.repr (T := T)) src b.src
          let d ← Slice.end_as_mut_ptr (Pointee.repr (T := T)) dst b.dst
          ok (s, d))⌝ ∗ b.src ↦* src.val ∗ b.src.exposure src.length ∗
        b.dst ↦* dst.val ∗ b.dst.exposure dst.length ⦄ := by
  unfold InPlaceOrDisjointBuffer.new_disjoint
  step*
  subst as_mut_ptr_back_post as_mut_ptr_back1_post
  exact ⟨by simp [Slice.len, Slice.length], fun _ => rfl⟩

@[step]
theorem InPlaceOrDisjointBuffer.impl.len.spec {T : Type} [Pointee T]
    (self : InPlaceOrDisjointBuffer T) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.impl.len (SharedBorrow.mk self) ⦃ r => ⌜r = self.len⌝ ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.len
  step*

/-- `src` shares the cells of the source range as a slice; its back function ends the share. -/
@[step]
theorem InPlaceOrDisjointBuffer.impl.src.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (self : InPlaceOrDisjointBuffer T) (depth : Nat) (vs : List T) (h : self.len.val = vs.length)
    (h0 : 0 < vs.length) :
    ⦃ self.src.range depth vs ⦄ InPlaceOrDisjointBuffer.impl.src (SharedBorrow.mk self)
      ⦃ (s, back) => ⌜s.val.val = vs ∧
        back = RawPtr.endShareRange (Pointee.repr (T := T)) self.src vs⌝ ∗
        self.src.range (depth + 1) vs ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.src
  step*

/-- `dst` borrows the cells of the destination range as a slice. -/
@[step]
theorem InPlaceOrDisjointBuffer.impl.dst.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (self : InPlaceOrDisjointBuffer T) (vs : List T) (h : self.len.val = vs.length)
    (h0 : 0 < vs.length) :
    ⦃ self.dst ↦* vs ⦄ InPlaceOrDisjointBuffer.impl.dst (MutBorrow.mk self)
      ⦃ (s, back, back'a) => ⌜s.val.val = vs ∧ (∀ s', back s' = (do
          core.slice.raw.from_raw_parts_mut.back (Pointee.repr (T := T)) self.dst self.len s'
          ok self)) ∧ ∀ b, back'a b = self⌝ ∗ self.dst ↦† vs.length ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.dst
  step*
  subst from_raw_parts_mut_back_post
  step
  rw [← h]
  iframe

/- The clients `zero_first_in_place`, `copy_first` and `increment_first_in_place` are not specified,
for lack of pointer specifications in `Aeneas.Std.RawPtrSpecs`:
- they write through the slice of `dst`, whose backward function `from_raw_parts_mut.back` (which
  gives the borrowed cells `p ↦† len` back as `p ↦* s.val`) has no specification;
- `copy_first` and `increment_first_in_place` read through the slice of `src`, which shares the
  exclusive range `b.src ↦* vs` (depth `0` to `1`); its backward function
  `RawPtr.endShareRange` is only specified from depth `depth + 1` to `depth` with `0 < depth`, so
  the share cannot be ended back to the exclusive range. -/

end in_place_or_disjoint_buffer
