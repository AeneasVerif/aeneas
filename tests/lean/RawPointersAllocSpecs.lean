import RawPointersAlloc

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace raw_pointers_alloc

theorem box_init.spec : ⦃ emp ⦄ box_init ⦃ r => ⌜r = 5#u32⌝ ⦄ := by
  unfold box_init
  step*
  subst_vars
  step*

theorem box_new_uninit.spec : ⦃ emp ⦄ box_new_uninit ⦃ r => ⌜r = 6#u32⌝ ⦄ := by
  unfold box_new_uninit
  step*
  subst_vars
  step*

theorem box_read_write.spec : ⦃ emp ⦄ box_read_write ⦃ r => ⌜r = 2#u32⌝ ⦄ := by
  unfold box_read_write
  step*

/-- Reading an uninitialized box fails. -/
theorem box_read_uninit.fails (Q : IPost U32) : ¬ ispec emp (box_read_uninit) Q := by
  apply not_ispec_of_ifails_emp
  unfold box_read_uninit
  simp only [alloc.boxed.Box.new_uninit, Std.bind_ok]
  refine ifails_bind (alloc.boxed.Box.into_raw.spec _) fun p => ?_
  exact ifails_mono (by iframe) (MaybeUninit.read_cast.fails p)

/-- Assigning through a raw pointer to an uninitialized box fails: the old value is dropped. -/
theorem assign_uninit_box.fails (Q : IPost U32) : ¬ ispec emp assign_uninit_box Q := by
  apply not_ispec_of_ifails_emp
  unfold assign_uninit_box
  simp only [core.mem.maybe_uninit.MaybeUninit.uninit, Std.bind_ok]
  refine ifails_bind (alloc.boxed.Box.into_raw.spec _) fun p => ?_
  exact ifails_bind_left (ifails_mono (by iframe) (MaybeUninit.read_cast.fails p))

/-- `ptr::write` initializes the box without dropping its old value. -/
theorem write_uninit_box.spec : ⦃ emp ⦄ write_uninit_box ⦃ r => ⌜r = 1#u32⌝ ⦄ := by
  unfold write_uninit_box
  step*

/-- Freeing twice fails. -/
theorem double_free.fails (Q : IPost Unit) : ¬ ispec emp (double_free) Q := by
  apply not_ispec_of_ifails_emp
  unfold double_free
  refine ifails_bind (alloc.boxed.Box.into_raw.spec _) fun p => ifails_ipure fun hAlign => ?_
  refine ifails_bind (alloc.boxed.Box.from_raw.spec_freed p hAlign) fun _ => ?_
  exact ifails_bind_left (ifails_mono (by iframe) (alloc.boxed.Box.from_raw.fails_freed p (by simp)))

/-- Using a freed pointer fails. -/
theorem use_after_free.fails (Q : IPost U32) : ¬ ispec emp (use_after_free) Q := by
  apply not_ispec_of_ifails_emp
  unfold use_after_free
  refine ifails_bind (alloc.boxed.Box.into_raw.spec _) fun p => ifails_ipure fun hAlign => ?_
  refine ifails_bind (alloc.boxed.Box.from_raw.spec_freed p hAlign) fun _ => ?_
  exact ifails_mono (by iframe) (RawPtr.read.fails_freed p (by simp))

/-- Freeing an interior pointer fails. -/
theorem free_interior.fails (Q : IPost Unit) : ¬ ispec emp (free_interior) Q := by
  apply not_ispec_of_ifails_emp
  unfold free_interior
  refine ifails_bind (alloc.boxed.Box.into_raw.spec _) fun p => ifails_ipure fun _ => ?_
  have hAdd := ispec_frame (RawPtr.add.spec p [1#u32] 1#usize (by simp)) p.freeable
  rw [← RawPtr.pointsTo_eq_range] at hAdd
  refine ifails_bind hAdd fun q => ?_
  refine ifails_mono (P' := iprop(⌜q = p.shift 1⌝ ∗ p.freeable)) (by iframe) (ifails_ipure ?_)
  rintro rfl
  exact ifails_bind_left (alloc.boxed.Box.from_raw.fails_end p (by simp))

/-- Freeing a pointer which does not come from a box fails. -/
theorem free_borrowed.fails (x : U32) (Q : IPost U32) : ¬ ispec emp (free_borrowed x) Q := by
  apply not_ispec_of_ifails_emp
  unfold free_borrowed
  refine ifails_bind (core.ptr.from_mut.spec x) fun ⟨p, back⟩ => ?_
  simp only [Std.uncurry]
  refine ifails_mono (P' := iprop(⌜back = core.ptr.end_from_mut p⌝ ∗ p ↦ x ∗ p.freeable 1 .view))
    (by iframe) (ifails_ipure fun _ => ?_)
  exact ifails_bind_left (alloc.boxed.Box.from_raw.fails_view p)

end raw_pointers_alloc
