import MaybeUninit

open Aeneas
open Aeneas.SepLogic
open Aeneas.Std
open Aeneas.Std.WP
open maybe_uninit

namespace SepLogic.ExtractedMaybeUninit

theorem write_two.spec (p q : MutRawPtr U64) (a b : Std.MaybeUninit U64) :
    ⦃ p ↦? a ∗ q ↦? b ⦄ write_two p q ⦃⇓ p ↦ 1#u64 ∗ q ↦ 2#u64⦄ := by
  unfold write_two
  apply WP.ispec_bind (WP.ispec_frame (MutRawPtr.write.spec_uninit p a 1#u64) (q ↦? b))
    (sep_emp_r _).mpr
  intro _
  rw [sep_emp_r_eq]
  exact WP.ispec_frame_left (MutRawPtr.write.spec_uninit q b 2#u64) (p ↦ 1#u64)

theorem init_through_ptrs.spec :
    ⦃ emp ⦄ init_through_ptrs ⦃⇓ r => ⌜r = 3#u64⌝⦄ := by
  unfold init_through_ptrs
  simp only [core.mem.maybe_uninit.MaybeUninit.uninit]
  step as ⟨p⟩
  step as ⟨q⟩
  step with write_two.spec p q .uninit .uninit
  step with Std.MaybeUninit.end_as_mut_ptr.spec_init .uninit p 1#u64 (by decide)
  subst a1_post
  simp only [Std.MaybeUninit.assume_init_init]
  step with Std.MaybeUninit.end_as_mut_ptr.spec_init .uninit q 2#u64 (by decide) as ⟨b, hb⟩
  subst hb
  simp only [Std.MaybeUninit.assume_init_init]
  step*

theorem read_uninit_eq : read_uninit = Result.fail .undef := by
  simp [read_uninit, core.mem.maybe_uninit.MaybeUninit.uninit]

end SepLogic.ExtractedMaybeUninit
