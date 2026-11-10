import Aeneas

/-! Regression tests for the specifications of possibly uninitialized ranges (`p ↦?* values`,
`Aeneas/Std/UninitSpecs.lean`), on small programs written directly in Lean. -/

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result core.mem.maybe_uninit

namespace uninit_specs_tests

/-- Writes two bytes into a buffer, moves back with `sub` and reads the first one. -/
def write_two (p : MutRawPtr U8) : Result U8 := do
  MutRawPtr.write p 1#u8
  let q ← RawPtr.add p 1#usize
  MutRawPtr.write q 2#u8
  let r ← RawPtr.sub q 1#usize
  RawPtr.read r

theorem write_two.spec (p : MutRawPtr U8) :
    ⦃ p ↦?* [⟨none⟩, ⟨none⟩] ⦄ write_two p
      ⦃ r => ⌜r = 1#u8⌝ ∗ p ↦?* [⟨some 1#u8⟩, ⟨some 2#u8⟩] ⦄ := by
  unfold write_two
  -- at the start of the range (`MutRawPtr.write.spec_uninit_head`, `RawPtr.add.spec_uninit_head`,
  -- not `@[step]`: same programs as `MutRawPtr.write.spec` and `RawPtr.add.spec`)
  step with MutRawPtr.write.spec_uninit_head p [⟨none⟩, ⟨none⟩] 1#u8 (by simp)
  step with RawPtr.add.spec_uninit_head p [⟨some 1#u8⟩, ⟨none⟩] 1#usize (by simp) (by simp)
  subst q_post
  step
  step
  subst r_post
  step with RawPtr.read.spec_uninit p [⟨some 1#u8⟩, ⟨some 2#u8⟩] (1 - 1) 1#u8 (by simp) rfl

/-- `step` finds the specifications by itself (`@[step]`). -/
def write_at (p : MutRawPtr U8) : Result (RawPtr U8) := do
  MutRawPtr.write (p.elem 1) 5#u8
  let q ← RawPtr.ptr_cast U8 p
  RawPtr.add (q.elem 1) 1#usize

theorem write_at.spec (p : MutRawPtr U8) :
    ⦃ p ↦?* [⟨none⟩, ⟨none⟩] ⦄ write_at p
      ⦃ r => ⌜r = p.elem 2⌝ ∗ p ↦?* [⟨none⟩, ⟨some 5#u8⟩] ⦄ := by
  unfold write_at
  step
  step
  subst q_post
  simp only [RawPtr.cast_self]
  step*

/-- Writes the second element of a buffer, through a pointer to it. -/
def write_second (q : MutRawPtr U16) : Result Unit :=
  MutRawPtr.write q 7#u16

theorem write_second.spec (q : MutRawPtr U16) :
    ⦃ q ↦?* [⟨none⟩] ⦄ write_second q ⦃ q ↦?* [⟨some 7#u16⟩] ⦄ := by
  unfold write_second
  simpa using MutRawPtr.write.spec_uninit q [⟨none⟩] 0 7#u16 (by simp)

/-- The caller splits its buffer, lets `write_second` initialize the second half, and merges the
halves back. -/
def write_second_of (p : MutRawPtr U16) : Result Unit := do
  let q ← RawPtr.add p 1#usize
  write_second q

theorem write_second_of.spec (p : MutRawPtr U16) (v : U16) :
    ⦃ p ↦?* [⟨some v⟩, ⟨none⟩] ⦄ write_second_of p
      ⦃ p ↦?* [⟨some v⟩, ⟨some 7#u16⟩] ⦄ := by
  unfold write_second_of
  step with RawPtr.add.spec_uninit_head p [⟨some v⟩, ⟨none⟩] 1#usize (by simp) (by simp)
  subst q_post
  -- Split the buffer, call the function on the second half, and merge the halves back.
  refine ispec_realEntails_pre (uninitRange_split_real p [⟨some v⟩] [⟨none⟩]) ?_
  refine ispec_realEntails_post (Q' := fun _ => p ↦?* [⟨some v⟩] ∗
    (p.elem [⟨some v⟩].length) ↦?* [⟨some 7#u16⟩]) ?_
    (fun _ => uninitRange_merge p [⟨some v⟩] [⟨some 7#u16⟩])
  simp only [List.length_singleton]
  step with write_second.spec (p.elem 1)

/-! ## `step` at the start of a range, and between same-shape specifications -/

/-- The `_head` specifications (`*p = v`, `p.add(k)`, `p.offset(k)`, `*p`), next to the ones of
`p ↦ v` (`MutRawPtr.write.spec`). `step` doesn't backtrack: the `_head` specifications whose programs
have the same shape as other `@[step]` specifications are used with `step with`;
`RawPtr.offset.spec_uninit_head` is `@[step]`. -/
example (p : MutRawPtr U8) (q : MutRawPtr U32) :
    ⦃ p ↦?* [⟨none⟩, ⟨none⟩] ∗ q ↦ 0#u32 ⦄
      (do MutRawPtr.write p 3#u8
          MutRawPtr.write q 1#u32
          let r ← RawPtr.offset p 1#isize
          MutRawPtr.write r 4#u8
          RawPtr.read p)
    ⦃ x => ⌜x = 3#u8⌝ ∗ p ↦?* [⟨some 3#u8⟩, ⟨some 4#u8⟩] ∗ q ↦ 1#u32 ⦄ := by
  step with MutRawPtr.write.spec_uninit_head p [⟨none⟩, ⟨none⟩] 3#u8 (by simp)
  step
  step
  subst r_post
  step
  step with RawPtr.read.spec_uninit_head p [⟨some 3#u8⟩, ⟨some 4#u8⟩] 3#u8 (by simp) (by simp)

/-- Pointer arithmetic in a readable range, from its start (as on the result of `as_ptr`). -/
example (p : ConstRawPtr U16) (a b c : U16) :
    ⦃ p.readable 1 [a, b, c] ⦄
      (do let q ← RawPtr.offset p 2#isize
          let r ← RawPtr.sub q 1#usize
          RawPtr.read r)
    ⦃ x => ⌜x = b⌝ ∗ p.readable 1 [a, b, c] ⦄ := by
  step with RawPtr.offset.spec_readable_head p 1 [a, b, c] 2#isize (by simp) (by simp) (by simp)
  subst q_post
  step with RawPtr.sub.spec_readable p 1 [a, b, c] 2 1#usize (by simp) (by simp) (by simp)
  subst r_post
  -- `RawPtr.read.spec_uninit` has the same program, and is tried first
  step with RawPtr.read.spec_readable p 1 [a, b, c] (2 - 1) (by simp)

/-! ## `RealEntails` with pure facts and existentials -/

example (p : MutRawPtr U8) (v : U8) :
    RealEntails iprop(⌜True⌝ ∗ iprop(∃ n : Nat, ⌜n = 1⌝ ∗ p ↦?* [⟨some v⟩] ∗ (p.elem n) ↦?* [⟨none⟩]))
      iprop(∃ u : U8, p ↦?* [⟨some u⟩, ⟨none⟩]) := by
  refine RealEntails.pure_l fun _ => RealEntails.exists_l fun n => RealEntails.pure_l fun hn => ?_
  subst hn
  exact RealEntails.exists_r v (uninitRange_merge p [⟨some v⟩] [⟨none⟩])

example (p : MutRawPtr U8) (v : U8) :
    RealEntails (p ↦?* [⟨some v⟩] ∗ (p.elem 1) ↦?* [⟨none⟩]) (p ↦?* [⟨none⟩, ⟨none⟩]) :=
  (uninitRange_merge p [⟨some v⟩] [⟨none⟩]).trans_entails (uninitRange_forget p _)

/-- The value read back from a `MaybeUninit` out-parameter. -/
example (r : MaybeUninit U32) (v : U32) (h : MaybeUninit.Refines [r] [⟨some v⟩]) :
    r = ⟨some v⟩ := by
  simpa using h

/-- A long `if` cascade, split without `simp`. -/
example (c d : Bool) (P : IProp) :
    ⦃ P ⦄ (if c then ok 1#u8 else if d then ok 2#u8 else ok 3#u8) ⦃ _ => P ⦄ := by
  repeat' (apply ispec_ite <;> intro)
  all_goals exact ispec_ok _ (entails_refl _)

/-- A full range is a range of initialized values, and a buffer can be forgotten. -/
example (p : RawPtr U8) (a b : U8) :
    p ↦* [a, b] ⊢ p ↦?* [⟨none⟩, ⟨none⟩] :=
  entails_trans (range_uninitRange p [a, b]) (uninitRange_forget p [⟨some a⟩, ⟨some b⟩])

example (p : RawPtr U8) (vs : List U8) :
    p.readable 0 vs = (p ↦?* vs.map (fun v => ⟨some v⟩)) :=
  readable_eq_uninitRange p vs

example (p : RawPtr U32) (i j : Nat) : (p.elem i).elem j = p.elem (i + j) :=
  RawPtr.elem_elem p i j

#print axioms write_two.spec
#print axioms MutRawPtr.write.spec_uninit_head
#print axioms RawPtr.offset.spec_readable_head
#print axioms RealEntails.pure_l
#print axioms write_second_of.spec
#print axioms MutRawPtr.write.spec_uninit
#print axioms RawPtr.read.spec_uninit
#print axioms RawPtr.offset.spec_uninit
#print axioms RawPtr.sub.spec_readable
#print axioms uninitRange_merge
#print axioms uninitRange_split_real
#print axioms readable_eq_uninitRange

end uninit_specs_tests
