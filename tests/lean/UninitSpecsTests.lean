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
  have hw := MutRawPtr.write.spec_uninit p [⟨none⟩, ⟨none⟩] 0 1#u8 (by simp)
  simp only [RawPtr.elem_zero] at hw
  step with hw
  have ha := RawPtr.add.spec_uninit p [⟨some 1#u8⟩, ⟨none⟩] 0 1#usize (by simp) (by simp)
  simp only [RawPtr.elem_zero] at ha
  step with ha
  subst q_post
  step with MutRawPtr.write.spec_uninit p [⟨some 1#u8⟩, ⟨none⟩] 1 2#u8 (by simp)
  step with RawPtr.sub.spec_uninit p [⟨some 1#u8⟩, ⟨some 2#u8⟩] 1 1#usize (by simp) (by simp) (by simp)
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
  have ha := RawPtr.add.spec_uninit p [⟨some v⟩, ⟨none⟩] 0 1#usize (by simp) (by simp)
  simp only [RawPtr.elem_zero] at ha
  step with ha
  subst q_post
  -- Split the buffer, call the function on the second half, and merge the halves back.
  refine ispec_realEntails_pre (uninitRange_split_real p [⟨some v⟩] [⟨none⟩]) ?_
  refine ispec_realEntails_post (Q' := fun _ => p ↦?* [⟨some v⟩] ∗
    (p.elem [⟨some v⟩].length) ↦?* [⟨some 7#u16⟩]) ?_
    (fun _ => uninitRange_merge p [⟨some v⟩] [⟨some 7#u16⟩])
  simp only [List.length_singleton, Nat.zero_add]
  step with write_second.spec (p.elem 1)

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
#print axioms write_second_of.spec
#print axioms MutRawPtr.write.spec_uninit
#print axioms RawPtr.read.spec_uninit
#print axioms RawPtr.offset.spec_uninit
#print axioms RawPtr.sub.spec_readable
#print axioms uninitRange_merge
#print axioms uninitRange_split_real
#print axioms readable_eq_uninitRange

end uninit_specs_tests
