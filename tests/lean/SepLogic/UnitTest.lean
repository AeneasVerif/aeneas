import SepLogic.Fixtures

/-! Unit tests of the separation-logic layer: entailments and the `i` tactics (`iframe`, `iintro`,
`irewrite`, `isimp`, `iwp =>`), the raw-pointer operations and the heap model (including the
adequacy tests: reading, writing or stepping over empty or freed memory, double free, freeing
memory that `into_raw` did not return), and `step` on `ispec`/`dispec` triples. -/

open Aeneas
open SepLogic
open Aeneas.SepLogic

namespace SepLogic

open Aeneas.Data.Coinductive

open Aeneas.Std.WP

open Aeneas.Std (Heap MutRawPtr RawPtr Result RustEffect)
open Aeneas.Std.MutRawPtr (write)
open Aeneas.Std.alloc.boxed.Box (into_raw from_raw)
open Aeneas.Std.RawPtr (read pointsTo_exclusive)

unseal Result

example : (Result.fail .panic : Result Nat) =
    Result.vis (RustEffect.Input.fail .panic) PEmpty.elim :=
  rfl

example (Q : Nat → Prop) :
    ¬ spec (Result.fail .panic : Result Nat) Q :=
  (spec_fail .panic).mp

example (Q : Nat → Prop) :
    ¬ dspec (Result.fail .panic : Result Nat) Q :=
  (dspec_fail .panic).mp

example (P Q : IProp) : emp ⊢ (P ∗ (P -∗ Q)) -∗ Q := by
  apply wand_intro
  irewrite (wand_cancel P Q)
  iframe

example (p q : MutRawPtr Nat) (x y : Nat) :
    p ↦ x ∗ q ↦ y ⊢ q ↦ y ∗ p ↦ x := by
  iframe

example (p : MutRawPtr Nat) (value : Nat) :
    p ↦ value ⊢ iprop(∃ w, ⌜w = value⌝ ∗ p ↦ w) := by
  iframe

example (p : MutRawPtr Nat) (value w : Nat) :
    iprop(⌜w = value + 1⌝ ∗ p ↦ value) ⊢ iprop(⌜0 < w⌝ ∗ p ↦ value) := by
  iframe

example (p : MutRawPtr Nat) :
    iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) ⊢ iprop(∃ m, p ↦ m) := by
  iframe

example (p q r : MutRawPtr Nat) (x y z : Nat) :
    iprop((p ↦ x ∗ q ↦ y) ∗ r ↦ z) ⊢ iprop(r ↦ z ∗ (q ↦ y ∗ p ↦ x)) := by
  iframe

example (p : MutRawPtr Nat) :
    p ↦ 3 ⊢ iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) := by
  iframe

example (p : MutRawPtr Nat) :
    ⦃ iprop(∃ n, ⌜n = 1⌝ ∗ p ↦ n) ⦄ Fixtures.incr_ptr p ⦃ p ↦ 2⦄ := by
  unfold Fixtures.incr_ptr
  fail_if_success
    step
    done
  fail_if_success iintro_shallow
  iwp => iintro_shallow
  step*
  subst_vars
  iframe

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ iprop(⌜value = 1⌝ ∗ p ↦ value) ⦄ Fixtures.incr_ptr p ⦃ p ↦ 2⦄ := by
  unfold Fixtures.incr_ptr
  iwp => iintro
  step*
  subst_vars
  iframe

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ iprop(p ↦ value ∗ ⌜value = 1⌝) ⦄ pure () ⦃ p ↦ value⦄ := by
  apply (ispec_ok _).mpr
  iintro_shallow
  guard_hyp h : value = 1
  iframe

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ iprop(p ↦ value ∗ ⌜value = 1⌝) ⦄ pure () ⦃ p ↦ value⦄div := by
  apply (dispec_ok _).mpr
  iintro_shallow
  guard_hyp h : value = 1
  iframe

example (p : MutRawPtr Nat) (value : Nat) (P F : Prop) :
    ⦃ iprop((p ↦ value ∗ ⌜P⌝) ∗ ⌜F⌝) ⦄ pure ()
      ⦃ iprop(p ↦ value ∗ ⌜F⌝)⦄ := by
  apply (ispec_ok _).mpr
  iintro_shallow_post
  guard_hyp h : P
  fail_if_success have : F := by assumption
  iframe

example (p q : MutRawPtr Nat) :
    ⦃ iprop(⌜q = p⌝ ∗ p ↦ 1) ⦄ Fixtures.incr_ptr q ⦃ iprop(⌜q = p⌝ ∗ p ↦ 2)⦄ := by
  unfold Fixtures.incr_ptr
  iwp => iintro_shallow
  subst_vars
  step*
  subst_vars
  iframe

example (p : MutRawPtr Nat) (n : Nat) :
    ⦃ iprop(⌜n = 1⌝ ∗ p ↦ n) ⦄ pure () ⦃ iprop(⌜n = 1⌝ ∗ p ↦ 1)⦄ := by
  apply (ispec_ok _).mpr
  iintro_keep
  guard_target = (iprop(⌜n = 1⌝ ∗ p ↦ n) ⊢ iprop(⌜n = 1⌝ ∗ p ↦ 1))
  iframe

example (n : Nat) :
    ⦃ emp ⦄ (Prod.rec (fun value _ => pure value) (n, true) : Result Nat)
      ⦃ result => ⌜result = n⌝⦄ := by
  step

def namedPure (n : Nat) : Result Nat :=
  pure n

@[step]
theorem namedPure.spec (n : Nat) :
    ⦃ emp ⦄ namedPure n ⦃ result => ⌜result = n⌝⦄ := by
  unfold namedPure
  step

example (n : Nat) :
    ⦃ emp ⦄ namedPure n ⦃ result => ⌜result = n⌝⦄ := by
  step

example (n : Nat) :
    True ∧ ⦃ emp ⦄ (pure n : Result Nat) ⦃ result => ⌜result = n⌝⦄ := by
  constructor
  fail_if_success all_goals step
  · trivial
  · step

def touchAny (p : MutRawPtr Nat) : Result Unit := do
  let value ← read p
  write p value

@[step]
theorem touchAny.spec (p : MutRawPtr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchAny p ⦃ iprop(∃ n, p ↦ n)⦄ := by
  unfold touchAny
  fail_if_success
    step*
    done
  iwp => iintro n
  step*

def touchThenSet (p : MutRawPtr Nat) : Result Unit := do
  touchAny p
  write p 7

example (p : MutRawPtr Nat) (x : Nat) :
    ⦃ iprop(⌜x = 5⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃ iprop(⌜x = 5⌝ ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step as ⟨ pulled ⟩
  guard_hyp pulled : Nat
  step*

example (p : MutRawPtr Nat) (x : Nat) :
    ⦃ iprop(⌜x = 5⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃ iprop(⌜x = 5⌝ ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step*

example (p q : MutRawPtr Nat) (x : Nat) :
    ⦃ iprop(iexists (fun n => q ↦ n) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃ iprop(iexists (fun n => q ↦ n) ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step*

example (p : MutRawPtr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchThenSet p ⦃ p ↦ 7⦄ := by
  unfold touchThenSet
  step*

example (p : MutRawPtr Nat) (x : Nat) : (p ↦ x ⊢ p ↦ x) ∧ 1 = 1 := by
  refine ⟨?_, ?_⟩
  · iframe
  · rfl

def readThenWrite (p : MutRawPtr Nat) : Result Unit := do
  let value ← read p
  write p (value + 1)

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readThenWrite p ⦃ p ↦ value + 1⦄ := by
  unfold readThenWrite
  step as ⟨actual, hActual⟩
  guard_hyp hActual : actual = value
  subst actual
  guard_target =
    ⦃ p ↦ value ⦄ write p (value + 1) ⦃ p ↦ value + 1⦄
  step*

def readAndFree (p : MutRawPtr Nat) : Result Nat := do
  let v ← read p
  let _ ← from_raw p
  pure (v + 1)

/-- `p.freeable` is required: without it, `p` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour in Rust (see `from_raw.spec`). -/
example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ∗ p.freeable ⦄ readAndFree p ⦃ result => ⌜result = value + 1⌝⦄ := by
  unfold readAndFree
  step*

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : MutRawPtr Nat) : Result Nat := do
  let value ← read p
  let _ ← from_raw p
  pure (value + 1)

/-- `p.freeable` is required: without it, `p` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour in Rust (see `from_raw.spec`). -/
example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ∗ p.freeable ⦄ readFreeReturn p
      ⦃ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  step*
  simp only [opaqueStepResult]
  agrind

/-- `p.freeable` is required: without it, `p` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour in Rust (see `from_raw.spec`). -/
example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ∗ p.freeable ⦄ readFreeReturn p
      ⦃ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  step* 2
  step
  simp only [opaqueStepResult]
  agrind

/-- `p.freeable` is required: without it, `p` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour in Rust (see `from_raw.spec`). -/
example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ∗ p.freeable ⦄ readFreeReturn p
      ⦃ result => ⌜result = value + 1⌝⦄ := by
  unfold readFreeReturn
  fail_if_success
    step*
    step
  step
  step
  step
  agrind

example (p : MutRawPtr Nat) (value : Nat) :
    p ↦ value ⊢ emp := by
  iframe

example (p q : MutRawPtr Nat) (left right : Nat) :
    p ↦ left ∗ q ↦ right ⊢ p ↦ left := by
  iframe

example (P : IProp) : P ⊢ ⌜8 = 8⌝ := by
  iframe

example (p q : MutRawPtr Nat) (left right : Nat) :
    p ↦ left ∗ q ↦ right ⊢ p ↦ left ∗ emp := by
  iframe

example (p : MutRawPtr Nat) (x y : Nat) :
    p ↦ x ∗ p ↦ y ⊢ ⌜False⌝ :=
  pointsTo_exclusive p x y

example (p q : MutRawPtr Nat) (x y : Nat) : p ↦ x ∗ q ↦ y ⊢ q ↦ y := by
  fail_if_success
    (have : p ↦ x ⊢ q ↦ y := by iframe)
  iframe

example (p : MutRawPtr Nat) (value : Nat) : ¬ (emp ⊢ p ↦ value) := by
  intro hImpl
  have hContains := RawPtr.contains_of_pointsTo (hImpl ∅ trivial)
  exact Heap.not_isValid_empty p hContains

example (p : MutRawPtr Nat) : ¬ (⦃ emp ⦄ read p ⦃ _ => emp⦄) := by
  intro hTriple
  rw [ispec_iff] at hTriple
  have hSpec := hTriple emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.RawPtr.read, Result.guardedModify] at hSpec
  obtain ⟨hContains, -⟩ := hSpec.vis_view
  exact Heap.not_isValid_empty p.cellPtr hContains.valid

example (p : MutRawPtr Nat) (value : Nat) : ¬ (⦃ emp ⦄ write p value ⦃ _ => emp⦄) := by
  intro hTriple
  rw [ispec_iff] at hTriple
  have hSpec := hTriple emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.MutRawPtr.write, Result.guardedModify] at hSpec
  obtain ⟨hContains, -⟩ := hSpec.vis_view
  exact Heap.not_isValid_empty p hContains

/-! Allocation ids are never reused: freed blocks stay in the heap. -/

-- The linter times out on the unreduced heaps in these hypotheses.
set_option linter.constructorNameAsVariable false in
/-- Use after free: the freed block stays dead, and the next allocation gets a new id. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let _ ← from_raw p
    let _ ← into_raw (2 : Nat)
    RawPtr.read p) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [into_raw, from_raw, Std.alloc.alloc.Global.allocate, RawPtr.alloc,
    Std.alloc.alloc.Global.deallocate,
    RawPtr.read,
    Result.guardedModify, Std.pure_tc_eq, Std.bind_tc_vis,
    Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hPre, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains', -⟩ := hSpec.vis_view
  simp only [] at hPre hContains'
  exact Heap.not_isLive_freeBlock hPre rfl
    ((Heap.isLive_allocBlock_of_mem (Heap.mem_freeBlock hPre)).mp (Heap.isLive_of_isValid hContains'.valid))

set_option linter.constructorNameAsVariable false in
/-- Double free, with an allocation in between that must not reuse the freed id. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let _ ← from_raw p
    let _ ← into_raw (2 : Nat)
    from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [into_raw, from_raw, Std.alloc.alloc.Global.allocate, RawPtr.alloc,
    Std.alloc.alloc.Global.deallocate,
    RawPtr.read,
    Result.guardedModify, Std.pure_tc_eq, Std.bind_tc_vis,
    Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hPre, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains', -⟩ := hSpec.vis_view
  simp only [] at hPre hContains'
  exact Heap.not_isLive_freeBlock hPre rfl
    ((Heap.isLive_allocBlock_of_mem (Heap.mem_freeBlock hPre)).mp (Heap.isLive_of_isValid hContains'.valid))

/-- A pointer into an empty slice does not alias the next allocation. -/
example : ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_ptr (Aeneas.Std.Slice.new Nat))
    fun (p, _) => do
      let _ ← into_raw (5 : Nat)
      RawPtr.read p) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.Slice.as_ptr, into_raw, Std.alloc.alloc.Global.allocate, RawPtr.alloc, RawPtr.read,
    RawPtr.allocView, Result.guardedModify, Std.bind_tc_eq, Std.bind_vis, Std.bind_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains, -⟩ := hSpec.vis_view
  exact Heap.not_isLive_allocBlock_of_le (h := ∅)
    (values := (Aeneas.Std.Slice.new Nat).val.map Std.Pointee.toCell) (i := 0)
    (by simp) ((Heap.isLive_allocBlock_of_mem (Heap.mem_allocBlock _ _)).mp
      (Heap.isLive_of_isValid hContains.valid))

/-- Freeing a pointer one past the end of a `Box`: `from_raw` needs the pointer that `into_raw`
returned, and moving the value out already reads past the end of the block. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let q ← p.add 1#usize
    let _ ← from_raw q
    pure ()) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [into_raw, from_raw, Std.alloc.alloc.Global.allocate, RawPtr.alloc, RawPtr.add, RawPtr.read,
    Result.guardedModify, Std.pure_tc_eq, Std.bind_tc_vis,
    Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains, -⟩ := hSpec.vis_view
  exact Heap.not_isLive_allocBlock_of_le (h := ∅) (values := [some (1 : Nat)]) (kind := .heap)
    (i := 1) (T := Nat) (M := .Mut) (by simp)
    ((Heap.isLive_congr (by simp) (by simp)).mp (Heap.isLive_of_isValid hContains.valid))

/-- Deallocating the tail of a two-cell allocation: the pointer is not the start of the
allocation. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← Std.alloc.alloc.Global.mk.allocate [(1 : Nat), 2]
    let q ← p.ptr.add 1#usize
    Std.alloc.alloc.Global.mk.deallocate ⟨q⟩ 1) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Std.alloc.alloc.Global.allocate, RawPtr.alloc, Std.alloc.alloc.Global.deallocate, RawPtr.add,
    Result.guardedModify, Std.bind_tc_vis, Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hPre, -⟩ := hSpec.vis_view
  simpa using Heap.offset_eq_zero_of_canDealloc hPre

/-- Freeing a pointer from `from_mut`: it only borrows its memory. -/
example : ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.core.ptr.from_mut (1 : Nat))
    fun (p, _) => from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.core.ptr.from_mut, from_raw, Std.alloc.alloc.Global.deallocate, RawPtr.read,
    RawPtr.allocView, RawPtr.alloc, Result.guardedModify, Std.pure_tc_eq, Std.bind_tc_eq, Std.bind_vis,
    Std.bind_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hPre, -⟩ := hSpec.vis_view
  simpa using ((Heap.canDealloc_allocBlock_iff _ _ _ _ _).mp hPre).1

/-- Freeing a pointer from `Slice.as_mut_ptr`: it only borrows its memory, even when it holds one
cell, like a `Box`. -/
example (s : Aeneas.Std.Slice Nat) (_hs : s.val = [1]) :
    ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_mut_ptr s)
      fun (p, _) => from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.Slice.as_mut_ptr, from_raw, Std.alloc.alloc.Global.deallocate, RawPtr.read,
    RawPtr.allocView, RawPtr.alloc, Result.guardedModify, Std.pure_tc_eq, Std.bind_tc_eq, Std.bind_vis,
    Std.bind_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hPre, -⟩ := hSpec.vis_view
  simpa using ((Heap.canDealloc_allocBlock_iff _ _ _ _ _).mp hPre).1

/-- Freeing an empty allocation: its block has no cell, so there is nothing to move out. -/
example : ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_mut_ptr (Aeneas.Std.Slice.new Nat))
    fun (p, _) => from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.Slice.as_mut_ptr, from_raw, RawPtr.read, RawPtr.allocView, RawPtr.alloc,
    Result.guardedModify, Std.pure_tc_eq, Std.bind_tc_eq, Std.bind_vis, Std.bind_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains, -⟩ := hSpec.vis_view
  exact Heap.not_isLive_allocBlock_of_le (h := ∅)
    (values := (Aeneas.Std.Slice.new Nat).val.map Std.Pointee.toCell) (i := 0)
    (by simp) (Heap.isLive_of_isValid hContains.valid)

/-- Freeing the start of a two-element slice: the block has two cells, not one. -/
example (s : Aeneas.Std.Slice Nat) (hs : s.val = [1, 2]) :
    ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_mut_ptr s)
      fun (p, _) => from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.Slice.as_mut_ptr, from_raw, Std.alloc.alloc.Global.deallocate, RawPtr.read,
    RawPtr.allocView, RawPtr.alloc, Result.guardedModify, Std.pure_tc_eq, Std.bind_tc_eq, Std.bind_vis,
    Std.bind_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hPre, -⟩ := hSpec.vis_view
  simpa [hs] using ((Heap.canDealloc_allocBlock_iff _ _ _ _ _).mp hPre).2

/-- Write after free. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let _ ← from_raw p
    write p 2) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [into_raw, from_raw, Std.alloc.alloc.Global.allocate, RawPtr.alloc,
    Std.alloc.alloc.Global.deallocate,
    RawPtr.read,
    Aeneas.Std.MutRawPtr.write, Result.guardedModify, Std.pure_tc_eq,
    Std.bind_tc_vis, Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hPre, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains, -⟩ := hSpec.vis_view
  exact Heap.not_isLive_freeBlock hPre rfl (Heap.isLive_of_isValid hContains)

/-- A non-zero `add` after free: the freed block cannot be stepped over. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let _ ← from_raw p
    p.add 1#usize) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [into_raw, from_raw, Std.alloc.alloc.Global.allocate, RawPtr.alloc,
    Std.alloc.alloc.Global.deallocate,
    RawPtr.read,
    RawPtr.add, Result.guardedModify, Std.pure_tc_eq, Std.bind_tc_vis,
    Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hPre, hSpec⟩ := hSpec.vis_view
  obtain ⟨hInBounds, -⟩ := hSpec.vis_view
  exact Heap.not_isLive_freeBlock hPre (by simp) (hInBounds 0 (by simp))

/-- Reading one past the end of a `Box`: the block has no cell there. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let q ← p.add 1#usize
    read q) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [into_raw, Std.alloc.alloc.Global.allocate, RawPtr.alloc, RawPtr.add, Aeneas.Std.RawPtr.read,
    Result.guardedModify, Std.bind_tc_vis, Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains, -⟩ := hSpec.vis_view
  exact Heap.not_isLive_allocBlock_of_le (h := ∅) (values := [some (1 : Nat)]) (kind := .heap)
    (i := 1) (T := Nat) (M := .Mut) (by simp)
    ((Heap.isLive_congr (by simp) (by simp)).mp (Heap.isLive_of_isValid hContains.valid))

/-- Writing one past the end of a `Box`: the block has no cell there. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let q ← p.add 1#usize
    write q 0) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [into_raw, Std.alloc.alloc.Global.allocate, RawPtr.alloc, RawPtr.add, Aeneas.Std.MutRawPtr.write,
    Result.guardedModify, Std.bind_tc_vis, Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains, -⟩ := hSpec.vis_view
  exact Heap.not_isLive_allocBlock_of_le (h := ∅) (values := [some (1 : Nat)]) (kind := .heap)
    (i := 1) (T := Nat) (M := .Mut) (by simp)
    ((Heap.isLive_congr (by simp) (by simp)).mp (Heap.isLive_of_isValid hContains))

/-- `write` takes a `MutRawPtr`: writing through a `ConstRawPtr` does not type-check. -/
example : True := by
  fail_if_success have := fun (p : Aeneas.Std.ConstRawPtr Nat) => write p 1
  trivial

/-- The right to free a `Box` cannot come from nothing. -/
example (p : MutRawPtr Nat) : ¬ (emp ⊢ p.freeable) := by
  intro hImpl
  obtain ⟨-, hSub⟩ := (RawPtr.freeable_holds p ∅).mp (hImpl ∅ trivial)
  obtain ⟨rest, -, hEmpty⟩ := Heap.subheap_iff.mp hSub
  apply Heap.notMem_empty p.allocId
  rw [hEmpty]
  exact Heap.mem_union.mpr (.inl (Heap.mem_header.mpr rfl))

def allocAndForget (value : Nat) : Result Unit := do
  let _ ← into_raw value
  pure ()

example (value : Nat) :
    ⦃ emp ⦄ allocAndForget value ⦃ emp⦄ := by
  unfold allocAndForget
  step*

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ (pure () : Result Unit) ⦃ emp⦄ := by
  step*

example (p : MutRawPtr Nat) :
    iprop(∃ n, ⌜0 < n⌝ ∗ p ↦ n) ⊢ iprop(∃ m, p ↦ (m + 1)) := by
  iintro
  rename_i x hx
  refine entails_exists_r (x - 1) ?_
  rw [show x - 1 + 1 = x by agrind]
  iframe

theorem cellPair (p q : MutRawPtr Nat) : iprop(p ↦ 1 ∗ q ↦ 2) ⊢ iprop(∃ n, p ↦ n ∗ q ↦ 2) :=
  entails_exists_r 1 (entails_refl _)

example (p q r : MutRawPtr Nat) :
    iprop(r ↦ 0 ∗ (p ↦ 1 ∗ q ↦ 2)) ⊢ iprop(∃ n, r ↦ 0 ∗ (p ↦ n ∗ q ↦ 2)) := by
  irewrite (cellPair p q)
  iframe

theorem swapEq (p q : MutRawPtr Nat) : iprop(p ↦ 1 ∗ q ↦ 2) = iprop(q ↦ 2 ∗ p ↦ 1) :=
  sep_comm_eq _ _

example (p q : MutRawPtr Nat) :
    ⦃ iprop((p ↦ 1 ∗ q ↦ 2) ∗ emp) ⦄ Fixtures.incr_ptr q ⦃ iprop(q ↦ 3 ∗ p ↦ 1)⦄ := by
  unfold Fixtures.incr_ptr
  iwp => irewrite (swapEq p q)
  step*
  subst_vars
  iframe

example (p : MutRawPtr Nat) : ⦃ p ↦ 1 ⦄ (pure 5 : Result Nat) ⦃ v => ⌜v = 5⌝ ∗ p ↦ 1⦄ := by
  step*

example (p q : MutRawPtr Nat) (x : Nat) :
    ⦃ iprop(p ↦ x ∗ q ↦ 9) ⦄ Fixtures.incr_ptr p ⦃ iprop(q ↦ 9 ∗ p ↦ (x + 1))⦄ := by
  step*


example (p q : MutRawPtr Nat) :
    ⦃ iprop(p ↦ 3 ∗ q ↦ 7) ⦄ read p ⦃ r => iprop(⌜r = 3⌝ ∗ (p ↦ 3 ∗ q ↦ 7))⦄ := by
  step with read.spec p 3

example (q : MutRawPtr Nat) :
    ⦃ iexists (fun n => iprop(q ↦ n)) ⦄ into_raw 5
      ⦃ r => iprop(r ↦ 5 ∗ iexists (fun n => iprop(q ↦ n)))⦄ := by
  step*

example (p q : MutRawPtr Nat) (x : Nat) :
    ⦃ iprop(iexists (fun n => iprop(q ↦ n)) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃ iprop(iexists (fun n => iprop(q ↦ n)) ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  apply Aeneas.Std.WP.ispec_bind (m := touchAny p) (touchAny.spec p)
  case hPre =>
    fail_if_success iintro
    iframe
  case hNext =>
    intro _
    iwp => iintro
    step*

example (Q₁ Q₂ : IPost Nat) (H : IProp) :
    iprop(H ∗ (Q₁ -∗+ Q₂)) ⊢ iprop(H ∗ (Q₁ -∗+ Q₂)) := by
  iframe

example (p q : MutRawPtr Nat) :
    (⦃ iprop(p ↦ 3 ∗ q ↦ 7) ⦄ read p ⦃ r => iprop(⌜r = 3⌝ ∗ (p ↦ 3 ∗ q ↦ 7))⦄)
    ∧ (iprop(p ↦ 3 ∗ q ↦ 7) ⊢ iprop(q ↦ 7 ∗ p ↦ 3)) := by
  refine ⟨?_, ?_⟩
  step with read.spec p 3
  guard_target = (iprop(p ↦ 3 ∗ q ↦ 7) ⊢ iprop(q ↦ 7 ∗ p ↦ 3))
  iframe

example (p : MutRawPtr Nat) (x : Nat) :
    ⦃ iprop(⌜x = 5⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃ iprop(⌜x = 5⌝ ∗ p ↦ 7)⦄ := by
  unfold touchThenSet
  step*

example (p : MutRawPtr Nat) :
    ⦃ iprop(∃ n, p ↦ n) ⦄ touchAny p ⦃ iprop(∃ n, p ↦ n)⦄ := by
  unfold touchAny
  iwp => iintro n
  step with read.spec p n
  step*

def readTwice (p : MutRawPtr Nat) : Result Nat := do
  let a ← read p
  let b ← read p
  pure (a + b)

@[step]
theorem readTwice.spec (p : MutRawPtr Nat) (n : Nat) (hn : 0 < n) :
    ⦃ p ↦ n ⦄ readTwice p ⦃ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  unfold readTwice
  step*

example (p : MutRawPtr Nat) : ⦃ p ↦ 3 ⦄ readTwice p ⦃ r => iprop(⌜0 < r⌝ ∗ p ↦ 3)⦄ := by
  step*

example (p : MutRawPtr Nat) (n : Nat) (b : Bool) (hb : b = true) (hguard : b = true → 0 < n) :
    ⦃ p ↦ n ⦄ readTwice p ⦃ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  step*

example (q : MutRawPtr Nat) (x y : Nat) :
    (q ↦* [x, y]) = iprop(q ↦ x ∗ (q.shift 1) ↦ y) :=
  by rw [RawPtr.pointsToRange_cons, ← RawPtr.pointsTo_eq_range]

example (q : MutRawPtr Nat) : (q ↦* ([] : List Nat)) = emp :=
  RawPtr.pointsToRange_nil q

example (q : MutRawPtr Nat) (x y : Nat) : q ↦ x ∗ q ↦ y ⊢ ⌜False⌝ :=
  pointsTo_exclusive q x y

example (q : MutRawPtr Nat) (x y : Nat) : q ↦ x ∗ (q.shift 1) ↦ y ⊢ q ↦* [x, y] :=
  entails_of_eq (by rw [RawPtr.pointsToRange_cons, ← RawPtr.pointsTo_eq_range])

/-- `as_mut_ptr` returns a `Result` in `Type 1` (its back computation), hence the explicit
universe-heterogeneous `Std.bind` (the extracted code gets it from the Aeneas `do` elaborator). -/
def slicePtrWrite (s : Aeneas.Std.Slice Nat) : Result (Nat × Aeneas.Std.Slice Nat) :=
  Aeneas.Std.bind s.as_mut_ptr fun (p, back) => do
    let q ← p.add 1#usize
    write q 42
    let value ← read q
    let s ← back
    pure (value, s)

/-- The write through the pointer is seen in the slice given back when the borrow ends. -/
theorem slicePtrWrite.spec (s : Aeneas.Std.Slice Nat) (h : 1 < s.length) :
    ⦃ emp ⦄ slicePtrWrite s ⦃ (value, s') => ⌜value = 42 ∧ s'.val = s.val.set 1 42⌝⦄ := by
  unfold slicePtrWrite
  step as ⟨r, hr⟩
  obtain ⟨p, back⟩ := r
  simp only at hr
  subst hr
  step* 1
  subst_vars
  step with MutRawPtr.write.spec_range p s.val 1 42 (by simpa using h)
  step with RawPtr.read.spec_range p (s.val.set 1 42) 1 (by simpa using h)
  step*
  exact ⟨by simp [value_post], s_post⟩

/-! `add` stays within the allocation, up to one past its end. -/

example : ⦃ emp ⦄ (do
    let p ← RawPtr.allocView [1, 2]
    p.add 2#usize) ⦃ _ => ⌜True⌝ ⦄ := by
  step*

/-- Two past the end of a one-cell allocation: `add` steps past the end of its block. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (5 : Nat)
    p.add 2#usize) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [into_raw, Std.alloc.alloc.Global.allocate, RawPtr.alloc, RawPtr.add,
    Result.guardedModify, Std.bind_tc_vis, Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hInBounds, -⟩ := hSpec.vis_view
  exact Heap.not_isLive_allocBlock_of_le (h := ∅) (values := [some (5 : Nat)]) (kind := .heap)
    (i := 1) (T := Nat) (M := .Mut) (by simp)
    ((Heap.isLive_congr (by simp) (by simp)).mp (hInBounds 1 (by simp)))

/-- `add 0` is allowed on any pointer, including into an empty allocation. -/
example : ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_ptr (Aeneas.Std.Slice.new Nat))
    fun (p, _) => p.add 0#usize) ⦃ _ => ⌜True⌝ ⦄ := by
  step*

/-- A non-zero `add` into an empty allocation steps past the end of its block. -/
example : ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_ptr (Aeneas.Std.Slice.new Nat))
    fun (p, _) => p.add 1#usize) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.Slice.as_ptr, RawPtr.add, RawPtr.allocView, RawPtr.alloc, Result.guardedModify,
    Std.bind_vis, Std.bind_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hInBounds, -⟩ := hSpec.vis_view
  exact Heap.not_isLive_allocBlock_of_le (h := ∅)
    (values := (Aeneas.Std.Slice.new Nat).val.map Std.Pointee.toCell) (i := 0)
    (by simp) (by convert hInBounds 0 (by simp) using 2 <;> simp)

end SepLogic
