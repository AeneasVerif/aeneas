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

open Aeneas.Std (Heap MutRawPtr Pointee RawPtr Result RustEffect)
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
  pointsTo_exclusive p x y (by simp)

example (p q : MutRawPtr Nat) (x y : Nat) : p ↦ x ∗ q ↦ y ⊢ q ↦ y := by
  fail_if_success
    (have : p ↦ x ⊢ q ↦ y := by iframe)
  iframe

example (p : MutRawPtr Nat) (value : Nat) : ¬ (emp ⊢ p ↦ value) := by
  intro hImpl
  exact Heap.not_isValid_empty _ (RawPtr.isValid_of_pointsTo (hImpl ∅ trivial) (by simp))

example (p : MutRawPtr Nat) : ¬ (⦃ emp ⦄ read p ⦃ _ => emp⦄) := by
  intro hTriple
  rw [ispec_iff] at hTriple
  have hSpec := hTriple emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.RawPtr.read, RawPtr.read_unaligned, RawPtr.load, Std.Result.require,
    Std.HeapOp.reads, Std.HeapOp.read, Pointee.size_default, Result.guardedModify,
    Std.bind_tc_vis, Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hValid, -⟩ := hSpec.vis_view
  exact Heap.not_isValid_empty _ hValid

example (p : MutRawPtr Nat) (value : Nat) : ¬ (⦃ emp ⦄ write p value ⦃ _ => emp⦄) := by
  intro hTriple
  rw [ispec_iff] at hTriple
  have hSpec := hTriple emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.MutRawPtr.write, Std.MutRawPtr.write_unaligned, Std.Result.require,
    Std.HeapOp.writes, Std.HeapOp.write, Pointee.toCells_default, Result.guardedModify,
    Std.bind_tc_vis, Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hValid, -⟩ := hSpec.vis_view
  exact Heap.not_isValid_empty _ hValid

/-! Allocation ids are never reused: freed slots and end markers stay in the heap as dead slots. -/

/-- The slot of a freed pointer is not live in any heap containing it. -/
theorem freed_not_isLive {T : Type} [Pointee T] {M : Std.Mutability} (q : RawPtr T M) :
    ∀ h, q.freed h → ∀ h', Heap.Subheap h h' → ¬ Heap.IsLive h' q.loc :=
  fun _ hFreed _ hSub => Heap.not_isLive_of_isFreed (Heap.Subheap.isFreed (hFreed.trans hSub))

/-- The end marker of a freeable allocation is not live in any heap containing it. -/
theorem freeable_not_isLive {T : Type} [Pointee T] {M : Std.Mutability} (q : RawPtr T M)
    (count : Nat) (kind : Std.AllocKind) :
    ∀ h, q.freeable count kind h → ∀ h', Heap.Subheap h h' →
      ¬ Heap.IsLive h' (q.loc.shift (count * Pointee.size T)) :=
  fun _ hFreeable _ hSub =>
    Heap.not_isLive_of_isEndMarker (Heap.Subheap.isEndMarker (hFreeable.2.trans hSub))

/-- Writing a `Nat` fails if its slot is not live. -/
theorem write_fails {P : IPre} (q : MutRawPtr Nat) (value : Nat)
    (hNot : ∀ h, P h → ∀ h', Heap.Subheap h h' → ¬ Heap.IsLive h' q.loc) :
    ifails P (write q value) := by
  unfold Std.MutRawPtr.write Std.MutRawPtr.write_unaligned
  refine Std.ifails_require_bind (Std.ifails_require_bind ?_)
  simp only [Pointee.toCells_default, Std.HeapOp.writes]
  exact ifails_bind_left (ifails_guardedModify fun h hP h' hSub hValid =>
    hNot h hP h' hSub (by have := Heap.isLive_of_isValid hValid; exact this))

/-- `add count` fails if one of the `count` slots it steps over is not live. -/
theorem add_fails {P : IPre} {M : Std.Mutability} (q : RawPtr Nat M) (count : Std.Usize) (i : Nat)
    (hi : i < count.val)
    (hNot : ∀ h, P h → ∀ h', Heap.Subheap h h' → ¬ Heap.IsLive h' (q.loc.shift i)) :
    ifails P (q.add count) :=
  ifails_guardedModify fun h hP h' hSub hIn =>
    hNot h hP h' hSub (Heap.isLive_of_isValid (hIn i (by simpa using hi)))

/-- Use after free: the freed slot stays dead, and the next allocation gets a new id. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let _ ← from_raw p
    let _ ← into_raw (2 : Nat)
    RawPtr.read p) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (into_raw.spec _) fun p => ifails_ipure fun hAlign => ?_
  refine ifails_bind (Std.alloc.boxed.Box.from_raw.spec_freed p hAlign) fun _ =>
    ifails_ipure fun _ => ?_
  refine ifails_mono (entails_of_eq (sep_emp_r_eq _).symm)
    (ifails_bind (ispec_frame_left (into_raw.spec 2) _) fun _ => ?_)
  exact ifails_mono (by iframe) (RawPtr.read.fails_freed p (by simp))

/-- Double free, with an allocation in between that must not reuse the freed id. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let _ ← from_raw p
    let _ ← into_raw (2 : Nat)
    from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (into_raw.spec _) fun p => ifails_ipure fun hAlign => ?_
  refine ifails_bind (Std.alloc.boxed.Box.from_raw.spec_freed p hAlign) fun _ =>
    ifails_ipure fun _ => ?_
  refine ifails_mono (entails_of_eq (sep_emp_r_eq _).symm)
    (ifails_bind (ispec_frame_left (into_raw.spec 2) _) fun _ => ?_)
  exact ifails_mono (by iframe) (Std.alloc.boxed.Box.from_raw.fails_freed p (by simp))

/-- A pointer into an empty slice does not alias the next allocation. -/
example : ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_ptr (Aeneas.Std.Slice.new Nat))
    fun (p, _) => do
      let _ ← into_raw (5 : Nat)
      RawPtr.read p) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (Std.Slice.as_ptr.spec _) fun (p, _) => ifails_ipure fun _ =>
    ifails_ipure fun _ => ?_
  refine ifails_mono (entails_of_eq (sep_emp_r_eq _).symm)
    (ifails_bind (ispec_frame_left (into_raw.spec 5) _) fun _ => ?_)
  have hEnd := RawPtr.read.fails_end p 0 .view (by simp)
  rw [RawPtr.shift_zero] at hEnd
  exact ifails_mono (by simp [Std.Slice.new]; iframe) hEnd

/-- Freeing a pointer one past the end of a `Box`: `from_raw` needs the pointer that `into_raw`
returned, and moving the value out already reads the dead end marker. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let q ← p.add 1#usize
    let _ ← from_raw q
    pure ()) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (into_raw.spec _) fun p => ifails_ipure fun _ => ?_
  rw [RawPtr.pointsTo_eq_range]
  refine ifails_bind (ispec_frame (RawPtr.add.spec p [1] 1#usize (by simp)) _) fun q => ?_
  refine ifails_mono (entails_of_eq (sep_assoc_eq _ _ _)) (ifails_ipure fun hq => ?_)
  subst hq
  exact ifails_bind_left
    (ifails_mono (by iframe) (Std.alloc.boxed.Box.from_raw.fails_end p (by simp)))

/-- Deallocating the tail of a two-slot allocation: the size and end marker match, but the pointer
is not the start of the allocation. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← Std.Global.mk.allocate [(1 : Nat), 2]
    let q ← p.ptr.add 1#usize
    Std.Global.mk.deallocate ⟨q⟩ 1) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (Std.Global.allocate.spec _ _) fun p => ifails_ipure fun _ => ?_
  refine ifails_bind (ispec_frame (RawPtr.add.spec p.ptr [1, 2] 1#usize (by simp)) _) fun q => ?_
  refine ifails_mono (entails_of_eq (sep_assoc_eq _ _ _)) (ifails_ipure fun hq => ?_)
  subst hq
  refine ifails_mono (by iframe)
    (ifails_guardedModify (P := p.ptr.freeable 2) fun _ hP _ _ hDealloc => ?_)
  simpa [hP.1] using (Heap.canDealloc_iff.mp hDealloc).1

/-- Freeing a pointer from `from_mut`: it only borrows its memory. -/
example : ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.core.ptr.from_mut (1 : Nat))
    fun (p, _) => from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (Std.core.ptr.from_mut.spec _) fun (p, _) => ifails_ipure fun _ =>
    ifails_ipure fun _ => ?_
  exact Std.alloc.boxed.Box.from_raw.fails_view p

/-- Freeing a pointer from `Slice.as_mut_ptr`: it only borrows its memory, even when it holds one
slot, like a `Box`. -/
example (s : Aeneas.Std.Slice Nat) (hs : s.val = [1]) :
    ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_mut_ptr s)
      fun (p, _) => from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (Std.Slice.as_mut_ptr.spec _) fun (p, _) => ifails_ipure fun _ =>
    ifails_ipure fun _ => ?_
  rw [hs, Std.Slice.length, hs, ← RawPtr.pointsTo_eq_range]
  exact Std.alloc.boxed.Box.from_raw.fails_view p

/-- Freeing an empty allocation: its only slot is the dead end marker, so there is nothing to move
out. -/
example : ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_mut_ptr (Aeneas.Std.Slice.new Nat))
    fun (p, _) => from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (Std.Slice.as_mut_ptr.spec _) fun (p, _) => ifails_ipure fun _ =>
    ifails_ipure fun _ => ?_
  have hEnd := RawPtr.read.fails_end p 0 .view (by simp)
  rw [RawPtr.shift_zero] at hEnd
  unfold from_raw
  exact ifails_bind_left (ifails_mono (by simp [Std.Slice.new]; iframe) hEnd)

/-- Freeing the start of a two-element slice: the slot after it is not an end marker. -/
example (s : Aeneas.Std.Slice Nat) (hs : s.val = [1, 2]) :
    ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_mut_ptr s)
      fun (p, _) => from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (Std.Slice.as_mut_ptr.spec _) fun (p, _) => ifails_ipure fun _ =>
    ifails_ipure fun hAlign => ?_
  rw [hs, RawPtr.pointsToRange_cons, ← RawPtr.pointsTo_eq_range]
  dsimp only
  unfold from_raw
  refine ifails_mono (entails_of_eq (sep_assoc_eq _ _ _))
    (ifails_bind (ispec_frame (read.spec p 1 hAlign) _) fun _ => ?_)
  refine ifails_bind_left (ifails_mono (by iframe)
    (ifails_guardedModify (P := (p.shift 1) ↦ (2 : Nat)) fun _ hP _ hSub hDealloc => ?_))
  have hLive := Heap.isLive_of_isValid
    (Heap.Subheap.isValid hSub (RawPtr.isValid_of_pointsTo hP (by simp)))
  exact Heap.not_isLive_of_isEndMarker (Heap.canDealloc_iff.mp hDealloc).2.2 (by simpa using hLive)

/-- Write after free. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let _ ← from_raw p
    write p 2) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (into_raw.spec _) fun p => ifails_ipure fun hAlign => ?_
  refine ifails_bind (Std.alloc.boxed.Box.from_raw.spec_freed p hAlign) fun _ =>
    ifails_ipure fun _ => ?_
  exact write_fails p 2 (freed_not_isLive p)

/-- A non-zero `add` after free: the freed slot cannot be stepped over. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let _ ← from_raw p
    p.add 1#usize) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (into_raw.spec _) fun p => ifails_ipure fun hAlign => ?_
  refine ifails_bind (Std.alloc.boxed.Box.from_raw.spec_freed p hAlign) fun _ =>
    ifails_ipure fun _ => ?_
  exact add_fails p 1#usize 0 (by simp) (by simpa using freed_not_isLive p)

/-- Reading one past the end of a `Box`: the slot is its dead end marker. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let q ← p.add 1#usize
    read q) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (into_raw.spec _) fun p => ifails_ipure fun _ => ?_
  rw [RawPtr.pointsTo_eq_range]
  refine ifails_bind (ispec_frame (RawPtr.add.spec p [1] 1#usize (by simp)) _) fun q => ?_
  refine ifails_mono (entails_of_eq (sep_assoc_eq _ _ _)) (ifails_ipure fun hq => ?_)
  subst hq
  exact ifails_mono (by iframe) (RawPtr.read.fails_end p 1 .global (by simp))

/-- Writing one past the end of a `Box`: the slot is its dead end marker. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let q ← p.add 1#usize
    write q 0) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (into_raw.spec _) fun p => ifails_ipure fun _ => ?_
  rw [RawPtr.pointsTo_eq_range]
  refine ifails_bind (ispec_frame (RawPtr.add.spec p [1] 1#usize (by simp)) _) fun q => ?_
  refine ifails_mono (entails_of_eq (sep_assoc_eq _ _ _)) (ifails_ipure fun hq => ?_)
  subst hq
  exact ifails_mono (by iframe)
    (write_fails (P := p.freeable) _ 0 (by simpa using freeable_not_isLive p 1 .global))

/-- `write` takes a `MutRawPtr`: writing through a `ConstRawPtr` does not type-check. -/
example : True := by
  fail_if_success have := fun (p : Aeneas.Std.ConstRawPtr Nat) => write p 1
  trivial

/-- The right to free a `Box` is exclusive. -/
example (p : MutRawPtr Nat) : p.freeable ∗ p.freeable ⊢ ⌜False⌝ := by
  rintro h ⟨h₁, h₂, hCompatible, -, hFree₁, hFree₂⟩
  have hEnd₁ := ((RawPtr.freeable_holds p h₁).mp hFree₁).2
  have hEnd₂ := ((RawPtr.freeable_holds p h₂).mp hFree₂).2
  have hSelf := Heap.Subheap.compatible hEnd₂
    (PartialCommMonoid.compatible_comm (Heap.Subheap.compatible hEnd₁ hCompatible))
  exact hSelf _ (Heap.mem_endMarker.mpr rfl) (Heap.mem_endMarker.mpr rfl)

/-- The right to free a `Box` cannot come from nothing. -/
example (p : MutRawPtr Nat) : ¬ (emp ⊢ p.freeable) := by
  intro hImpl
  exact Heap.not_isEndMarker_empty _ _
    (Heap.Subheap.isEndMarker ((RawPtr.freeable_holds p ∅).mp (hImpl ∅ trivial)).2)

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
  RawPtr.pointsToRange_append q [x] [y]

example (q : MutRawPtr Nat) : (q ↦* ([] : List Nat)) = emp :=
  RawPtr.pointsToRange_nil q

example (q : MutRawPtr Nat) (x y : Nat) : q ↦ x ∗ q ↦ y ⊢ ⌜False⌝ :=
  pointsTo_exclusive q x y (by simp)

example (q : MutRawPtr Nat) (x y : Nat) : q ↦ x ∗ (q.shift 1) ↦ y ⊢ q ↦* [x, y] :=
  entails_of_eq (RawPtr.pointsToRange_append q [x] [y]).symm

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

/-- Two past the end of a one-cell allocation: `add` steps over the dead end marker. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (5 : Nat)
    p.add 2#usize) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (into_raw.spec _) fun p => ifails_ipure fun _ => ?_
  exact ifails_mono (by iframe) (add_fails (P := p.freeable) p 2#usize 1 (by simp)
    (by simpa using freeable_not_isLive p 1 .global))

/-- `add 0` is allowed on any pointer, including into an empty allocation. -/
example : ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_ptr (Aeneas.Std.Slice.new Nat))
    fun (p, _) => p.add 0#usize) ⦃ _ => ⌜True⌝ ⦄ := by
  step*

/-- A non-zero `add` into an empty allocation steps over its dead end marker. -/
example : ¬ ⦃ emp ⦄ (Aeneas.Std.bind (Aeneas.Std.Slice.as_ptr (Aeneas.Std.Slice.new Nat))
    fun (p, _) => p.add 1#usize) ⦃ _ => ⌜True⌝ ⦄ := by
  apply not_ispec_of_ifails_emp
  refine ifails_bind (Std.Slice.as_ptr.spec _) fun (p, _) => ifails_ipure fun _ =>
    ifails_ipure fun _ => ?_
  exact ifails_mono (by simp [Std.Slice.new]; iframe)
    (add_fails (P := p.freeable 0 .view) p 1#usize 0 (by simp)
      (by simpa using freeable_not_isLive p 0 .view))

end SepLogic
