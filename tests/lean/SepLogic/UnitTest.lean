import SepLogic.Fixtures

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
  iintro_shallow
  step*

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ iprop(⌜value = 1⌝ ∗ p ↦ value) ⦄ Fixtures.incr_ptr p ⦃ p ↦ 2⦄ := by
  unfold Fixtures.incr_ptr
  iintro
  step*

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ iprop(p ↦ value ∗ ⌜value = 1⌝) ⦄ pure () ⦃ p ↦ value⦄ := by
  wp_pures
  iintro_shallow
  guard_hyp h : value = 1
  iframe

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ iprop(p ↦ value ∗ ⌜value = 1⌝) ⦄ pure () ⦃ p ↦ value⦄div := by
  dwp_pures
  iintro_shallow
  guard_hyp h : value = 1
  iframe

example (p : MutRawPtr Nat) (value : Nat) (P F : Prop) :
    ⦃ iprop((p ↦ value ∗ ⌜P⌝) ∗ ⌜F⌝) ⦄ pure ()
      ⦃ iprop(p ↦ value ∗ ⌜F⌝)⦄ := by
  wp_pures
  iintro_shallow_post
  guard_hyp h : P
  fail_if_success have : F := by assumption
  iframe

example (p q : MutRawPtr Nat) :
    ⦃ iprop(⌜q = p⌝ ∗ p ↦ 1) ⦄ Fixtures.incr_ptr q ⦃ iprop(⌜q = p⌝ ∗ p ↦ 2)⦄ := by
  unfold Fixtures.incr_ptr
  iintro_shallow
  step*

example (p : MutRawPtr Nat) (n : Nat) :
    ⦃ iprop(⌜n = 1⌝ ∗ p ↦ n) ⦄ pure () ⦃ iprop(⌜n = 1⌝ ∗ p ↦ 1)⦄ := by
  wp_pures
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
  iintro n
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

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readAndFree p ⦃ result => ⌜result = value + 1⌝⦄ := by
  unfold readAndFree
  step*

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : MutRawPtr Nat) : Result Nat := do
  let value ← read p
  let _ ← from_raw p
  pure (value + 1)

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  step*
  simp only [opaqueStepResult]
  agrind

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
      ⦃ result => ⌜opaqueStepResult result (value + 1)⌝⦄ := by
  unfold readFreeReturn
  step* 2
  step
  simp only [opaqueStepResult]
  agrind

example (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ readFreeReturn p
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
  exact RawPtr.not_contains_empty p hContains

example (p : MutRawPtr Nat) : ¬ (⦃ emp ⦄ read p ⦃ _ => emp⦄) := by
  intro hTriple
  rw [ispec_iff] at hTriple
  have hSpec := hTriple emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.RawPtr.read, Result.guardedModify] at hSpec
  obtain ⟨hReadable, -⟩ := hSpec.vis_view
  exact RawPtr.not_contains_empty p hReadable.contains

/-! Allocation ids are never reused: freed slots and end markers stay in the heap as dead slots. -/

/-- Use after free: the freed slot stays dead, and the next allocation gets a new id. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let _ ← from_raw p
    let _ ← into_raw (2 : Nat)
    RawPtr.read p) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [into_raw, from_raw, RawPtr.read, RawPtr.materialize, Result.guardedModify,
    Std.bind_tc_vis, Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hReadable, -⟩ := hSpec.vis_view
  exact Heap.not_contains_free hContains
    ((Heap.contains_freshHeap_of_mem (Heap.mem_free hContains)).mp hReadable.contains)

/-- Double free, with an allocation in between that must not reuse the freed id. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← into_raw (1 : Nat)
    let _ ← from_raw p
    let _ ← into_raw (2 : Nat)
    from_raw p) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [into_raw, from_raw, RawPtr.materialize, Result.guardedModify,
    Std.bind_tc_vis, Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hContains', -⟩ := hSpec.vis_view
  exact Heap.not_contains_free hContains
    ((Heap.contains_freshHeap_of_mem (Heap.mem_free hContains)).mp hContains')

/-- A pointer into an empty slice does not alias the next allocation. -/
example : ¬ ⦃ emp ⦄ (do
    let p ← Aeneas.Std.Slice.as_ptr (Aeneas.Std.Slice.new Nat)
    let _ ← into_raw (5 : Nat)
    RawPtr.read p) ⦃ _ => ⌜True⌝ ⦄ := by
  intro hTriple
  have hSpec := (ispec_iff.mp hTriple) emp ∅ ((entails_of_eq (sep_emp_r_eq emp).symm) ∅ trivial)
  simp only [Aeneas.Std.Slice.as_ptr, into_raw, RawPtr.read, RawPtr.materialize,
    Result.guardedModify, Std.bind_tc_vis, Std.bind_tc_ok] at hSpec
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨_, hSpec⟩ := hSpec.vis_view
  obtain ⟨hReadable, -⟩ := hSpec.vis_view
  exact Heap.not_contains_freshHeap_end (h := ∅) (values := (Aeneas.Std.Slice.new Nat).val)
    ((Heap.contains_freshHeap_of_mem (Heap.mem_freshHeap_end _ _)).mp hReadable.contains)

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

example (H1 H2 : IProp) : H1 ∗ (H1 -∗ H2) ⊢ H2 := wand_cancel H1 H2
example (Q1 Q2 : IPost Nat) : Q1 ∗+ (Q1 -∗+ Q2) ⊢+ Q2 := postWand_cancel Q1 Q2

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
  irewrite (swapEq p q)
  step*

example (p : MutRawPtr Nat) : ⦃ p ↦ 1 ⦄ (pure 5 : Result Nat) ⦃ v => ⌜v = 5⌝ ∗ p ↦ 1⦄ := by
  wp_pures
  iframe

example (p q : MutRawPtr Nat) (x : Nat) :
    ⦃ iprop(p ↦ x ∗ q ↦ 9) ⦄ Fixtures.incr_ptr p ⦃ iprop(q ↦ 9 ∗ p ↦ (x + 1))⦄ := by
  wp_apply (Fixtures.incr_ptr.spec p x)


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
    iintro
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
  iintro n
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

example (p : MutRawPtr Nat) (n : Nat) (b : Bool) (hb : b = true) (hguard : b = true → 0 < n) :
    ⦃ p ↦ n ⦄ readTwice p ⦃ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  step* -grind -threadGrindState

example (q : MutRawPtr Nat) (x y : Nat) :
    (q ↦* [x, y]) = iprop(q ↦ x ∗ (q.shift 1) ↦ y) :=
  RawPtr.pointsToRange_append q [x] [y]

example (q : MutRawPtr Nat) (i : Nat) : (q.shift i).base = q.base := rfl

example (q : MutRawPtr Nat) : (q ↦* ([] : List Nat)) = emp :=
  RawPtr.pointsToRange_nil q

example (q : MutRawPtr Nat) (x y : Nat) : q ↦ x ∗ q ↦ y ⊢ ⌜False⌝ :=
  pointsTo_exclusive q x y

example (q : MutRawPtr Nat) (x y : Nat) : q ↦ x ∗ (q.shift 1) ↦ y ⊢ q ↦* [x, y] :=
  entails_of_eq (RawPtr.pointsToRange_append q [x] [y]).symm

def slicePtrWrite (s : Aeneas.Std.Slice Nat) : Result (Nat × Aeneas.Std.Slice Nat) := do
  let (p, s) ← s.as_mut_ptr
  write (p.add 1#usize) 42
  let value ← read (p.add 1#usize)
  pure (value, s)

/-- `as_mut_ptr` copies: the write is seen through the pointer, not in the returned slice. -/
theorem slicePtrWrite.spec (s : Aeneas.Std.Slice Nat) (h : 1 < s.length) :
    ⦃ emp ⦄ slicePtrWrite s ⦃ (value, s') => ⌜value = 42 ∧ s' = s⌝⦄ := by
  unfold slicePtrWrite
  step as ⟨r, hr⟩
  obtain ⟨p, s'⟩ := r
  simp only [RawPtr.add_eq_shift, show (1#usize).val = 1 by simp]
  step with MutRawPtr.write.spec_range p s.val 1 42 (by simpa using h)
  step with RawPtr.read.spec_range p (s.val.set 1 42) 1 (by simpa using h)
  step*

end SepLogic
