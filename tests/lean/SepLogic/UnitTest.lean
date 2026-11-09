import SepLogic.Fixtures

/-! Unit tests of the separation-logic layer: entailments and the `i` tactics (`iframe`, `iintro`,
`irewrite`, `isimp`, `iwp =>`), the raw-pointer operations (including that they are not enabled
without their resources), and `step` on `ispec`/`dispec` triples. -/

open Aeneas
open SepLogic
open Aeneas.SepLogic

namespace SepLogic

open Aeneas.Data.Coinductive

open Aeneas.Std.WP

open Aeneas.Std (Heap MutRawPtr RawPtr Result RustEffect U32)
open Aeneas.Std.MutRawPtr (write)
open Aeneas.Std.alloc.boxed.Box (into_raw from_raw)
open Aeneas.Std.RawPtr (read)

unseal Result

example : (Result.fail .panic : Result Nat) =
    Result.vis (RustEffect.Input.fail .panic) PEmpty.elim :=
  rfl

example (Q : Nat → Prop) :
    ¬ spec (Result.fail .panic : Result Nat) Q :=
  fun h => nomatch (spec_fail .panic).mp h

example (Q : Nat → Prop) :
    ¬ dspec (Result.fail .panic : Result Nat) Q :=
  fun h => nomatch (dspec_fail .panic).mp h

/-- The successor on the `U32` pointees of these tests: wrapping, so that the tests need no
overflow side conditions. -/
def inc (x : U32) : U32 := x.wrapping_add 1#u32

example (P Q : IProp) : emp ⊢ (P ∗ (P -∗ Q)) -∗ Q := by
  apply wand_intro
  irewrite (wand_cancel P Q)
  iframe

example (p q : MutRawPtr U32) (x y : U32) :
    p ↦ x ∗ q ↦ y ⊢ q ↦ y ∗ p ↦ x := by
  iframe

example (p : MutRawPtr U32) (value : U32) :
    p ↦ value ⊢ iprop(∃ w, ⌜w = value⌝ ∗ p ↦ w) := by
  iframe

example (p : MutRawPtr U32) (value : U32) (w : Nat) :
    iprop(⌜w = value.val + 1⌝ ∗ p ↦ value) ⊢ iprop(⌜0 < w⌝ ∗ p ↦ value) := by
  iframe

example (p : MutRawPtr U32) :
    iprop(∃ n : U32, ⌜0 < n.val⌝ ∗ p ↦ n) ⊢ iprop(∃ m, p ↦ m) := by
  iframe

example (p q r : MutRawPtr U32) (x y z : U32) :
    iprop((p ↦ x ∗ q ↦ y) ∗ r ↦ z) ⊢ iprop(r ↦ z ∗ (q ↦ y ∗ p ↦ x)) := by
  iframe

example (p : MutRawPtr U32) :
    p ↦ 3#u32 ⊢ iprop(∃ n : U32, ⌜0 < n.val⌝ ∗ p ↦ n) := by
  iframe

example (p : MutRawPtr U32) :
    ⦃ iprop(∃ n : U32, ⌜n = 1#u32⌝ ∗ p ↦ n) ⦄ Fixtures.incr_ptr p
      ⦃ ∃ v, ⌜v.val = 2⌝ ∗ p ↦ v⦄ := by
  fail_if_success
    step
    done
  fail_if_success iintro_shallow
  iwp => iintro_shallow
  step*

example (p : MutRawPtr U32) (value : U32) :
    ⦃ iprop(⌜value = 1#u32⌝ ∗ p ↦ value) ⦄ Fixtures.incr_ptr p
      ⦃ ∃ v, ⌜v.val = 2⌝ ∗ p ↦ v⦄ := by
  iwp => iintro
  step*

example (p : MutRawPtr U32) (value : U32) :
    ⦃ iprop(p ↦ value ∗ ⌜value = 1#u32⌝) ⦄ pure () ⦃ p ↦ value⦄ := by
  apply ispec_ok
  iintro_shallow
  guard_hyp h : value = 1#u32
  iframe

example (p : MutRawPtr U32) (value : U32) :
    ⦃ iprop(p ↦ value ∗ ⌜value = 1#u32⌝) ⦄ pure () ⦃ p ↦ value⦄div := by
  apply dispec_ok
  iintro_shallow
  guard_hyp h : value = 1#u32
  iframe

example (p : MutRawPtr U32) (value : U32) (P F : Prop) :
    ⦃ iprop((p ↦ value ∗ ⌜P⌝) ∗ ⌜F⌝) ⦄ pure ()
      ⦃ iprop(p ↦ value ∗ ⌜F⌝)⦄ := by
  apply ispec_ok
  iintro_shallow_post
  guard_hyp h : P
  fail_if_success have : F := by assumption
  iframe

example (p q : MutRawPtr U32) :
    ⦃ iprop(⌜q = p⌝ ∗ p ↦ 1#u32) ⦄ Fixtures.incr_ptr q
      ⦃ iprop(⌜q = p⌝ ∗ ∃ v, ⌜v.val = 2⌝ ∗ p ↦ v)⦄ := by
  iwp => iintro_shallow
  subst_vars
  step*

example (p : MutRawPtr U32) (n : U32) :
    ⦃ iprop(⌜n = 1#u32⌝ ∗ p ↦ n) ⦄ pure () ⦃ iprop(⌜n = 1#u32⌝ ∗ p ↦ 1#u32)⦄ := by
  apply ispec_ok
  iintro_keep
  guard_target = (iprop(⌜n = 1#u32⌝ ∗ p ↦ n) ⊢ iprop(⌜n = 1#u32⌝ ∗ p ↦ 1#u32))
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

def touchAny (p : MutRawPtr U32) : Result Unit := do
  let value ← read p
  write p value

@[step]
theorem touchAny.spec (p : MutRawPtr U32) :
    ⦃ iprop(∃ n : U32, p ↦ n) ⦄ touchAny p ⦃ iprop(∃ n : U32, p ↦ n)⦄ := by
  unfold touchAny
  fail_if_success
    step*
    done
  iwp => iintro n
  step*

def touchThenSet (p : MutRawPtr U32) : Result Unit := do
  touchAny p
  write p 7#u32

example (p : MutRawPtr U32) (x : U32) :
    ⦃ iprop(⌜x = 5#u32⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃ iprop(⌜x = 5#u32⌝ ∗ p ↦ 7#u32)⦄ := by
  unfold touchThenSet
  step as ⟨ pulled ⟩
  guard_hyp pulled : U32
  step*

example (p : MutRawPtr U32) (x : U32) :
    ⦃ iprop(⌜x = 5#u32⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃ iprop(⌜x = 5#u32⌝ ∗ p ↦ 7#u32)⦄ := by
  unfold touchThenSet
  step*

example (p q : MutRawPtr U32) (x : U32) :
    ⦃ iprop(iexists (fun n : U32 => q ↦ n) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃ iprop(iexists (fun n : U32 => q ↦ n) ∗ p ↦ 7#u32)⦄ := by
  unfold touchThenSet
  step*

example (p : MutRawPtr U32) :
    ⦃ iprop(∃ n : U32, p ↦ n) ⦄ touchThenSet p ⦃ p ↦ 7#u32⦄ := by
  unfold touchThenSet
  step*

example (p : MutRawPtr U32) (x : U32) : (p ↦ x ⊢ p ↦ x) ∧ 1 = 1 := by
  refine ⟨?_, ?_⟩
  · iframe
  · rfl

def readThenWrite (p : MutRawPtr U32) : Result Unit := do
  let value ← read p
  write p (inc value)

example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ readThenWrite p ⦃ p ↦ inc value⦄ := by
  unfold readThenWrite
  step as ⟨actual, hActual⟩
  guard_hyp hActual : actual = value
  subst actual
  guard_target =
    ⦃ p ↦ value ⦄ write p (inc value) ⦃ p ↦ inc value⦄
  step*

def readAndFree (p : MutRawPtr U32) : Result Nat := do
  let v ← read p
  let _ ← from_raw p
  pure (v.val + 1)

/-- `p.freeable 1` is required: without it, `p` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour in Rust (see `from_raw.spec`). -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ∗ p.freeable 1 ⦄ readAndFree p ⦃ result => ⌜result = value.val + 1⌝⦄ := by
  unfold readAndFree
  step*

def opaqueStepResult (actual expected : Nat) : Prop :=
  actual = expected

def readFreeReturn (p : MutRawPtr U32) : Result Nat := do
  let value ← read p
  let _ ← from_raw p
  pure (value.val + 1)

/-- `p.freeable 1` is required: without it, `p` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour in Rust (see `from_raw.spec`). -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ∗ p.freeable 1 ⦄ readFreeReturn p
      ⦃ result => ⌜opaqueStepResult result (value.val + 1)⌝⦄ := by
  unfold readFreeReturn
  step*
  simp only [opaqueStepResult]
  agrind

/-- `p.freeable 1` is required: without it, `p` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour in Rust (see `from_raw.spec`). -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ∗ p.freeable 1 ⦄ readFreeReturn p
      ⦃ result => ⌜opaqueStepResult result (value.val + 1)⌝⦄ := by
  unfold readFreeReturn
  step* 2
  step
  simp only [opaqueStepResult]
  agrind

/-- `p.freeable 1` is required: without it, `p` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour in Rust (see `from_raw.spec`). -/
example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ∗ p.freeable 1 ⦄ readFreeReturn p
      ⦃ result => ⌜result = value.val + 1⌝⦄ := by
  unfold readFreeReturn
  fail_if_success
    step*
    step
  step
  step
  step
  agrind

example (p : MutRawPtr U32) (value : U32) :
    p ↦ value ⊢ emp := by
  iframe

example (p q : MutRawPtr U32) (left right : U32) :
    p ↦ left ∗ q ↦ right ⊢ p ↦ left := by
  iframe

example (P : IProp) : P ⊢ ⌜8 = 8⌝ := by
  iframe

example (p q : MutRawPtr U32) (left right : U32) :
    p ↦ left ∗ q ↦ right ⊢ p ↦ left ∗ emp := by
  iframe

example (p q : MutRawPtr U32) (x y : U32) : p ↦ x ∗ q ↦ y ⊢ q ↦ y := by
  fail_if_success
    (have : p ↦ x ⊢ q ↦ y := by iframe)
  iframe

/-! ### Raw-pointer operations need their resources -/

theorem not_subheap_empty {a : Fragment} {r : Resource} (hr : a r)
    (h : PartialCommMonoid.Subheap a ∅) : False := by
  obtain ⟨rest, -, he⟩ := PartialCommMonoid.subheap_iff.mp h
  have : (a ∪ rest) r := Or.inl hr
  rw [← he] at this
  exact this

theorem mem_of_subheap {a h : Fragment} {r : Resource} (hr : a r)
    (hSub : PartialCommMonoid.Subheap a h) : h r := by
  obtain ⟨rest, -, rfl⟩ := PartialCommMonoid.subheap_iff.mp hSub
  exact Or.inl hr

example (p : MutRawPtr U32) (value : U32) : ¬ (emp ⊢ p ↦ value) := by
  intro hImpl
  obtain ⟨bptr, a, ⟨data, -, -, -, rfl⟩, hSub⟩ := hImpl ∅ trivial
  exact not_subheap_empty ⟨0, by simpa using Aeneas.Std.Pointee.Sized.pos (T := U32), rfl⟩ hSub

/-- The right to free a `Box` cannot come from nothing. -/
example (p : MutRawPtr U32) : ¬ (emp ⊢ p.freeable 1) := by
  intro hImpl
  obtain ⟨a, ⟨-, rfl⟩, hSub⟩ := hImpl ∅ trivial
  refine not_subheap_empty (r := .cleanup p.provenance (1 * (Aeneas.Std.Pointee.repr (T := U32)).size) p.address true) ?_ hSub
  rfl

/-- Two points-to assertions on the same pointer are never realized by a heap. (As an entailment of
fragments, `p ↦ x ∗ p ↦ y ⊢ ⌜False⌝` does not hold: the fragments of `p ↦ x` and `p ↦ y` may
describe the cells of `p` from two different block bases, which only the heap can rule out.) -/
example (p : MutRawPtr U32) (x y : U32) (s : Heap) : ¬ Realizes iprop(p ↦ x ∗ p ↦ y) s := by
  rintro ⟨-, h, ⟨h₁, h₂, hDisjoint, rfl, ⟨b₁, a₁, ⟨d₁, -, -, -, rfl⟩, hSub₁⟩,
    ⟨b₂, a₂, ⟨d₂, -, -, -, rfl⟩, hSub₂⟩⟩, hMatches, -⟩
  have hpos := Aeneas.Std.Pointee.Sized.pos (T := U32)
  have hr₁ := mem_of_subheap (r := .cell p.provenance (p.offsetFrom b₁ + 0) b₁ _)
    ⟨0, by simpa using hpos, rfl⟩ hSub₁
  have hr₂ := mem_of_subheap (r := .cell p.provenance (p.offsetFrom b₂ + 0) b₂ _)
    ⟨0, by simpa using hpos, rfl⟩ hSub₂
  obtain ⟨blk₁, hl₁, -, hb₁, -⟩ := hMatches _ (Or.inl hr₁)
  obtain ⟨blk₂, hl₂, -, hb₂, -⟩ := hMatches _ (Or.inr hr₂)
  rw [hl₁] at hl₂
  cases hl₂
  subst hb₁ hb₂
  have hCompatible := hDisjoint _ hr₁ _ hr₂
  simp [Resource.Compatible, Resource.base, Resource.key] at hCompatible

/-- On the empty heap, `read` is not enabled: it fails with `undef`. -/
example (p : MutRawPtr U32) : ¬ (⦃ emp ⦄ read p ⦃ _ => emp⦄) := by
  intro hTriple
  have hSpec := ispec_iff.mp hTriple emp Heap.empty (realizes_sep_emp.mpr realizes_emp_empty)
  simp only [Aeneas.Std.RawPtr.read, Result.checkedModify] at hSpec
  have hNone := hSpec.vis_view.2 none Heap.empty
    ⟨fun ⟨_, _, hRead, _⟩ => by simp [Heap.read, Heap.empty] at hRead, rfl⟩
  simp [Result.ofOption] at hNone
  exact absurd hNone.vis_view (by simp)

/-- On the empty heap, `write` is not enabled: it fails with `undef`. -/
example (p : MutRawPtr U32) (value : U32) : ¬ (⦃ emp ⦄ write p value ⦃ _ => emp⦄) := by
  intro hTriple
  have hSpec := ispec_iff.mp hTriple emp Heap.empty (realizes_sep_emp.mpr realizes_emp_empty)
  simp only [Aeneas.Std.MutRawPtr.write, Result.checkedModify] at hSpec
  have hNone := hSpec.vis_view.2 none Heap.empty
    ⟨fun ⟨_, _, ⟨_, _, hWrite⟩⟩ => by simp [Heap.write, Heap.modify, Heap.empty] at hWrite, rfl⟩
  simp [Result.ofOption] at hNone
  exact absurd hNone.vis_view (by simp)

def allocAndForget (value : U32) : Result Unit := do
  let _ ← into_raw ⟨value⟩
  pure ()

example (value : U32) :
    ⦃ emp ⦄ allocAndForget value ⦃ emp⦄ := by
  unfold allocAndForget
  step*

example (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ (pure () : Result Unit) ⦃ emp⦄ := by
  step*

theorem inc_pred (n : U32) : inc ⟨n.bv - BitVec.ofNat _ 1⟩ = n := by
  cases n
  simp [inc, Aeneas.Std.U32.wrapping_add, Aeneas.Std.UScalar.wrapping_add]

example (p : MutRawPtr U32) :
    iprop(∃ n : U32, ⌜0 < n.val⌝ ∗ p ↦ n) ⊢ iprop(∃ m, p ↦ inc m) := by
  iintro
  rename_i x hx
  refine entails_exists_r ⟨x.bv - BitVec.ofNat _ 1⟩ ?_
  rw [inc_pred]
  iframe

theorem cellPair (p q : MutRawPtr U32) :
    iprop(p ↦ 1#u32 ∗ q ↦ 2#u32) ⊢ iprop(∃ n : U32, p ↦ n ∗ q ↦ 2#u32) :=
  entails_exists_r 1#u32 (entails_refl _)

example (p q r : MutRawPtr U32) :
    iprop(r ↦ 0#u32 ∗ (p ↦ 1#u32 ∗ q ↦ 2#u32)) ⊢
      iprop(∃ n : U32, r ↦ 0#u32 ∗ (p ↦ n ∗ q ↦ 2#u32)) := by
  irewrite (cellPair p q)
  iframe

theorem swapEq (p q : MutRawPtr U32) :
    iprop(p ↦ 1#u32 ∗ q ↦ 2#u32) = iprop(q ↦ 2#u32 ∗ p ↦ 1#u32) :=
  sep_comm_eq _ _

example (p q : MutRawPtr U32) :
    ⦃ iprop((p ↦ 1#u32 ∗ q ↦ 2#u32) ∗ emp) ⦄ Fixtures.incr_ptr q
      ⦃ iprop((∃ v, ⌜v.val = 3⌝ ∗ q ↦ v) ∗ p ↦ 1#u32)⦄ := by
  iwp => irewrite (swapEq p q)
  step*

example (p : MutRawPtr U32) :
    ⦃ p ↦ 1#u32 ⦄ (pure 5 : Result Nat) ⦃ v => ⌜v = 5⌝ ∗ p ↦ 1#u32⦄ := by
  step*

example (p q : MutRawPtr U32) (x : U32) (h : x.val + 1 ≤ U32.max) :
    ⦃ iprop(p ↦ x ∗ q ↦ 9#u32) ⦄ Fixtures.incr_ptr p
      ⦃ iprop(q ↦ 9#u32 ∗ ∃ v, ⌜v.val = x.val + 1⌝ ∗ p ↦ v)⦄ := by
  step*

example (p q : MutRawPtr U32) :
    ⦃ iprop(p ↦ 3#u32 ∗ q ↦ 7#u32) ⦄ read p
      ⦃ r => iprop(⌜r = 3#u32⌝ ∗ (p ↦ 3#u32 ∗ q ↦ 7#u32))⦄ := by
  step with RawPtr.read.spec p 3#u32

example (q : MutRawPtr U32) :
    ⦃ iexists (fun n : U32 => iprop(q ↦ n)) ⦄ into_raw ⟨5#u32⟩
      ⦃ r => iprop((r ↦ 5#u32 ∗ r.freeable 1) ∗ iexists (fun n : U32 => iprop(q ↦ n)))⦄ := by
  step*

example (p q : MutRawPtr U32) (x : U32) :
    ⦃ iprop(iexists (fun n : U32 => iprop(q ↦ n)) ∗ p ↦ x) ⦄ touchThenSet p
      ⦃ iprop(iexists (fun n : U32 => iprop(q ↦ n)) ∗ p ↦ 7#u32)⦄ := by
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

example (p q : MutRawPtr U32) :
    (⦃ iprop(p ↦ 3#u32 ∗ q ↦ 7#u32) ⦄ read p
      ⦃ r => iprop(⌜r = 3#u32⌝ ∗ (p ↦ 3#u32 ∗ q ↦ 7#u32))⦄)
    ∧ (iprop(p ↦ 3#u32 ∗ q ↦ 7#u32) ⊢ iprop(q ↦ 7#u32 ∗ p ↦ 3#u32)) := by
  refine ⟨?_, ?_⟩
  step with RawPtr.read.spec p 3#u32
  guard_target = (iprop(p ↦ 3#u32 ∗ q ↦ 7#u32) ⊢ iprop(q ↦ 7#u32 ∗ p ↦ 3#u32))
  iframe

example (p : MutRawPtr U32) (x : U32) :
    ⦃ iprop(⌜x = 5#u32⌝ ∗ p ↦ x) ⦄ touchThenSet p ⦃ iprop(⌜x = 5#u32⌝ ∗ p ↦ 7#u32)⦄ := by
  unfold touchThenSet
  step*

example (p : MutRawPtr U32) :
    ⦃ iprop(∃ n : U32, p ↦ n) ⦄ touchAny p ⦃ iprop(∃ n : U32, p ↦ n)⦄ := by
  unfold touchAny
  iwp => iintro n
  step with RawPtr.read.spec p n
  step*

def readTwice (p : MutRawPtr U32) : Result Nat := do
  let a ← read p
  let b ← read p
  pure (a.val + b.val)

@[step]
theorem readTwice.spec (p : MutRawPtr U32) (n : U32) (hn : 0 < n.val) :
    ⦃ p ↦ n ⦄ readTwice p ⦃ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  unfold readTwice
  step*

example (p : MutRawPtr U32) :
    ⦃ p ↦ 3#u32 ⦄ readTwice p ⦃ r => iprop(⌜0 < r⌝ ∗ p ↦ 3#u32)⦄ := by
  step*

example (p : MutRawPtr U32) (n : U32) (b : Bool) (hb : b = true)
    (hguard : b = true → 0 < n.val) :
    ⦃ p ↦ n ⦄ readTwice p ⦃ r => iprop(⌜0 < r⌝ ∗ p ↦ n)⦄ := by
  step*

example (q : MutRawPtr U32) (x : U32) : (q ↦* [x]) = (q ↦ x) :=
  RawPtr.range_singleton q x

/-- `as_mut_ptr` returns a `Result` in `Type 1` (its back computation), hence the explicit
universe-heterogeneous `Std.bind` (the extracted code gets it from the Aeneas `do` elaborator). -/
def slicePtrWrite (s : Aeneas.Std.Slice U32) : Result (U32 × Aeneas.Std.Slice U32) :=
  Aeneas.Std.bind (Aeneas.Std.Slice.as_mut_ptr ⟨s⟩) fun (p, back) => do
    let q ← p.add 1#usize
    write q 42#u32
    let value ← read q
    let s ← back
    pure (value, s)

/-- The write through the pointer is seen in the slice given back when the borrow ends. -/
theorem slicePtrWrite.spec (s : Aeneas.Std.Slice U32) (h : 1 < s.length) :
    ⦃ emp ⦄ slicePtrWrite s ⦃ (value, s') => ⌜value = 42#u32 ∧ s'.val = s.val.set 1 42#u32⌝⦄ := by
  unfold slicePtrWrite
  step as ⟨r, hr⟩
  obtain ⟨p, back⟩ := r
  simp only at hr
  subst hr
  step with RawPtr.add.spec p s.val 1#usize (by scalar_tac) (by scalar_tac)
  subst_vars
  step with MutRawPtr.write.spec_range p s.val 1 42#u32 (by simpa using h)
  step with RawPtr.read.spec_range p (s.val.set 1 42#u32) 1 (by simpa using h)
  step*
  exact ⟨by simp [value_post], s_post⟩

end SepLogic
