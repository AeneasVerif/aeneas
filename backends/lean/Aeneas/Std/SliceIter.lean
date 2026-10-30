/- Arrays/Slices -/
module
public import Aeneas.Std.Slice
public import Aeneas.Std.Array.Array
public import Aeneas.Std.Array.ArraySlice
public import Aeneas.Std.Core.Iter
public meta import Aeneas.Std.Core.Iter
meta import Aeneas.Std.Slice
meta import Aeneas.Std.Array.Array
public meta import Lean.Elab.Tactic.Basic
import Aeneas.Tactic.Misc.FCongr.FCongr
public section

@[expose] section

namespace Aeneas.Std

open Result Error core.ops.range WP

attribute [-simp] List.getElem!_eq_getElem?_getD


@[rust_type "core::slice::iter::Iter"]
structure core.slice.iter.Iter (T : Type _) where
  /- We need to remember the slice and an index inside the slice (this is necessary)
     for double ended iterators) -/
  slice : Slice T
  i : Nat

@[rust_type "core::slice::iter::IterMut" (mutRegions := #[0]) (body := .opaque)]
structure core.slice.iter.IterMut (T : Type _) where
  /- We need to remember the slice and an index inside the slice (this is necessary)
     for double ended iterators) -/
  slice : Slice T
  i : Nat := 0

@[rust_fun "core::slice::{[@T]}::iter"]
def core.slice.Slice.iter {T : Type _} (s : Slice T) : Result (core.slice.iter.Iter T) :=
  ok ⟨ s, 0 ⟩

@[rust_fun "core::slice::{[@T]}::contains"]
def core.slice.Slice.contains {T : Type _} (partialEqInst : core.cmp.PartialEq T T)
  (s : Slice T) (x : T) : Result Bool :=
  List.anyM (partialEqInst.eq x) s.val

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::next"]
def core.slice.iter.IteratorIterMut.next
  {T : Type _}
  (it : core.slice.iter.IterMut T) :
  Result ((Option T) × (core.slice.iter.IterMut T) ×
          (core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T)) :=
  if h: it.i < it.slice.len then
    let x := it.slice[it.i]
    let i := it.i
    let it := { it with i := i + 1 }
    let back it' x :=
      match x with
      | none => it'
      | some x => { it' with slice := it'.slice.setAtNat i x }
    ok (some x, it, back)
  else ok (none, it, fun it _ => it)

@[rust_fun "core::slice::{[@T]}::iter_mut"]
def core.slice.Slice.iter_mut {T : Type _} (slice : Slice T) :
  Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut T → Slice T)) :=
  ok ({slice}, fun it => it.slice)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::next"]
def core.slice.iter.IteratorSliceIter.next
  {T : Type _} (it : core.slice.iter.Iter T) : Result ((Option T) × (core.slice.iter.Iter T)) :=
  if h : it.i < it.slice.len then
    let x := it.slice[it.i]
    let it := { it with i := it.i + 1}
    ok (some x, it)
  else ok (none, it)

/-- `DoubleEndedIterator::next_back` on `slice::Iter`.

The standard library generates this impl with the `iterator!` macro
(`library/core/src/slice/iter/macros.rs`):
```rust
fn next_back(&mut self) -> Option<&'a T> {
    if is_empty!(self) { None } else { Some(self.next_back_unchecked()) }
}
```
where `is_empty!` is `self.ptr == self.end`, and `next_back_unchecked` decrements `end` by one
and returns the element it now points to.

The model represents the remaining elements as `slice[i..slice.length]`: `ptr` corresponds
to `i` and `end` to `slice.length`. Decrementing `end` is therefore truncating the slice by
one, and `i` is left untouched, as `ptr` is. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::double_ended::DoubleEndedIterator<core::slice::iter::Iter<'a, @T>, &'_ @T>}::next_back"]
def core.slice.iter.IteratorSliceIter.next_back
  {T : Type} (it : core.slice.iter.Iter T) : Result ((Option T) × (core.slice.iter.Iter T)) :=
  if h : it.i < it.slice.val.length then
    let n := it.slice.val.length - 1
    let x := it.slice[n]'(by scalar_tac)
    let s := Slice.from (it.slice.val.take n) (by scalar_tac)
    ok (some x, { it with slice := s })
  else ok (none, it)

@[step]
theorem core.slice.iter.IteratorSliceIter.next_back.spec
    {T : Type} (it : core.slice.iter.Iter T) (h : it.i < it.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next_back it
    ⦃ r => r.1 = it.slice.val.getLast? ∧
           r.2.slice.val = it.slice.val.take (it.slice.val.length - 1) ∧
           r.2.i = it.i ⦄ := by
  unfold core.slice.iter.IteratorSliceIter.next_back
  simp [h, WP.spec_ok, List.getLast?_eq_getElem?]
  rw [List.getElem?_eq_getElem (by scalar_tac), Slice.getElem_Nat_eq]
  scalar_tac

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>"]
impl_def core.iter.traits.iterator.IteratorSliceIter (T : Type _) :
  core.iter.traits.iterator.Iterator (core.slice.iter.Iter T) T := {
  next := core.slice.iter.IteratorSliceIter.next
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorSliceIter T)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.traits.iterator.IteratorSliceIter T)
  take := core.iter.traits.iterator.Iterator.take.trait_default
    (core.iter.traits.iterator.IteratorSliceIter T)
}

-- ============================================================================
-- IntoIterator for shared array references: &[T; N] → Iter<T>
-- ============================================================================

/-- Model for `IntoIterator::into_iter` for `&[T; N]`.
Mirrors Rust: `(&[T; N]).into_iter()` returns an `Iter<T>` over the array
viewed as a slice. -/
@[rust_fun
  "core::array::{core::iter::traits::collect::IntoIterator<&'a [@T; @N], &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
    {T : Type _} {N : Usize} (a : Array T N) : Result (core.slice.iter.Iter T) :=
  ok ⟨ .from a.val (by scalar_tac), 0 ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<&'a [@T; @N], &'a @T, core::slice::iter::Iter<'a, @T>>"]
def SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
    (T : Type _) (N : Usize) :
    core.iter.traits.collect.IntoIterator (Array T N) T (core.slice.iter.Iter T) := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceIter T
  into_iter := SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
}

-- ============================================================================
-- IntoIterator for mutable array references: &mut [T; N] → IterMut<T>
-- ============================================================================

/-- Model for `IntoIterator::into_iter` for `&mut [T; N]`
(<https://doc.rust-lang.org/std/primitive.array.html#impl-IntoIterator-for-%26mut+%5BT;+N%5D>). -/
@[rust_fun
  "core::array::{core::iter::traits::collect::IntoIterator<&'a mut [@T; @N], &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter"]
def MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
    {T : Type _} {N : Usize} (a : Array T N) :
    Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut T → Array T N)) :=
  ok ({ slice := Array.to_slice a }, fun it => Array.from_slice a it.slice)

-- ============================================================================
-- IntoIterator for shared slice references: &[T] → Iter<T>
-- ============================================================================

/-- Model for `IntoIterator::into_iter` for `&[T]`.
Mirrors Rust: `(&[T]).into_iter()` returns an `Iter<T>` starting at index 0. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
    {T : Type _} (s : Slice T) : Result (core.slice.iter.Iter T) :=
  ok ⟨ s, 0 ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, core::slice::iter::Iter<'a, @T>>"]
def SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
    (T : Type _) :
    core.iter.traits.collect.IntoIterator (Slice T) T (core.slice.iter.Iter T) := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceIter T
  into_iter := SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
}

@[rust_type "core::slice::iter::ChunksExact" (body := .opaque)]
structure core.slice.iter.ChunksExact (T : Type _) where
  chunks : List (Slice T)
  remainder : Slice T

@[rust_fun
  "core::slice::iter::{core::slice::iter::ChunksExact<'a, @T>}::remainder"]
def core.slice.iter.ChunksExact.getRemainder
  {T : Type _} (self : core.slice.iter.ChunksExact T) : Result (Slice T) :=
  ok self.remainder

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::next"]
def core.slice.iter.IteratorChunksExact.next
  {T : Type _} (self : core.slice.iter.ChunksExact T) :
  Result ((Option (Slice T)) × (core.slice.iter.ChunksExact T)) :=
  match self.chunks with
  | [] => ok (none, self)
  | chunk :: chunks => ok (some chunk, { chunks, remainder := self.remainder })

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>"]
impl_def core.iter.traits.iterator.IteratorChunksExact (T : Type _) :
  core.iter.traits.iterator.Iterator (core.slice.iter.ChunksExact T) (Slice T)
  := {
  next := core.slice.iter.IteratorChunksExact.next
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorChunksExact T)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.traits.iterator.IteratorChunksExact T)
  take := core.iter.traits.iterator.Iterator.take.trait_default
    (core.iter.traits.iterator.IteratorChunksExact T)
}

/-- Split a list into non-overlapping chunks of exactly size `n`, returning the
    full-sized chunks and the trailing remainder (which has fewer than `n` elements). -/
def List.toChunksExact (n : Nat) (hn : 0 < n) (l : List α) :
    List (List α) × List α :=
  if _h : l.length < n then ([], l)
  else
    let (chunks, rem) := toChunksExact n hn (l.drop n)
    (l.take n :: chunks, rem)
termination_by l.length
decreasing_by simp [List.length_drop]; omega

theorem List.toChunksExact_chunk_length
    {n : Nat} (hn : 0 < n) (l : List α) :
    ∀ c ∈ (List.toChunksExact n hn l).1, c.length ≤ n := by
  unfold toChunksExact
  split
  · simp
  · simp only [List.mem_cons]
    intro c hc
    rcases hc with rfl | hc
    · simp [List.length_take]
    · exact toChunksExact_chunk_length hn _ c hc
termination_by l.length
decreasing_by simp [List.length_drop]; omega

theorem List.toChunksExact_remainder_length
    {n : Nat} (hn : 0 < n) (l : List α) :
    (List.toChunksExact n hn l).2.length ≤ l.length := by
  unfold toChunksExact
  split
  · simp
  · simp only []
    have := toChunksExact_remainder_length hn (l.drop n)
    simp [List.length_drop] at this
    omega
termination_by l.length
decreasing_by simp [List.length_drop]; omega

@[rust_fun "core::slice::{[@T]}::chunks_exact"]
def core.slice.Slice.chunks_exact {T : Type _} (s : Slice T) (chunk_size : Std.Usize) :
  Result (core.slice.iter.ChunksExact T) :=
  if hcs : chunk_size.val > 0 then
    let result := List.toChunksExact chunk_size.val hcs s.val
    let sliceChunks := result.1.attach.map fun ⟨c, hc⟩ => .from c (by
        have := List.toChunksExact_chunk_length hcs s.val c hc
        scalar_tac)
    ok { chunks := sliceChunks,
         remainder := .from result.2 (by
           have := List.toChunksExact_remainder_length hcs s.val
           grind) }
  else fail .panic


-- ============================================================================
-- StepBy tests
-- ============================================================================

private def mkSliceIter (l : List Nat) (h : l.length ≤ Usize.max := by scalar_tac) :
    core.slice.iter.Iter Nat :=
  { slice := .from l h, i := 0 }

private def collectStepBy (sbi : core.iter.adapters.step_by.StepBy (core.slice.iter.Iter Nat))
    (fuel : Nat := 100) : Result (List Nat) :=
  match fuel with
  | 0 => .ok []
  | fuel + 1 => do
    let (opt, sbi) ←
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorSliceIter Nat) sbi
    match opt with
    | none => .ok []
    | some x => do
      let rest ← collectStepBy sbi fuel
      .ok (x :: rest)

-- step_by(0) panics
#guard
  match (core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [1, 2, 3]) 0#usize).match with
  | .vis (.fail e) _ => e == panic
  | _ => false

-- step_by(1) returns all elements
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2, 3, 4]) 1#usize
  collectStepBy sbi).reducesTo [0, 1, 2, 3, 4]

-- step_by(2) returns every other element
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2, 3, 4]) 2#usize
  collectStepBy sbi).reducesTo [0, 2, 4]

-- step_by(3)
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2, 3, 4, 5, 6]) 3#usize
  collectStepBy sbi).reducesTo [0, 3, 6]

-- step_by larger than collection: returns only first element
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2]) 10#usize
  collectStepBy sbi).reducesTo [0]

-- step_by on empty iterator
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter []) 2#usize
  collectStepBy sbi).reducesTo []

-- step_by(1) on single element
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [42]) 1#usize
  collectStepBy sbi).reducesTo [42]

-- step_by(2) on single element
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [42]) 2#usize
  collectStepBy sbi).reducesTo [42]

-- step_by equal to length: returns only first element
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2]) 3#usize
  collectStepBy sbi).reducesTo [0]

-- step_by = length - 1
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2]) 2#usize
  collectStepBy sbi).reducesTo [0, 2]

-- step_by(2) on two elements: returns only first
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1]) 2#usize
  collectStepBy sbi).reducesTo [0]

-- step_by(2) on three elements: returns first and third
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2]) 2#usize
  collectStepBy sbi).reducesTo [0, 2]

-- step_by(4) on longer sequence
#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default
    (mkSliceIter [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) 4#usize
  collectStepBy sbi).reducesTo [0, 4, 8]

-- Verify that step_by(0) on the generic Iterator.step_by.default also panics
#guard
  match (core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [1]) 0#usize).match with
  | .vis (.fail e) _ => e == panic
  | _ => false

-- Nested step_by: step_by(2) then step_by(2) on [0..8] gives [0, 4]
private def collectNestedStepBy
    (sbi : core.iter.adapters.step_by.StepBy
      (core.iter.adapters.step_by.StepBy (core.slice.iter.Iter Nat)))
    (fuel : Nat := 100) : Result (List Nat) :=
  match fuel with
  | 0 => .ok []
  | fuel + 1 => do
    let (opt, sbi) ←
      (core.iter.traits.iterator.IteratorStepBy
        (core.iter.traits.iterator.IteratorStepBy
          (core.iter.traits.iterator.IteratorSliceIter Nat))).next sbi
    match opt with
    | none => .ok []
    | some x => do
      let rest ← collectNestedStepBy sbi fuel
      .ok (x :: rest)

#guard (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default
    (mkSliceIter [0, 1, 2, 3, 4, 5, 6, 7]) 2#usize
  let sbi2 ← core.iter.traits.iterator.Iterator.step_by.default sbi 2#usize
  collectNestedStepBy sbi2).reducesTo [0, 4]

-- ============================================================================
-- Step specs for SharedArray.into_iter and SharedSlice.into_iter
-- ============================================================================

namespace core.slice

@[step]
theorem SharedArray.into_iter.spec {T : Type _} {N : Usize} (a : Array T N) :
    SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter a
    ⦃ (iter : iter.Iter T) =>
      iter.slice.val = a.val ∧ iter.i = 0 ⦄ := by
  simp [SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, WP.spec_ok]

@[step]
theorem SharedSlice.into_iter.spec {T : Type _} (s : Slice T) :
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s
    ⦃ (iter : iter.Iter T) =>
      iter.slice = s ∧ iter.i = 0 ⦄ := by
  simp [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, WP.spec_ok]

/-- `<&mut [T; N] as IntoIterator>::into_iter`: the iterator ranges over the array from index `0`,
and the back function writes the iterator's slice back into the array. -/
@[step]
theorem MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter.spec
    {T : Type _} {N : Usize} (a : Array T N) :
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter a
    ⦃ (iter : iter.IterMut T) (back : core.slice.iter.IterMut T → Array T N) =>
      iter.slice.val = a.val ∧ iter.i = 0 ∧
      ∀ iter' : core.slice.iter.IterMut T, iter'.slice.length = N.val →
        (back iter').val = iter'.slice.val ⦄ := by
  simp only [MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter, WP.spec_ok]
  refine ⟨by simp, rfl, fun iter' h => Array.from_slice_val _ _ (by simpa using h)⟩

/-- `<IterMut<T> as Iterator>::next`, by cases on the returned element: `some x` is the element at
the current index, the index advances, and the back function writes a new value for that element;
`none` means the iterator is at the end. -/
@[step]
theorem iter.IteratorIterMut.next.spec {T : Type _} [Inhabited T] (it : iter.IterMut T) :
    iter.IteratorIterMut.next it ⦃ o it' back =>
      it'.slice = it.slice ∧ (∀ it'', back it'' none = it'') ∧
      match o with
      | some x => it.i < it.slice.length ∧ x = it.slice.val[it.i]! ∧ it'.i = it.i + 1 ∧
          ∀ it'' y, back it'' (some y) = { it'' with slice := it''.slice.setAtNat it.i y }
      | none => it.slice.length ≤ it.i ∧ it'.i = it.i ⦄ := by
  unfold iter.IteratorIterMut.next
  split
  · rename_i h
    have hi : it.i < it.slice.val.length := by simpa using h
    simp [hi, getElem!_pos]
    rfl
  · simp_all

/-- The body of the loop generated for `for x in it { *x = g(*x) }` over an `IterMut`. -/
def iter.IterMut.updateBody {T : Type _} (g : T → Result T) (it : iter.IterMut T)
    (back : iter.IterMut T → iter.IterMut T) :
    Result (ControlFlow (iter.IterMut T × (iter.IterMut T → iter.IterMut T)) (iter.IterMut T)) := do
  let (o, it1, next_back) ← iter.IteratorIterMut.next it
  match o with
  | none => ok (ControlFlow.done (let im := next_back it1 none
                                  back im))
  | some x =>
    let x1 ← g x
    ok (ControlFlow.cont (it1, fun im => let im1 := next_back im (some x1)
                                         back im1))

/-- Invariant of `IterMut.updateBody` loops over the slice `a`: the iterator ranges over `a`, and
the back function writes `P`-related values to the elements already visited and leaves the others
as they are. -/
private def iter.IterMut.UpdateInv {T : Type _} [Inhabited T] (a : Slice T)
    (P : Nat → T → T → Prop) (it : iter.IterMut T) (back : iter.IterMut T → iter.IterMut T) :
    Prop :=
  it.slice = a ∧ it.i ≤ a.length ∧
  ∀ it' : iter.IterMut T, it'.slice.length = a.length →
    (back it').slice.length = a.length ∧
    (∀ j < it.i, P j a.val[j]! (back it').slice.val[j]!) ∧
    (∀ j, it.i ≤ j → j < a.length → (back it').slice.val[j]! = it'.slice.val[j]!)

private theorem iter.IterMut.loop_updateBody.spec_gen {T : Type _} [Inhabited T]
    (g : T → Result T) (P : Nat → T → T → Prop) (a : Slice T)
    (hg : ∀ j < a.length, g a.val[j]! ⦃ y => P j a.val[j]! y ⦄)
    (it : iter.IterMut T) (back : iter.IterMut T → iter.IterMut T)
    (hinv : iter.IterMut.UpdateInv a P it back) :
    loop (fun (p : iter.IterMut T × (iter.IterMut T → iter.IterMut T)) =>
      iter.IterMut.updateBody g p.1 p.2) (it, back) ⦃ res =>
      res.slice.length = a.length ∧ ∀ j < a.length, P j a.val[j]! res.slice.val[j]! ⦄ := by
  apply loop.spec_decr_nat (fun p => a.length - p.1.i) (fun p => iter.IterMut.UpdateInv a P p.1 p.2)
    _ _ _ ?_ hinv
  rintro ⟨it, back⟩ ⟨hs, hi, hb⟩
  dsimp only at hs hi hb
  unfold iter.IterMut.updateBody
  apply WP.spec_bind (iter.IteratorIterMut.next.spec it)
  rintro ⟨o, it1, next_back⟩ ⟨hsl, hnone, ho⟩
  simp only [uncurry]
  cases o
  · -- `none`: every element has been visited
    obtain ⟨h1, h2, -⟩ := hb it1 (by rw [hsl, hs])
    simp only [WP.spec_ok, hnone]
    exact ⟨h1, fun j hj => h2 j (by rw [hs] at ho; agrind)⟩
  · -- `some x`: update the element; the invariant holds for the next iteration
    obtain ⟨hlt, rfl, hi1, hback⟩ := ho
    subst hs
    apply WP.spec_bind (hg it.i hlt)
    intro x1 hx1
    simp only [WP.spec_ok, hback]
    refine ⟨⟨hsl, by agrind, fun it' hl => ?_⟩, by agrind⟩
    obtain ⟨h1, h2, h3⟩ := hb { slice := it'.slice.setAtNat it.i x1, i := it'.i } (by simp [hl])
    have hset := fun j => Slice.getElem!_Nat_setAtNat it'.slice it.i j x1 (by simpa [hl] using hlt)
    refine ⟨h1, fun j hj => ?_, fun j hj hj' => ?_⟩
    · by_cases hji : j = it.i
      · subst hji
        rw [h3 _ (by agrind) (by simpa using hlt), hset]
        simpa using hx1
      · exact h2 j (by agrind)
    · rw [h3 j (by agrind) hj', hset]
      simp [show j ≠ it.i by agrind]

open Lean Elab Tactic Meta in
/-- The head constant of the left-hand side of `∀ xs, lhs = rhs`. -/
private meta def iterMutBodyName (tgt : Expr) : MetaM Name :=
  forallTelescope tgt fun _ e => do
    let some (_, lhs, _) := e.eq? | throwError "expected an equality"
    let .const n _ := lhs.getAppFn | throwError "expected a constant on the left"
    return n

/-- Proves that a generated loop body is `IterMut.updateBody g` (the body of
`for x in it { *x = g(*x) }`). Conditional writes (`if c { *x = v }`) are handled by splitting on
the condition, with `g` the corresponding `if`. -/
syntax (name := iterMutUpdateBody) "iter_mut_update_body" : tactic

open Lean Elab Tactic Meta in
@[tactic iterMutUpdateBody]
meta def evalIterMutUpdateBody : Tactic := fun _ => withMainContext do
  let id := mkIdent (← iterMutBodyName (← getMainTarget))
  evalTactic (← `(tactic|
    (intro it back; unfold $id:ident iter.IterMut.updateBody; fcongr 1;
     funext ⟨o, _, _⟩; cases o <;> first | rfl | (simp only [uncurry]; split <;> simp_all))))

/-- Loops generated for `for x in it { *x = g(*x) }` over a fresh `IterMut` (index `0`, no write
yet): every element `x` of the slice is replaced by a value `y` with `P j x y`, given a spec of `g`
with postcondition `P j x` for each element `x` at index `j`. `body` is the generated loop body; the
tactic `iter_mut_update_body` proves that it has the expected shape. -/
theorem iter.IterMut.loop_updateBody.spec {T : Type _} [Inhabited T]
    (g : T → Result T) (P : Nat → T → T → Prop)
    (body : iter.IterMut T → (iter.IterMut T → iter.IterMut T) →
      Result (ControlFlow (iter.IterMut T × (iter.IterMut T → iter.IterMut T)) (iter.IterMut T)))
    (it : iter.IterMut T) (hi : it.i = 0)
    (hg : ∀ j < it.slice.length, g it.slice.val[j]! ⦃ y => P j it.slice.val[j]! y ⦄)
    (hbody : ∀ it back, body it back = iter.IterMut.updateBody g it back := by
      iter_mut_update_body) :
    loop (fun (p : iter.IterMut T × (iter.IterMut T → iter.IterMut T)) => body p.1 p.2)
      (it, fun im => im) ⦃ res => res.slice.length = it.slice.length ∧
        ∀ j < it.slice.length, P j it.slice.val[j]! res.slice.val[j]! ⦄ := by
  simp only [hbody]
  exact iter.IterMut.loop_updateBody.spec_gen g P it.slice hg it _
    ⟨rfl, by simp [hi], fun it' hl => ⟨hl, by simp [hi], fun _ _ _ => rfl⟩⟩

end core.slice

end Aeneas.Std
