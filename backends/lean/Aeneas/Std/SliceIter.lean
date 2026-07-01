/- Arrays/Slices -/
import Aeneas.Std.Slice
import Aeneas.Std.Array.Array
import Aeneas.Std.Core.Iter

namespace Aeneas.Std

open Result Error core.ops.range WP

attribute [-simp] List.getElem!_eq_getElem?_getD


@[rust_type "core::slice::iter::Iter"]
structure core.slice.iter.Iter (T : Type) where
  /- We need to remember the slice and an index inside the slice (this is necessary)
     for double ended iterators) -/
  slice : Slice T
  i : Nat

@[rust_type "core::slice::iter::IterMut" (mutRegions := #[0]) (body := .opaque)]
structure core.slice.iter.IterMut (T : Type) where
  /- We need to remember the slice and an index inside the slice (this is necessary)
     for double ended iterators) -/
  slice : Slice T
  i : Nat := 0

@[rust_fun "core::slice::{[@T]}::iter"]
def core.slice.Slice.iter {T : Type} (s : Slice T) : Result (core.slice.iter.Iter T) :=
  ok ⟨ s, 0 ⟩

@[rust_fun "core::slice::{[@T]}::contains"]
def core.slice.Slice.contains {T : Type} (partialEqInst : core.cmp.PartialEq T T)
  (s : Slice T) (x : T) : Result Bool :=
  List.anyM (partialEqInst.eq x) s.val

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::next"]
def core.slice.iter.IteratorIterMut.next
  {T : Type}
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
def core.slice.Slice.iter_mut {T : Type} (slice : Slice T) :
  Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut T → Slice T)) :=
  ok ({slice}, fun it => it.slice)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::next"]
def core.slice.iter.IteratorSliceIter.next
  {T : Type} (it : core.slice.iter.Iter T) : Result ((Option T) × (core.slice.iter.Iter T)) :=
  if h : it.i < it.slice.len then
    let x := it.slice[it.i]
    let it := { it with i := it.i + 1}
    ok (some x, it)
  else ok (none, it)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::step_by"]
def core.slice.iter.IteratorSliceIter.step_by {T} (slice : core.slice.iter.Iter T) (steps : Usize) :
  Result (core.iter.adapters.step_by.StepBy (core.slice.iter.Iter T)) :=
  if steps.val = 0 then .fail .panic
  else ok (⟨ slice, steps ⟩)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::enumerate"]
def core.slice.iter.IteratorSliceIter.enumerate {T} (slice : core.slice.iter.Iter T) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T)) :=
  .ok { iter := slice, count := 0#usize }

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::take"]
def core.slice.iter.IteratorSliceIter.take {T} (slice : core.slice.iter.Iter T) (n : Usize) :
  Result (core.iter.adapters.take.Take (core.slice.iter.Iter T)) :=
  ok ⟨ slice, n ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>"]
def core.iter.traits.iterator.IteratorSliceIter (T : Type) :
  core.iter.traits.iterator.Iterator (core.slice.iter.Iter T) T := {
  next := core.slice.iter.IteratorSliceIter.next
  step_by := core.slice.iter.IteratorSliceIter.step_by
  enumerate := core.slice.iter.IteratorSliceIter.enumerate
  take := core.slice.iter.IteratorSliceIter.take
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
    {T : Type} {N : Usize} (a : Array T N) : Result (core.slice.iter.Iter T) :=
  ok ⟨ ⟨a.val, by scalar_tac⟩, 0 ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<&'a [@T; @N], &'a @T, core::slice::iter::Iter<'a, @T>>"]
def SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
    (T : Type) (N : Usize) :
    core.iter.traits.collect.IntoIterator (Array T N) T (core.slice.iter.Iter T) := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceIter T
  into_iter := SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
}

-- ============================================================================
-- IntoIterator for shared slice references: &[T] → Iter<T>
-- ============================================================================

/-- Model for `IntoIterator::into_iter` for `&[T]`.
Mirrors Rust: `(&[T]).into_iter()` returns an `Iter<T>` starting at index 0. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
    {T : Type} (s : Slice T) : Result (core.slice.iter.Iter T) :=
  ok ⟨ s, 0 ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, core::slice::iter::Iter<'a, @T>>"]
def SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
    (T : Type) :
    core.iter.traits.collect.IntoIterator (Slice T) T (core.slice.iter.Iter T) := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceIter T
  into_iter := SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
}

@[rust_type "core::slice::iter::ChunksExact" (body := .opaque)]
structure core.slice.iter.ChunksExact (T : Type) where
  chunks : List (Slice T)
  remainder : Slice T

@[rust_fun
  "core::slice::iter::{core::slice::iter::ChunksExact<'a, @T>}::remainder"]
def core.slice.iter.ChunksExact.getRemainder
  {T : Type} (self : core.slice.iter.ChunksExact T) : Result (Slice T) :=
  ok self.remainder

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::next"]
def core.slice.iter.IteratorChunksExact.next
  {T : Type} (self : core.slice.iter.ChunksExact T) :
  Result ((Option (Slice T)) × (core.slice.iter.ChunksExact T)) :=
  match self.chunks with
  | [] => ok (none, self)
  | chunk :: chunks => ok (some chunk, { chunks, remainder := self.remainder })

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::step_by"]
def core.slice.iter.IteratorChunksExact.step_by
  {T : Type} (self : slice.iter.ChunksExact T) (steps : Usize) :
  Result (core.iter.adapters.step_by.StepBy (slice.iter.ChunksExact T)) :=
  if steps.val = 0 then .fail .panic
  else ok (⟨ self, steps ⟩)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::enumerate"]
def core.slice.iter.IteratorChunksExact.enumerate {T : Type} (self : core.slice.iter.ChunksExact T) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact T)) :=
  .ok { iter := self, count := 0#usize }

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::take"]
def core.slice.iter.IteratorChunksExact.take {T : Type} (self : core.slice.iter.ChunksExact T) (n : Usize) :
  Result (core.iter.adapters.take.Take (core.slice.iter.ChunksExact T)) :=
  ok ⟨ self, n ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>"]
def core.iter.traits.iterator.IteratorChunksExact (T : Type) :
  core.iter.traits.iterator.Iterator (core.slice.iter.ChunksExact T) (Slice T)
  := {
  next := core.slice.iter.IteratorChunksExact.next
  step_by := core.slice.iter.IteratorChunksExact.step_by
  enumerate := core.slice.iter.IteratorChunksExact.enumerate
  take := core.slice.iter.IteratorChunksExact.take
}

-- ============================================================================
-- `rev` / `zip` for slice `Iter<T>` and `ChunksExact<T>`
-- ============================================================================

/-- `Iter<T>::rev`: `Rev { iter: self }`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::rev"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorShared.rev
  {T Item : Type}
  (_DEInst : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.Iter T) Item) :
  core.slice.iter.Iter T → Result (core.iter.adapters.rev.Rev (core.slice.iter.Iter T)) :=
  fun self => ok ⟨self⟩

/-- `Iter<T>::zip`: `Zip::new(self, other.into_iter())`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::zip"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorShared.zip
  {T U Item IntoIter : Type}
  (IntoIterInst : core.iter.traits.collect.IntoIterator U Item IntoIter) :
  core.slice.iter.Iter T → U →
    Result (core.iter.adapters.zip.Zip (core.slice.iter.Iter T) IntoIter) :=
  fun self other => do
    let b ← IntoIterInst.into_iter other
    ok ⟨self, b⟩

/-- `ChunksExact<T>::rev`: `Rev { iter: self }`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::rev"]
def core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedSlice.rev
  {T Item : Type}
  (_DEInst : core.iter.traits.double_ended.DoubleEndedIterator
    (core.slice.iter.ChunksExact T) Item) :
  core.slice.iter.ChunksExact T →
    Result (core.iter.adapters.rev.Rev (core.slice.iter.ChunksExact T)) :=
  fun self => ok ⟨self⟩

/-- `ChunksExact<T>::zip`: `Zip::new(self, other.into_iter())`. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::zip"]
def core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedSlice.zip
  {T U Item IntoIter : Type}
  (IntoIterInst : core.iter.traits.collect.IntoIterator U Item IntoIter) :
  core.slice.iter.ChunksExact T → U →
    Result (core.iter.adapters.zip.Zip (core.slice.iter.ChunksExact T) IntoIter) :=
  fun self other => do
    let b ← IntoIterInst.into_iter other
    ok ⟨self, b⟩

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
def core.slice.Slice.chunks_exact {T : Type} (s : Slice T) (chunk_size : Std.Usize) :
  Result (core.slice.iter.ChunksExact T) :=
  if hcs : chunk_size.val > 0 then
    let result := List.toChunksExact chunk_size.val hcs s.val
    let sliceChunks := result.1.attach.map fun ⟨c, hc⟩ => ⟨c, by
        have := List.toChunksExact_chunk_length hcs s.val c hc
        scalar_tac⟩
    ok { chunks := sliceChunks,
         remainder := ⟨result.2, by
           have := List.toChunksExact_remainder_length hcs s.val
           scalar_tac⟩ }
  else fail .panic


-- ============================================================================
-- StepBy tests
-- ============================================================================

private def mkSliceIter (l : List Nat) (h : l.length ≤ Usize.max := by scalar_tac) :
    core.slice.iter.Iter Nat :=
  { slice := ⟨l, h⟩, i := 0 }

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
#assert
  match core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [1, 2, 3]) 0#usize with
  | .fail .panic => true
  | _ => false

-- step_by(1) returns all elements
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2, 3, 4]) 1#usize
  collectStepBy sbi) == .ok [0, 1, 2, 3, 4]

-- step_by(2) returns every other element
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2, 3, 4]) 2#usize
  collectStepBy sbi) == .ok [0, 2, 4]

-- step_by(3)
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2, 3, 4, 5, 6]) 3#usize
  collectStepBy sbi) == .ok [0, 3, 6]

-- step_by larger than collection: returns only first element
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2]) 10#usize
  collectStepBy sbi) == .ok [0]

-- step_by on empty iterator
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter []) 2#usize
  collectStepBy sbi) == .ok []

-- step_by(1) on single element
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [42]) 1#usize
  collectStepBy sbi) == .ok [42]

-- step_by(2) on single element
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [42]) 2#usize
  collectStepBy sbi) == .ok [42]

-- step_by equal to length: returns only first element
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2]) 3#usize
  collectStepBy sbi) == .ok [0]

-- step_by = length - 1
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2]) 2#usize
  collectStepBy sbi) == .ok [0, 2]

-- step_by(2) on two elements: returns only first
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1]) 2#usize
  collectStepBy sbi) == .ok [0]

-- step_by(2) on three elements: returns first and third
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by (mkSliceIter [0, 1, 2]) 2#usize
  collectStepBy sbi) == .ok [0, 2]

-- step_by(4) on longer sequence
#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by
    (mkSliceIter [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) 4#usize
  collectStepBy sbi) == .ok [0, 4, 8]

-- Verify that step_by(0) on the generic Iterator.step_by.default also panics
#assert
  match core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [1]) 0#usize with
  | .fail .panic => true
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

#assert (do
  let sbi ← core.slice.iter.IteratorSliceIter.step_by
    (mkSliceIter [0, 1, 2, 3, 4, 5, 6, 7]) 2#usize
  let sbi2 ← core.iter.adapters.step_by.IteratorStepBy.step_by
    (core.iter.traits.iterator.IteratorSliceIter Nat) sbi 2#usize
  collectNestedStepBy sbi2) == .ok [0, 4]

-- ============================================================================
-- Step specs for SharedArray.into_iter and SharedSlice.into_iter
-- ============================================================================

@[step]
theorem SharedArray.into_iter.spec {T : Type} {N : Usize} (a : Array T N) :
    SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter a
    ⦃ (iter : core.slice.iter.Iter T) =>
      iter.slice.val = a.val ∧ iter.i = 0 ⦄ := by
  simp [SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, WP.spec_ok]

@[step]
theorem SharedSlice.into_iter.spec {T : Type} (s : Slice T) :
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s
    ⦃ (iter : core.slice.iter.Iter T) =>
      iter.slice = s ∧ iter.i = 0 ⦄ := by
  simp [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, WP.spec_ok]
end Aeneas.Std
