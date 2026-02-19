/- Arrays/Slices -/
import Aeneas.Std.Slice
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
  ok (⟨ slice, steps ⟩)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::enumerate"]
def core.slice.iter.IteratorSliceIter.enumerate {T} (slice : core.slice.iter.Iter T) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T)) :=
  sorry

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

@[rust_type "core::slice::iter::ChunksExact" (body := .opaque)]
structure core.slice.iter.ChunksExact (T : Type) where
  chunks : List (Slice T)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::next"]
def core.slice.iter.IteratorChunksExact.next
  {T : Type} (self : core.slice.iter.ChunksExact T) :
  Result ((Option (Slice T)) × (core.slice.iter.ChunksExact T)) :=
  match self.chunks with
  | [] => ok (none, self)
  | chunk :: chunks => ok (some chunk, { chunks })

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::step_by"]
def core.slice.iter.IteratorChunksExact.step_by
  {T : Type} (self : slice.iter.ChunksExact T) (steps : Usize) :
  Result (core.iter.adapters.step_by.StepBy (slice.iter.ChunksExact T)) :=
  ok (⟨ self, steps ⟩)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::enumerate"]
def core.slice.iter.IteratorChunksExact.enumerate {T : Type} (self : core.slice.iter.ChunksExact T) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact T)) :=
  sorry

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

@[rust_fun "core::slice::{[@T]}::chunks_exact"]
def core.slice.Slice.chunks_exact {T : Type} (s : Slice T) (chunk_size : Std.Usize) :
  Result (core.slice.iter.ChunksExact T) :=
  if chunk_size.val > 0 && s.len % chunk_size.val = 0 then
    ok ⟨ List.map (fun s => ⟨ s, by sorry ⟩) (s.val.toChunks chunk_size.val) ⟩
  else fail .panic


end Aeneas.Std
