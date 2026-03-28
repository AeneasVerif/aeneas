import Aeneas.Std.Core.Iter
import Aeneas.Std.Vec

namespace Aeneas.Std

open Result

@[rust_type "alloc::vec::into_iter::IntoIter" (keepParams := [true, false])]
def alloc.vec.into_iter.IntoIter (T : Type) : Type := alloc.vec.Vec T

@[rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::next"
  (keepParams := [true, false])]
def alloc.vec.into_iter.IteratorIntoIter.next {T : Type} (it: alloc.vec.into_iter.IntoIter T) :
  Result ((Option T) × (alloc.vec.into_iter.IntoIter T)) :=
  match it with
  | ⟨ [], _ ⟩  => ok (none, it)
  | ⟨ hd :: tl, _ ⟩ => ok (hd, ⟨ tl, by scalar_tac ⟩ )

@[rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::step_by"
  (keepParams := [true, false])]
def alloc.vec.into_iter.IteratorIntoIter.step_by {T : Type} (it: alloc.vec.into_iter.IntoIter T) (steps : Usize) :
  Result (core.iter.adapters.step_by.StepBy (alloc.vec.into_iter.IntoIter T)) :=
  if steps.val = 0 then .fail .panic
  else .ok ⟨ it, steps ⟩

@[rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::enumerate"
  (keepParams := [true, false])]
def alloc.vec.into_iter.IteratorIntoIter.enumerate {T : Type} (it: alloc.vec.into_iter.IntoIter T) :
  Result (core.iter.adapters.enumerate.Enumerate (alloc.vec.into_iter.IntoIter T)) :=
  .ok { iter := it, count := 0#usize }

@[rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::take"
  (keepParams := [true, false])]
def alloc.vec.into_iter.IteratorIntoIter.take {T : Type} (it: alloc.vec.into_iter.IntoIter T) (n : Usize) :
  Result (core.iter.adapters.take.Take (alloc.vec.into_iter.IntoIter T)) :=
  .ok ⟨ it, n ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>"
  (keepParams := [true, false])]
def core.iter.traits.iterator.IteratorVecIntoIter (T : Type) :
  core.iter.traits.iterator.Iterator (alloc.vec.into_iter.IntoIter T) T := {
  next := alloc.vec.into_iter.IteratorIntoIter.next
  step_by := alloc.vec.into_iter.IteratorIntoIter.step_by
  enumerate := alloc.vec.into_iter.IteratorIntoIter.enumerate
  take := alloc.vec.into_iter.IteratorIntoIter.take
}

@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<alloc::vec::Vec<@T>, @T, alloc::vec::into_iter::IntoIter<@T, @A>>}::into_iter"
  (keepParams := [true, false])]
def alloc.vec.IntoIteratorVec.into_iter {T : Type} (v: alloc.vec.Vec T) : Result (alloc.vec.into_iter.IntoIter T) := ok v

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<alloc::vec::Vec<@T>, @T, alloc::vec::into_iter::IntoIter<@T, @A>>"
  (keepParams := [true, false])]
def core.iter.traits.collect.IntoIteratorVec (T : Type) :
  core.iter.traits.collect.IntoIterator (alloc.vec.Vec T) T
  (alloc.vec.into_iter.IntoIter T) := {
  iteratorInst := core.iter.traits.iterator.IteratorVecIntoIter T
  into_iter := alloc.vec.IntoIteratorVec.into_iter
}

/-- Iterate and collect elements into a list -/
def alloc.vec.FromIteratorVec.iterToList
    {T : Type} {IntoIter : Type}
    (iterInst : core.iter.traits.iterator.Iterator IntoIter T)
    (iter : IntoIter) (acc : List T) : Result (List T) := do
  let (opt, iter) ← iterInst.next iter
  match opt with
  | none => .ok acc.reverse
  | some item => alloc.vec.FromIteratorVec.iterToList iterInst iter (item :: acc)
partial_fixpoint

@[rust_fun
  "alloc::vec::{core::iter::traits::collect::FromIterator<alloc::vec::Vec<@T>, @T>}::from_iter"]
def alloc.vec.FromIteratorVec.from_iter
  {T : Type} {I : Type} {IntoIter : Type}
  (IntoIteratorInst : core.iter.traits.collect.IntoIterator I T IntoIter) :
  I → Result (alloc.vec.Vec T) :=
  fun input => do
    let iter ← IntoIteratorInst.into_iter input
    let list ← alloc.vec.FromIteratorVec.iterToList IntoIteratorInst.iteratorInst iter []
    if h : list.length ≤ Usize.max then .ok ⟨ list, h ⟩
    else .fail .panic

@[reducible, rust_trait_impl
  "core::iter::traits::collect::FromIterator<alloc::vec::Vec<@T>, @T>"]
def core.iter.traits.collect.FromIteratorVec (T : Type) :
  core.iter.traits.collect.FromIterator (alloc.vec.Vec T) T := {
  from_iter := fun {I : Type} {IntoIter : Type}
    (IntoIteratorInst : core.iter.traits.collect.IntoIterator I T IntoIter) =>
    alloc.vec.FromIteratorVec.from_iter IntoIteratorInst
}

@[rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::map"]
def alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.map
  {T : Type} {A : Type} {F : Type}
  (_FnMutInst : core.ops.function.FnMut F T A) :
  alloc.vec.into_iter.IntoIter T → F →
  Result (core.iter.adapters.map.Map (alloc.vec.into_iter.IntoIter T) F) :=
  fun it f => .ok ⟨ it, f ⟩


end Aeneas.Std
