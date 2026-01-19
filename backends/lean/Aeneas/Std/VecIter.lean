import Aeneas.Std.Core.Iter

namespace Aeneas.Std

open Result

@[rust_type "alloc::vec::into_iter::IntoIter" (keepParams := [true, false])]
def alloc.vec.into_iter.IntoIter (T : Type) : Type := alloc.vec.Vec T

@[rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::next"
  -canFail (keepParams := [true, false])]
def alloc.vec.into_iter.IteratorIntoIter.next {T : Type} (it: alloc.vec.into_iter.IntoIter T) :
  Result ((Option T) × (alloc.vec.into_iter.IntoIter T)) :=
  match it with
  | ⟨ [], _ ⟩  => ok (none, it)
  | ⟨ hd :: tl, _ ⟩ => ok (hd, ⟨ tl, by scalar_tac ⟩ )

@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<alloc::vec::Vec<@T>, @T, alloc::vec::into_iter::IntoIter<@T, @A>>}::into_iter"
  -canFail (keepParams := [true, false])]
def alloc.vec.IntoIteratorVec.into_iter {T : Type} (v: alloc.vec.Vec T) : Result (alloc.vec.into_iter.IntoIter T) := ok v

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>"
  (keepParams := [true, false])]
def core.iter.traits.iterator.IteratorVecIntoIter (T : Type) :
  core.iter.traits.iterator.Iterator (alloc.vec.into_iter.IntoIter T) T := {
  next := alloc.vec.into_iter.IteratorIntoIter.next
}

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<alloc::vec::Vec<@T>, @T, alloc::vec::into_iter::IntoIter<@T, @A>>"
  (keepParams := [true, false])]
def core.iter.traits.collect.IntoIteratorVec (T : Type) :
  core.iter.traits.collect.IntoIterator (alloc.vec.Vec T) T
  (alloc.vec.into_iter.IntoIter T) := {
  iteratorInst := core.iter.traits.iterator.IteratorVecIntoIter T
  into_iter := alloc.vec.IntoIteratorVec.into_iter
}

end Aeneas.Std
