/- `core::option::IntoIter`: the iterator that `Option::into_iter` returns -/
module
public import Aeneas.Std.Core.Iter
public section

namespace Aeneas.Std

open Result WP

/-- `option::IntoIter<A>` holds the `Option<A>` that is still to be yielded. -/
@[expose, rust_type "core::option::IntoIter"]
def core.option.IntoIter (A : Type u) : Type u := Option A

/-- `Option::into_iter`: an iterator over the payload of `some`, empty on `none`. -/
@[expose, rust_fun
  "core::option::{core::iter::traits::collect::IntoIterator<core::option::Option<@T>, @T, core::option::IntoIter<@T>>}::into_iter"]
def core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  {T : Type _} (x : Option T) : Result (core.option.IntoIter T) :=
  ok x

/-- `option::IntoIter::next`: yields the payload once, then `none`. -/
@[expose, rust_fun
  "core::option::{core::iter::traits::iterator::Iterator<core::option::IntoIter<@A>, @A>}::next"]
def core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  {A : Type _} (it : core.option.IntoIter A) :
  Result ((Option A) × (core.option.IntoIter A)) :=
  ok (it, none)

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::option::IntoIter<@A>, @A>"]
impl_def core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator (A : Type _) :
  core.iter.traits.iterator.Iterator (core.option.IntoIter A) A := {
  next := core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator A)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator A)
  take := core.iter.traits.iterator.Iterator.take.trait_default
    (core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator A)
}

@[expose, reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<core::option::Option<@T>, @T, core::option::IntoIter<@T>>"]
def core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter (T : Type _) :
  core.iter.traits.collect.IntoIterator (Option T) T (core.option.IntoIter T) := {
  iteratorInst := core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator T
  into_iter :=
    core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
}

@[step]
theorem core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter.spec
    {T : Type _} (x : Option T) :
    core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter x
    ⦃ it => it = x ⦄ := by
  unfold core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  exact (WP.spec_ok _).2 rfl

/-- The first call yields the payload, and the iterator is then exhausted. -/
@[step]
theorem core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator.next.spec
    {A : Type _} (it : core.option.IntoIter A) :
    core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator.next it
    ⦃ r => r = (it, none) ⦄ := by
  simp only [core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator.next, WP.spec_ok]
  rfl

end Aeneas.Std
