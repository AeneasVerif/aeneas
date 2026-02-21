import Aeneas.Std.Core.Cmp
import Aeneas.Std.Primitives
import Aeneas.Std.Range
import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Notations
import Aeneas.Std.Scalar.CloneCopy
import Aeneas.Std.Scalar.EqOrd
import Aeneas.Std.Scalar.CheckedOps
import Aeneas.Std.Core.Core

namespace Aeneas.Std

@[rust_trait "core::iter::range::Step"
  (parentClauses := ["cloneInst", "partialOrdInst"])]
structure core.iter.range.Step (Self : Type) where
  cloneInst : core.clone.Clone Self
  partialOrdInst : core.cmp.PartialOrd Self Self
  steps_between : Self → Self → Result (Usize × (Option Usize))
  forward_checked : Self → Usize → Result (Option Self)
  backward_checked : Self → Usize → Result (Option Self)

open Result

@[rust_trait "core::iter::adapters::zip::TrustedRandomAccessNoCoerce"
  (consts := ["MAY_HAVE_SIDE_EFFECT"])]
structure core.iter.adapters.zip.TrustedRandomAccessNoCoerce (Self : Type u)
  where
  MAY_HAVE_SIDE_EFFECT : Bool

@[rust_type "core::iter::adapters::step_by::StepBy" (body := .opaque)]
structure core.iter.adapters.step_by.StepBy (I : Type u) where
  iter : I
  /- This is not exactly the way the implementation is defined in the standard library, but this is a good model -/
  step_by : Usize

@[rust_type "core::iter::adapters::enumerate::Enumerate"]
structure core.iter.adapters.enumerate.Enumerate (I : Type u) where
  iter : I
  count : Usize

@[rust_type "core::iter::adapters::take::Take"]
structure core.iter.adapters.take.Take (I : Type u) where
  iter : I
  n : Usize

@[rust_type "core::iter::adapters::rev::Rev"]
structure core.iter.adapters.rev.Rev (T : Type u) where
  iter : T

@[rust_trait "core::iter::traits::iterator::Iterator"]
structure core.iter.traits.iterator.Iterator (Self : Type) (Self_Item : Type)
  where
  next : Self → Result ((Option Self_Item) × Self)
  step_by : Self → Usize → Result (core.iter.adapters.step_by.StepBy Self)
  enumerate : Self → Result (core.iter.adapters.enumerate.Enumerate Self)
  take : Self → Usize → Result (core.iter.adapters.take.Take Self)
  -- rev : Self → Result (core.iter.adapters.rev.Rev Self) -- requires DoubleEndedIterator, leading to circularity
  -- TODO: collect

@[rust_fun "core::iter::traits::iterator::Iterator::step_by"]
def core.iter.traits.iterator.Iterator.step_by.default
  {Self : Type} (self: Self) (step_by : Std.Usize) :
  Result (core.iter.adapters.step_by.StepBy Self) := .ok ⟨ self, step_by ⟩

@[rust_fun
  "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, @Clause0_Item>}::next"]
def core.iter.adapters.step_by.IteratorStepBy.next
  {I : Type} {Item : Type}
  (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
  core.iter.adapters.step_by.StepBy I →
  Result ((Option Item) × (core.iter.adapters.step_by.StepBy I)) :=
  sorry -- TODO

@[rust_fun
  "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, @Clause0_Item>}::step_by"]
def core.iter.adapters.step_by.IteratorStepBy.step_by
  {I : Type} {Item : Type}
  (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
  core.iter.adapters.step_by.StepBy I → Std.Usize →
  Result (core.iter.adapters.step_by.StepBy (core.iter.adapters.step_by.StepBy I)) := by
  sorry -- TODO

@[rust_fun
  "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, @Clause0_Item>}::enumerate"]
def core.iter.adapters.step_by.IteratorStepBy.enumerate
  {I : Type} {Item : Type}
  (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
  core.iter.adapters.step_by.StepBy I →
  Result (core.iter.adapters.enumerate.Enumerate (core.iter.adapters.step_by.StepBy I)) := by
  sorry -- TODO

@[rust_fun
  "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, @Clause0_Item>}::take"]
def core.iter.adapters.step_by.IteratorStepBy.take
  {I : Type} {Item : Type}
  (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
  core.iter.adapters.step_by.StepBy I → Std.Usize →
  Result (core.iter.adapters.take.Take (core.iter.adapters.step_by.StepBy I)) := by
  sorry -- TODO

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, @Clause0_Item>"]
def core.iter.traits.iterator.IteratorStepBy {I : Type} {Item : Type}
  (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
  core.iter.traits.iterator.Iterator (core.iter.adapters.step_by.StepBy I) Item := {
  next := core.iter.adapters.step_by.IteratorStepBy.next IteratorInst
  step_by := core.iter.adapters.step_by.IteratorStepBy.step_by IteratorInst
  enumerate := core.iter.adapters.step_by.IteratorStepBy.enumerate IteratorInst
  take := core.iter.adapters.step_by.IteratorStepBy.take IteratorInst
}

@[rust_trait "core::iter::traits::accum::Sum"]
structure core.iter.traits.accum.Sum (Self : Type) (A : Type) where
  sum : forall {I : Type} (_ : core.iter.traits.iterator.Iterator I A), I → Result Self

@[rust_trait "core::iter::traits::accum::Product"]
structure core.iter.traits.accum.Product (Self : Type) (A : Type) where
  product : forall {I : Type} (_ : core.iter.traits.iterator.Iterator I A), I → Result Self

@[rust_trait "core::iter::traits::collect::IntoIterator"
  (parentClauses := ["iteratorInst"])]
structure core.iter.traits.collect.IntoIterator (Self : Type) (Item :
  Type) (IntoIter : Type) where
  iteratorInst : core.iter.traits.iterator.Iterator IntoIter Item
  into_iter : Self → Result IntoIter

@[rust_trait "core::iter::traits::collect::FromIterator"]
structure core.iter.traits.collect.FromIterator (Self : Type) (A : Type) where
  from_iter : forall {T : Type} {IntoIter : Type}
    (_ : core.iter.traits.collect.IntoIterator T A IntoIter),
    T → Result Self

@[rust_fun "core::iter::traits::iterator::Iterator::collect"]
def core.iter.traits.iterator.Iterator.collect.default
  {Self : Type} {B : Type} {Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Item)
  (collectFromIteratorInst : core.iter.traits.collect.FromIterator B Item) :
  Self → Result B := sorry

@[rust_fun
  "core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<@I, @Item, @I>}::into_iter",
  simp]
def core.iter.traits.collect.IntoIterator.Blanket.into_iter
  {I : Type} {Item : Type} (_ : core.iter.traits.iterator.Iterator I Item) :
  I → Result I :=
    λ x => ok x

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<@I, @Item, @I>"]
def core.iter.traits.collect.IntoIterator.Blanket {I : Type} {Item : Type}
  (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
    core.iter.traits.collect.IntoIterator I Item I := {
  iteratorInst := IteratorInst
  into_iter := core.iter.traits.collect.IntoIterator.Blanket.into_iter IteratorInst
}

@[rust_trait "core::iter::traits::collect::Extend"]
structure core.iter.traits.collect.Extend (Self : Type) (A : Type) where
  extend : forall {T : Type} {IntoIter : Type}
    (_ : core.iter.traits.collect.IntoIterator T A IntoIter), Self → T → Result Self

@[rust_trait "core::iter::traits::double_ended::DoubleEndedIterator"
  (parentClauses := ["iteratorInst"])]
structure core.iter.traits.double_ended.DoubleEndedIterator (Self : Type) (Item : Type) where
  iteratorInst : core.iter.traits.iterator.Iterator Self Item
  next_back : Self → Result ((Option Item) × Self)

@[rust_trait "core::iter::traits::exact_size::ExactSizeIterator"
  (parentClauses := ["iteratorInst"])]
structure core.iter.traits.exact_size.ExactSizeIterator (Self : Type) (Item : Type) where
  iteratorInst : core.iter.traits.iterator.Iterator Self Item

@[rust_fun
  "core::iter::range::{core::iter::range::Step<usize>}::steps_between"]
def core.iter.range.StepUsize.steps_between
  : Usize → Usize → Result (Usize × (Option Usize)) :=
  λ start end_ =>
    if h: start > end_ then ok ⟨ 0#usize, none ⟩ else
      let steps := Usize.ofNatCore (end_.val - start.val) (by scalar_tac)
      ok ⟨ steps, some steps ⟩

@[rust_fun
  "core::iter::range::{core::iter::range::Step<usize>}::forward_checked"]
def core.iter.range.StepUsize.forward_checked
  : Usize → Usize → Result (Option Usize) :=
  λ start n => ok (Usize.checked_add start n)

@[rust_fun
  "core::iter::range::{core::iter::range::Step<usize>}::backward_checked"]
def core.iter.range.StepUsize.backward_checked
  : Usize → Usize → Result (Option Usize) :=
  λ start n => ok (Usize.checked_sub start n)

@[reducible, rust_trait_impl "core::iter::range::Step<usize>"]
def core.iter.range.StepUsize : core.iter.range.Step Usize := {
  cloneInst := core.clone.CloneUsize
  partialOrdInst := core.cmp.PartialOrdUsize
  steps_between := core.iter.range.StepUsize.steps_between
  forward_checked := core.iter.range.StepUsize.forward_checked
  backward_checked := core.iter.range.StepUsize.backward_checked
}

@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::next"]
def core.iter.range.IteratorRange.next
   {A : Type} (StepInst : core.iter.range.Step A) :
  core.ops.range.Range A → Result ((Option A) × (core.ops.range.Range A)) :=
  λ range => do
    let cmp ← StepInst.partialOrdInst.lt range.start range.end;
    if cmp then
      let range' ← StepInst.cloneInst.clone range.start;
      let n ← StepInst.forward_checked range' 1#usize;
      match n with
      | none => fail .panic -- Step invariants not upheld
      | some n => ok ⟨ some range', {range with start := n} ⟩
    else ok ⟨ none, range ⟩

@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::step_by"]
def core.iter.range.IteratorRange.step_by
   {A : Type} (_StepInst : core.iter.range.Step A) :
  core.ops.range.Range A → Usize → Result (adapters.step_by.StepBy (ops.range.Range A)) :=
  λ range step_by => .ok ⟨ range, step_by ⟩

@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::enumerate"]
def core.iter.range.IteratorRange.enumerate
   {A : Type} (_StepInst : core.iter.range.Step A)
  (range : core.ops.range.Range A) : Result (adapters.enumerate.Enumerate (ops.range.Range A)) :=
  .ok { iter := range, count := 0#usize }

@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::take"]
def core.iter.range.IteratorRange.take
   {A : Type} (_StepInst : core.iter.range.Step A)
  (iter : core.ops.range.Range A) (n : Usize) : Result (adapters.take.Take (ops.range.Range A)) :=
  .ok { iter, n }

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>"]
def core.iter.traits.iterator.IteratorRange {A : Type}
  (StepInst : core.iter.range.Step A) : core.iter.traits.iterator.Iterator
  (core.ops.range.Range A) A := {
  next := core.iter.range.IteratorRange.next StepInst
  step_by := core.iter.range.IteratorRange.step_by StepInst
  enumerate := core.iter.range.IteratorRange.enumerate StepInst
  take := core.iter.range.IteratorRange.take StepInst
}

@[rust_type "core::iter::adapters::map::Map"]
structure core.iter.adapters.map.Map (I : Type u) (F : Type v) where
  iter : I
  f : F
