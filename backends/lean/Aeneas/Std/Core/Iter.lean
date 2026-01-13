import Aeneas.Std.Core.Cmp
import Aeneas.Std.Primitives
import Aeneas.Std.Range
import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.CheckedOps
import Aeneas.Std.Scalar.Notations

namespace Aeneas.Std

@[rust_trait "core::iter::range::Step"
  (parentClauses := ["cloneCloneInst", "cmpPartialOrdInst"])]
structure core.iter.range.Step (Self : Type) where
  cloneCloneInst : core.clone.Clone Self
  cmpPartialOrdInst : core.cmp.PartialOrd Self Self
  steps_between : Self → Self → Result (Usize × (Option Usize))
  forward_checked : Self → Usize → Result (Option Self)
  backward_checked : Self → Usize → Result (Option Self)

open Result

@[rust_trait "core::iter::adapters::zip::TrustedRandomAccessNoCoerce"
  (consts := ["MAY_HAVE_SIDE_EFFECT"])]
structure core.iter.adapters.zip.TrustedRandomAccessNoCoerce (Self : Type)
  where
  MAY_HAVE_SIDE_EFFECT : Bool

@[rust_trait "core::iter::traits::iterator::Iterator"]
structure core.iter.traits.iterator.Iterator (Self : Type) (Self_Item : Type)
  where
  next : Self → Result ((Option Self_Item) × Self)


@[rust_trait "core::iter::traits::accum::Sum"]
structure core.iter.traits.accum.Sum (Self : Type) (A : Type) where
  sum : forall {I : Type} (_ : core.iter.traits.iterator.Iterator I A), I → Result Self

@[rust_trait "core::iter::traits::accum::Product"]
structure core.iter.traits.accum.Product (Self : Type) (A : Type) where
  product : forall {I : Type} (_ : core.iter.traits.iterator.Iterator I A), I → Result Self

@[rust_trait "core::iter::traits::collect::IntoIterator"
  (parentClauses := ["iteratorIteratorInst"])]
structure core.iter.traits.collect.IntoIterator (Self : Type) (Self_Item :
  Type) (Self_IntoIter : Type) where
  iteratorIteratorInst : core.iter.traits.iterator.Iterator Self_IntoIter
    Self_Item
  into_iter : Self → Result Self_IntoIter

@[rust_trait "core::iter::traits::collect::FromIterator"]
structure core.iter.traits.collect.FromIterator (Self : Type) (A : Type) where
  from_iter : forall {T : Type} {Clause0_IntoIter : Type}
    (_ : core.iter.traits.collect.IntoIterator T A Clause0_IntoIter), T → Result
    Self

@[rust_fun
  "core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<@I, @Clause0_Item, @I>}::into_iter"]
def core.iter.traits.collect.IntoIterator.Blanket.into_iter
  {I : Type} {Clause0_Item : Type} (_ : core.iter.traits.iterator.Iterator I Clause0_Item) :
  I → Result I :=
    λ x => ok x

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<@I, @Clause0_Item, @I>"]
def core.iter.traits.collect.IntoIterator.Blanket {I : Type} {Clause0_Item :
  Type} (iteratorIteratorInst : core.iter.traits.iterator.Iterator I
  Clause0_Item) : core.iter.traits.collect.IntoIterator I Clause0_Item I := {
  iteratorIteratorInst := iteratorIteratorInst
  into_iter := core.iter.traits.collect.IntoIterator.Blanket.into_iter
    iteratorIteratorInst
}

@[rust_trait "core::iter::traits::collect::Extend"]
structure core.iter.traits.collect.Extend (Self : Type) (A : Type) where
  extend : forall {T : Type} {Clause0_IntoIter : Type}
    (_ : core.iter.traits.collect.IntoIterator T A Clause0_IntoIter), Self → T →
    Result Self

@[rust_trait "core::iter::traits::double_ended::DoubleEndedIterator"
  (parentClauses := ["iteratorIteratorInst"])]
structure core.iter.traits.double_ended.DoubleEndedIterator (Self : Type)
  (Self_Clause0_Item : Type) where
  iteratorIteratorInst : core.iter.traits.iterator.Iterator Self
    Self_Clause0_Item
  next_back : Self → Result ((Option Self_Clause0_Item) × Self)

@[rust_trait "core::iter::traits::exact_size::ExactSizeIterator"
  (parentClauses := ["iteratorIteratorInst"])]
structure core.iter.traits.exact_size.ExactSizeIterator (Self : Type)
  (Self_Clause0_Item : Type) where
  iteratorIteratorInst : core.iter.traits.iterator.Iterator Self
    Self_Clause0_Item

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
  cloneCloneInst := core.clone.CloneUsize
  cmpPartialOrdInst := core.cmp.PartialOrdUsize
  steps_between := core.iter.range.StepUsize.steps_between
  forward_checked := core.iter.range.StepUsize.forward_checked
  backward_checked := core.iter.range.StepUsize.backward_checked
}

@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::next"]
def core.iter.range.IteratorcoreopsrangeRangeA.next
   {A : Type} (StepInst : core.iter.range.Step A) :
  core.ops.range.Range A → Result ((Option A) × (core.ops.range.Range A)) :=
  λ range => do
    let cmp ← StepInst.cmpPartialOrdInst.lt range.start range.end_;
    if cmp then
      let range' ← StepInst.cloneCloneInst.clone range.start;
      let n ← StepInst.forward_checked range' 1#usize;
      match n with
      | none => fail .panic -- Step invariants not upheld
      | some n => ok ⟨ some n, {range with start := n} ⟩
    else ok ⟨ none, range ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>"]
def core.iter.traits.iterator.IteratorRangeA {A : Type} (StepInst :
  core.iter.range.Step A) : core.iter.traits.iterator.Iterator
  (core.ops.range.Range A) A := {
  next := core.iter.range.IteratorcoreopsrangeRangeA.next StepInst
}
