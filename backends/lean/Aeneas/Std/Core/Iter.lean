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
  Result (core.iter.adapters.step_by.StepBy Self) :=
  if step_by.val = 0 then .fail .panic
  else .ok ⟨ self, step_by ⟩

@[rust_fun "core::iter::traits::iterator::Iterator::enumerate"]
def core.iter.traits.iterator.Iterator.enumerate.default
  {Self : Type} (self: Self) :
  Result (core.iter.adapters.enumerate.Enumerate Self) :=
  .ok { iter := self, count := 0#usize }

@[rust_fun "core::iter::traits::iterator::Iterator::take"]
def core.iter.traits.iterator.Iterator.take.default
  {Self : Type} (self: Self) (n : Std.Usize) :
  Result (core.iter.adapters.take.Take Self) :=
  .ok ⟨ self, n ⟩

/-- Skip up to `n` elements from an iterator -/
def core.iter.adapters.step_by.skipN
    {I : Type} {Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator I Item)
    (iter : I) : (n : Nat) → Result I
  | 0 => .ok iter
  | n + 1 => do
    let (opt, iter) ← iterInst.next iter
    match opt with
    | none => .ok iter
    | some _ => core.iter.adapters.step_by.skipN iterInst iter n

@[rust_fun
  "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, @Clause0_Item>}::next"]
def core.iter.adapters.step_by.IteratorStepBy.next
  {I : Type} {Item : Type}
  (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
  core.iter.adapters.step_by.StepBy I →
  Result ((Option Item) × (core.iter.adapters.step_by.StepBy I)) :=
  fun self => do
    let (opt, iter) ← IteratorInst.next self.iter
    match opt with
    | none => .ok (none, { self with iter })
    | some item => do
      let iter ← core.iter.adapters.step_by.skipN IteratorInst iter (self.step_by.val - 1)
      .ok (some item, { iter, step_by := self.step_by })

@[rust_fun
  "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, @Clause0_Item>}::step_by"]
def core.iter.adapters.step_by.IteratorStepBy.step_by
  {I : Type} {Item : Type}
  (_IteratorInst : core.iter.traits.iterator.Iterator I Item) :
  core.iter.adapters.step_by.StepBy I → Std.Usize →
  Result (core.iter.adapters.step_by.StepBy (core.iter.adapters.step_by.StepBy I)) :=
  fun self steps =>
    if steps.val = 0 then .fail .panic
    else .ok ⟨ self, steps ⟩

@[rust_fun
  "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, @Clause0_Item>}::enumerate"]
def core.iter.adapters.step_by.IteratorStepBy.enumerate
  {I : Type} {Item : Type}
  (_IteratorInst : core.iter.traits.iterator.Iterator I Item) :
  core.iter.adapters.step_by.StepBy I →
  Result (core.iter.adapters.enumerate.Enumerate (core.iter.adapters.step_by.StepBy I)) :=
  fun self => .ok { iter := self, count := 0#usize }

@[rust_fun
  "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, @Clause0_Item>}::take"]
def core.iter.adapters.step_by.IteratorStepBy.take
  {I : Type} {Item : Type}
  (_IteratorInst : core.iter.traits.iterator.Iterator I Item) :
  core.iter.adapters.step_by.StepBy I → Std.Usize →
  Result (core.iter.adapters.take.Take (core.iter.adapters.step_by.StepBy I)) :=
  fun self n => .ok ⟨ self, n ⟩

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

@[rust_fun "core::iter::traits::iterator::Iterator::collect"]
def core.iter.traits.iterator.Iterator.collect.default
  {Self : Type} {B : Type} {Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Item)
  (collectFromIteratorInst : core.iter.traits.collect.FromIterator B Item) :
  Self → Result B :=
  fun self => collectFromIteratorInst.from_iter
    (core.iter.traits.collect.IntoIterator.Blanket IteratorInst) self

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

-- ============================================================================
-- Generic Step operations for UScalar types
-- ============================================================================

/-- Generic `steps_between` for all unsigned scalar types.
    Conservatively checks that `diff ≤ Usize.max` (always true for small types,
    needed for U64/U128). -/
def core.iter.range.UScalarStep.steps_between {ty : UScalarTy}
    (start end_ : UScalar ty) : Result (Usize × (Option Usize)) :=
  if start.val > end_.val then ok ⟨ 0#usize, none ⟩
  else
    let diff := end_.val - start.val
    if h : diff ≤ Usize.max then
      let steps := Usize.ofNatCore diff (by scalar_tac)
      ok ⟨ steps, some steps ⟩
    else
      let usizeMax := Usize.ofNatCore Usize.max (by scalar_tac)
      ok ⟨ usizeMax, none ⟩

private theorem UScalar.max_add_one_eq_size (ty : UScalarTy) :
    UScalar.max ty + 1 = 2^ty.numBits := by
  cases ty <;> scalar_tac

/-- Generic `forward_checked` for all unsigned scalar types. -/
def core.iter.range.UScalarStep.forward_checked {ty : UScalarTy}
    (start : UScalar ty) (n : Usize) : Result (Option (UScalar ty)) :=
  if h : start.val + n.val ≤ UScalar.max ty then
    ok (some (UScalar.ofNatCore (start.val + n.val)
      (by have := UScalar.max_add_one_eq_size ty; omega)))
  else ok none

/-- Generic `backward_checked` for all unsigned scalar types. -/
def core.iter.range.UScalarStep.backward_checked {ty : UScalarTy}
    (start : UScalar ty) (n : Usize) : Result (Option (UScalar ty)) :=
  if h : n.val ≤ start.val then
    ok (some (UScalar.ofNatCore (start.val - n.val)
      (by have := start.hBounds; omega)))
  else ok none

-- ============================================================================
-- Specialized Step instances
-- ============================================================================

/-- Generic Step instance for all unsigned scalar types. The per-type instances
    below are abbreviations of this, differing only in Clone/PartialOrd. -/
def core.iter.range.UScalarStep (ty : UScalarTy)
    (cloneInst : core.clone.Clone (UScalar ty))
    (partialOrdInst : core.cmp.PartialOrd (UScalar ty) (UScalar ty)) :
    core.iter.range.Step (UScalar ty) := {
  cloneInst
  partialOrdInst
  steps_between := UScalarStep.steps_between
  forward_checked := UScalarStep.forward_checked
  backward_checked := UScalarStep.backward_checked
}

-- Per-type abbreviations with @[rust_fun] tags for the Aeneas compiler.

@[rust_fun "core::iter::range::{core::iter::range::Step<usize>}::steps_between"]
abbrev core.iter.range.StepUsize.steps_between := @UScalarStep.steps_between .Usize
@[rust_fun "core::iter::range::{core::iter::range::Step<usize>}::forward_checked"]
abbrev core.iter.range.StepUsize.forward_checked := @UScalarStep.forward_checked .Usize
@[rust_fun "core::iter::range::{core::iter::range::Step<usize>}::backward_checked"]
abbrev core.iter.range.StepUsize.backward_checked := @UScalarStep.backward_checked .Usize
@[rust_trait_impl "core::iter::range::Step<usize>"]
abbrev core.iter.range.StepUsize := UScalarStep .Usize core.clone.CloneUsize core.cmp.PartialOrdUsize

@[rust_fun "core::iter::range::{core::iter::range::Step<u8>}::steps_between"]
abbrev core.iter.range.StepU8.steps_between := @UScalarStep.steps_between .U8
@[rust_fun "core::iter::range::{core::iter::range::Step<u8>}::forward_checked"]
abbrev core.iter.range.StepU8.forward_checked := @UScalarStep.forward_checked .U8
@[rust_fun "core::iter::range::{core::iter::range::Step<u8>}::backward_checked"]
abbrev core.iter.range.StepU8.backward_checked := @UScalarStep.backward_checked .U8
@[rust_trait_impl "core::iter::range::Step<u8>"]
abbrev core.iter.range.StepU8 := UScalarStep .U8 core.clone.CloneU8 core.cmp.PartialOrdU8

@[rust_fun "core::iter::range::{core::iter::range::Step<u16>}::steps_between"]
abbrev core.iter.range.StepU16.steps_between := @UScalarStep.steps_between .U16
@[rust_fun "core::iter::range::{core::iter::range::Step<u16>}::forward_checked"]
abbrev core.iter.range.StepU16.forward_checked := @UScalarStep.forward_checked .U16
@[rust_fun "core::iter::range::{core::iter::range::Step<u16>}::backward_checked"]
abbrev core.iter.range.StepU16.backward_checked := @UScalarStep.backward_checked .U16
@[rust_trait_impl "core::iter::range::Step<u16>"]
abbrev core.iter.range.StepU16 := UScalarStep .U16 core.clone.CloneU16 core.cmp.PartialOrdU16

@[rust_fun "core::iter::range::{core::iter::range::Step<u32>}::steps_between"]
abbrev core.iter.range.StepU32.steps_between := @UScalarStep.steps_between .U32
@[rust_fun "core::iter::range::{core::iter::range::Step<u32>}::forward_checked"]
abbrev core.iter.range.StepU32.forward_checked := @UScalarStep.forward_checked .U32
@[rust_fun "core::iter::range::{core::iter::range::Step<u32>}::backward_checked"]
abbrev core.iter.range.StepU32.backward_checked := @UScalarStep.backward_checked .U32
@[rust_trait_impl "core::iter::range::Step<u32>"]
abbrev core.iter.range.StepU32 := UScalarStep .U32 core.clone.CloneU32 core.cmp.PartialOrdU32

@[rust_fun "core::iter::range::{core::iter::range::Step<u64>}::steps_between"]
abbrev core.iter.range.StepU64.steps_between := @UScalarStep.steps_between .U64
@[rust_fun "core::iter::range::{core::iter::range::Step<u64>}::forward_checked"]
abbrev core.iter.range.StepU64.forward_checked := @UScalarStep.forward_checked .U64
@[rust_fun "core::iter::range::{core::iter::range::Step<u64>}::backward_checked"]
abbrev core.iter.range.StepU64.backward_checked := @UScalarStep.backward_checked .U64
@[rust_trait_impl "core::iter::range::Step<u64>"]
abbrev core.iter.range.StepU64 := UScalarStep .U64 core.clone.CloneU64 core.cmp.PartialOrdU64

@[rust_fun "core::iter::range::{core::iter::range::Step<u128>}::steps_between"]
abbrev core.iter.range.StepU128.steps_between := @UScalarStep.steps_between .U128
@[rust_fun "core::iter::range::{core::iter::range::Step<u128>}::forward_checked"]
abbrev core.iter.range.StepU128.forward_checked := @UScalarStep.forward_checked .U128
@[rust_fun "core::iter::range::{core::iter::range::Step<u128>}::backward_checked"]
abbrev core.iter.range.StepU128.backward_checked := @UScalarStep.backward_checked .U128
@[rust_trait_impl "core::iter::range::Step<u128>"]
abbrev core.iter.range.StepU128 := UScalarStep .U128 core.clone.CloneU128 core.cmp.PartialOrdU128

-- ============================================================================
-- Enumerate.next — generic over any inner iterator
-- ============================================================================
--  Model for `Iterator::next` on `Enumerate<I>`

@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::next"]
def core.iter.adapters.enumerate.IteratorEnumerate.next
    {I : Type} {Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.enumerate.Enumerate I) :
    Result ((Option (Usize × Item)) × (core.iter.adapters.enumerate.Enumerate I)) := do
  let (opt, iter') ← IteratorInst.next self.iter
  match opt with
  | none => ok (none, { iter := iter', count := self.count })
  | some a => do
      let count' ← self.count + 1#usize
      ok (some (self.count, a), { iter := iter', count := count' })

@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::step_by"]
def core.iter.adapters.enumerate.IteratorEnumerate.step_by
    {I : Type} {Item : Type}
    (_IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.enumerate.Enumerate I) (steps : Usize) :
    Result (core.iter.adapters.step_by.StepBy (core.iter.adapters.enumerate.Enumerate I)) :=
  if steps.val = 0 then .fail .panic
  else .ok ⟨ self, steps ⟩

@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::enumerate"]
def core.iter.adapters.enumerate.IteratorEnumerate.enumerate
    {I : Type} {Item : Type}
    (_IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.enumerate.Enumerate I) :
    Result (core.iter.adapters.enumerate.Enumerate (core.iter.adapters.enumerate.Enumerate I)) :=
  .ok { iter := self, count := 0#usize }

@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::take"]
def core.iter.adapters.enumerate.IteratorEnumerate.take
    {I : Type} {Item : Type}
    (_IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.enumerate.Enumerate I) (n : Usize) :
    Result (core.iter.adapters.take.Take (core.iter.adapters.enumerate.Enumerate I)) :=
  .ok ⟨ self, n ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>"]
def core.iter.traits.iterator.IteratorEnumerate {I : Type} {Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.enumerate.Enumerate I) (Usize × Item) := {
  next := core.iter.adapters.enumerate.IteratorEnumerate.next IteratorInst
  step_by := core.iter.adapters.enumerate.IteratorEnumerate.step_by IteratorInst
  enumerate := core.iter.adapters.enumerate.IteratorEnumerate.enumerate IteratorInst
  take := core.iter.adapters.enumerate.IteratorEnumerate.take IteratorInst
}

-- ============================================================================
-- Take.next — generic over any inner iterator
-- ============================================================================
-- Model for `Iterator::next` on `Take<I>`

@[rust_fun
  "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, @Clause0_Item>}::next"]
def core.iter.adapters.take.IteratorTake.next
    {I : Type} {Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.take.Take I) :
    Result ((Option Item) × (core.iter.adapters.take.Take I)) :=
  if self.n.val = 0 then
    ok (none, self)
  else do
    let n' ← self.n - 1#usize
    let (opt, iter') ← IteratorInst.next self.iter
    ok (opt, { iter := iter', n := n' })

@[rust_fun
  "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, @Clause0_Item>}::step_by"]
def core.iter.adapters.take.IteratorTake.step_by
    {I : Type} {Item : Type}
    (_IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.take.Take I) (steps : Usize) :
    Result (core.iter.adapters.step_by.StepBy (core.iter.adapters.take.Take I)) :=
  if steps.val = 0 then .fail .panic
  else .ok ⟨ self, steps ⟩

@[rust_fun
  "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, @Clause0_Item>}::enumerate"]
def core.iter.adapters.take.IteratorTake.enumerate
    {I : Type} {Item : Type}
    (_IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.take.Take I) :
    Result (core.iter.adapters.enumerate.Enumerate (core.iter.adapters.take.Take I)) :=
  .ok { iter := self, count := 0#usize }

@[rust_fun
  "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, @Clause0_Item>}::take"]
def core.iter.adapters.take.IteratorTake.take
    {I : Type} {Item : Type}
    (_IteratorInst : core.iter.traits.iterator.Iterator I Item)
    (self : core.iter.adapters.take.Take I) (n : Usize) :
    Result (core.iter.adapters.take.Take (core.iter.adapters.take.Take I)) :=
  .ok ⟨ self, n ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, @Clause0_Item>"]
def core.iter.traits.iterator.IteratorTake {I : Type} {Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator I Item) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.take.Take I) Item := {
  next := core.iter.adapters.take.IteratorTake.next IteratorInst
  step_by := core.iter.adapters.take.IteratorTake.step_by IteratorInst
  enumerate := core.iter.adapters.take.IteratorTake.enumerate IteratorInst
  take := core.iter.adapters.take.IteratorTake.take IteratorInst
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
  λ range step_by =>
    if step_by.val = 0 then .fail .panic
    else .ok ⟨ range, step_by ⟩

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
