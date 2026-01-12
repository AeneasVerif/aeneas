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
