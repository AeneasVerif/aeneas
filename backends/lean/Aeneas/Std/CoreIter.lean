import Aeneas.Std.Core
import Aeneas.Std.Range
import Aeneas.Std.Scalar.CloneCopy
import Aeneas.ScalarTac.Lemmas
import Aeneas.Std.Scalar.CheckedOps.Add

namespace Aeneas.Std

open Result

/-!
# Iterator and IntoIterator
-/

/- Trait declaration: [core::iter::traits::iterator::Iterator]
   Name pattern: [core::iter::traits::iterator::Iterator] -/
structure core.iter.traits.iterator.Iterator (Self Item : Type) where
  next : Self → Result ((Option Item) × Self)

/- Trait declaration: [core::iter::traits::collect::IntoIterator]
   Name pattern: [core::iter::traits::collect::IntoIterator] -/
structure core.iter.traits.collect.IntoIterator (Self Item IntoIter : Type) where
  iteratorIteratorInst : core.iter.traits.iterator.Iterator IntoIter Item
  into_iter : Self → Result IntoIter

/- [core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<Item, I> for I}::into_iter]:
   Name pattern: [core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<@I, @Item, @I>}::into_iter] -/
@[simp] def core.iter.traits.collect.IntoIteratorBlanket.into_iter
  {I Item : Type} (_ : core.iter.traits.iterator.Iterator I Item)
  (self : I) : Result I := ok self

/-!
# Step
-/

/- Trait declaration: [core::iter::range::Step]
   Name pattern: [core::iter::range::Step] -/
structure core.iter.range.Step (Self : Type) where
  cloneInst : core.clone.Clone Self
  partialOrdInst : core.cmp.PartialOrd Self Self
  steps_between : Self → Self → Result (Usize × (Option Usize))
  forward_checked : Self → Usize → Result (Option Self)
  backward_checked : Self → Usize → Result (Option Self)
  -- Provided methods
  forward : Self → Usize → Result Self
  forward_unchecked : Self → Usize → Result Self
  backward : Self → Usize → Result Self
  backward_unchecked : Self → Usize → Result Self

def core.iter.range.Step.forward.default {Self : Type}
  (forward_checked : Self → Usize → Result (Option Self))
  (start : Self) (count : Usize) : Result Self := do
  let res ← forward_checked start count
  match res with -- This is actually: `std::option::Option::expect`
  | none => fail .panic
  | some res => ok res

def core.iter.range.Step.forward_unchecked.default {Self : Type}
  (forward : Self → Usize → Result Self)
  (start : Self) (count : Usize) : Result Self := do
  forward start count

def core.iter.range.Step.backward.default {Self : Type}
  (backward_checked : Self → Usize → Result (Option Self))
  (start : Self) (count : Usize) : Result Self := do
  let res ← backward_checked start count
  match res with -- This is actually: `std::option::Option::expect`
  | none => fail .panic
  | some res => ok res

def core.iter.range.Step.backward_unchecked.default {Self : Type}
  (backward : Self → Usize → Result Self)
  (start : Self) (count : Usize) : Result Self := do
  backward start count

/-!
# Instances of Step for the scalar types
-/

@[local scalar_tac_simps]
theorem UScalar_two_pow_numBits_eq_max (ty : UScalarTy) : 2^ty.numBits = UScalar.max ty + 1 := by
  cases ty <;> simp [UScalar.max] <;> scalar_tac

@[local scalar_tac_simps]
theorem IScalar_two_pow_numBits_eq_max (ty : IScalarTy) : 2^(ty.numBits - 1) = IScalar.max ty + 1 := by
  cases ty <;> simp [IScalar.max] <;> scalar_tac

@[local scalar_tac_simps]
theorem IScalar_two_pow_numBits_eq_min (ty : IScalarTy) : - 2^(ty.numBits - 1) = IScalar.min ty := by
  cases ty <;> simp [IScalar.min] <;> scalar_tac

/-!
Below, we're regrouping the "narrower" and "wider" implementations.
See: https://doc.rust-lang.org/src/core/iter/range.rs.html#247
-/
def UScalar.steps_between (start end_ : UScalar ty) : Usize × Option Usize :=
  if h0: start.val ≤ end_.val then
    if h1: end_.val - start.val ≤ Usize.max then
      let steps : Usize := Usize.ofNatCore (end_.val - start.val) (by scalar_tac)
      (steps, some steps)
    else
      (core.usize.max, none)
  else
    (0#usize, none)

-- https://doc.rust-lang.org/src/core/iter/range.rs.html#273
def UScalar.StepNarrow.forward_checked (start : UScalar ty) (n : Usize) : Option (UScalar ty) :=
  if h : n.val ≤ UScalar.max ty then -- Actually: `Self.try_from(n)`
    core.num.checked_add_UScalar start (UScalar.ofNatCore n.val (by scalar_tac))
  else none

-- https://doc.rust-lang.org/src/core/iter/range.rs.html#281
def UScalar.StepNarrow.backward_checked (start : UScalar ty) (n : Usize) : Option (UScalar ty) :=
  if h : n.val ≤ UScalar.max ty then -- Actually: `Self.try_from(n)`
    core.num.checked_sub_UScalar start (UScalar.ofNatCore n.val (by scalar_tac))
  else none



def UScalar.StepNarrow {ty : UScalarTy} : core.iter.range.Step (UScalar ty) where
  cloneInst := core.clone.CloneUScalar ty

  partialOrdInst : core.cmp.PartialOrd Self Self
  steps_between : Self → Self → Result (Usize × (Option Usize))
  forward_checked : Self → Usize → Result (Option Self)
  backward_checked : Self → Usize → Result (Option Self)
  -- Provided methods
  forward : Self → Usize → Result Self
  forward_unchecked : Self → Usize → Result Self
  backward : Self → Usize → Result Self
  backward_unchecked : Self → Usize → Result Self

impl Step for $i_narrower {
                step_identical_methods!();
                step_signed_methods!($u_narrower);

                #[inline]
                fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                    if *start <= *end {
                        // This relies on $i_narrower <= usize
                        //
                        // Casting to isize extends the width but preserves the sign.
                        // Use wrapping_sub in isize space and cast to usize to compute
                        // the difference that might not fit inside the range of isize.
                        let steps = (*end as isize).wrapping_sub(*start as isize) as usize;
                        (steps, Some(steps))
                    } else {
                        (0, None)
                    }
                }

                #[inline]
                fn forward_checked(start: Self, n: usize) -> Option<Self> {
                    match $u_narrower::try_from(n) {
                        Ok(n) => {
                            // Wrapping handles cases like
                            // `Step::forward(-120_i8, 200) == Some(80_i8)`,
                            // even though 200 is out of range for i8.
                            let wrapped = start.wrapping_add(n as Self);
                            if wrapped >= start {
                                Some(wrapped)
                            } else {
                                None // Addition overflowed
                            }
                        }
                        // If n is out of range of e.g. u8,
                        // then it is bigger than the entire range for i8 is wide
                        // so `any_i8 + n` necessarily overflows i8.
                        Err(_) => None,
                    }
                }

                #[inline]
                fn backward_checked(start: Self, n: usize) -> Option<Self> {
                    match $u_narrower::try_from(n) {
                        Ok(n) => {
                            // Wrapping handles cases like
                            // `Step::forward(-120_i8, 200) == Some(80_i8)`,
                            // even though 200 is out of range for i8.
                            let wrapped = start.wrapping_sub(n as Self);
                            if wrapped <= start {
                                Some(wrapped)
                            } else {
                                None // Subtraction overflowed
                            }
                        }
                        // If n is out of range of e.g. u8,
                        // then it is bigger than the entire range for i8 is wide
                        // so `any_i8 - n` necessarily overflows i8.
                        Err(_) => None,
                    }
                }
            }
        )+

/-!
# NonZero and ZeroablePrimitive
-/
structure std.num.ZeroablePrimitive (Self : Type) where
  copyInst : core.marker.Copy Self
  -- Missing: Sealed { }

def std.num.ZeroablePrimitiveU8 : std.num.ZeroablePrimitive U8 := {
  copyInst := core.marker.CopyU8 }

def std.num.ZeroablePrimitiveU16 : std.num.ZeroablePrimitive U16 := {
  copyInst := core.marker.CopyU16 }

def std.num.ZeroablePrimitiveU32 : std.num.ZeroablePrimitive U32 := {
  copyInst := core.marker.CopyU32 }

def std.num.ZeroablePrimitiveU64 : std.num.ZeroablePrimitive U64 := {
  copyInst := core.marker.CopyU64 }

def std.num.ZeroablePrimitiveU128 : std.num.ZeroablePrimitive U128 := {
  copyInst := core.marker.CopyU128 }

def std.num.ZeroablePrimitiveUsize : std.num.ZeroablePrimitive Usize := {
  copyInst := core.marker.CopyUsize }

def std.num.ZeroablePrimitiveI8 : std.num.ZeroablePrimitive I8 := {
  copyInst := core.marker.CopyI8 }

def std.num.ZeroablePrimitiveI16 : std.num.ZeroablePrimitive I16 := {
  copyInst := core.marker.CopyI16 }

def std.num.ZeroablePrimitiveI32 : std.num.ZeroablePrimitive I32 := {
  copyInst := core.marker.CopyI32 }

def std.num.ZeroablePrimitiveI64 : std.num.ZeroablePrimitive I64 := {
  copyInst := core.marker.CopyI64 }

def std.num.ZeroablePrimitiveI128 : std.num.ZeroablePrimitive I128 := {
  copyInst := core.marker.CopyI128 }

def std.num.ZeroablePrimitiveIsize : std.num.ZeroablePrimitive Isize := {
  copyInst := core.marker.CopyIsize }

abbrev std.num.NonZero {Self : Type} (_ : ZeroablePrimitive Self) := Self

/-!
# RangeIteratorImpl
-/
/- Trait declaration: [core::iter::range::RangeIteratorImpl]-/
structure core.iter.range.RangeIteratorImpl (Self Item : Type) where
    -- Iterator
    spec_next : Self → Result (Option Item × Self)
    spec_nth : Self → Usize → Result (Option Item × Self)
    spec_advance_by : Self → Usize → Result (core.result.Result Unit (std.num.NonZero std.num.ZeroablePrimitiveUsize) × Self)

    -- DoubleEndedIterator
    spec_next_back : Self → Result (Option Item × Self)
    spec_nth_back : Self → Usize → Result (Option Item × Self)
    spec_advance_back_by : Self → Usize → Result (core.result.Result Unit (std.num.NonZero std.num.ZeroablePrimitiveUsize) × Self)

-- https://doc.rust-lang.org/src/core/iter/range.rs.html#685
def core.iter.range.RangeIteratorImplRange.spec_next {A : Type} (stepInst : core.iter.range.Step A)
  (self : core.ops.range.Range A) : Result (Option A × core.ops.range.Range A) := do
  if ← stepInst.partialOrdInst.lt self.start self.end_ then
    let start ← stepInst.cloneInst.clone self.start
    let n ← stepInst.forward_checked start 1#usize
    match n with -- This is actually: `std::option::Option::expect`
    | none => fail .panic
    | some n =>
      ok (some self.start, { self with start := n }) -- actually: `std::mem::replace`
  else
    ok (none, self)

-- https://doc.rust-lang.org/src/core/iter/range.rs.html#696
def core.iter.range.RangeIteratorImplRange.spec_nth {A : Type} (stepInst : core.iter.range.Step A)
  (self : core.ops.range.Range A) (n : Usize) : Result (Option A × core.ops.range.Range A) := do
  if let some plus_n ← stepInst.forward_checked (← stepInst.cloneInst.clone self.start) n then
    if ← stepInst.partialOrdInst.lt plus_n self.end_ then
      let start ← stepInst.forward_checked (← stepInst.cloneInst.clone plus_n) 1#usize
      match start with -- This is actually: `std::option::Option::expect`
      | none => (fail .panic : Result (Option A × ops.range.Range A))
      | some start => ok (some plus_n, {self with start})
    else
      let self := { self with start := ← stepInst.cloneInst.clone self.end_ }
      ok (none, self)
  else
    let self := { self with start := ← stepInst.cloneInst.clone self.end_ }
    ok (none, self)

-- https://doc.rust-lang.org/src/core/iter/range.rs.html#710
def core.iter.range.RangeIteratorImplRange.spec_advance_by {A : Type} (stepInst : core.iter.range.Step A)
  (self : core.ops.range.Range A) (n : Usize) :
  Result (core.result.Result Unit (std.num.NonZero std.num.ZeroablePrimitiveUsize) × core.ops.range.Range A) := do
  let steps ← stepInst.steps_between self.start self.end_
  let available := core.option.Option.unwrap_or steps.snd steps.fst
  let taken := core.cmp.impls.OrdUsize.min available n
  let start ← stepInst.forward_checked (← stepInst.cloneInst.clone self.start) taken
  match start with -- This is actually: `std::option::Option::expect`
  | none => fail .panic
  | some start =>
    let self := { self with start }
    -- This is actually: `NonZero::new(n - taken).map_or(Ok(()), Err)`
    let n' ← n - taken
    if n' = 0#usize then
      ok (.Ok (), self)
    else ok (.Err n', self)

-- https://doc.rust-lang.org/src/core/iter/range.rs.html#723
def core.iter.range.RangeIteratorImplRange.spec_next_back {A : Type} (stepInst : core.iter.range.Step A)
  (self : core.ops.range.Range A) : Result (Option A × core.ops.range.Range A) := do
  if ← stepInst.partialOrdInst.lt self.start self.end_ then
    let end_ ← stepInst.backward_checked (← stepInst.cloneInst.clone self.end_) 1#usize
    match end_ with -- This is actually: `std::option::Option::expect`
    | none => fail .panic
    | some end_ =>
      let self := { self with end_ }
      ok (some (← stepInst.cloneInst.clone self.end_), self)
  else ok (none, self)

-- https://doc.rust-lang.org/src/core/iter/range.rs.html#734
def core.iter.range.RangeIteratorImplRange.spec_nth_back {A : Type} (stepInst : core.iter.range.Step A)
  (self : core.ops.range.Range A) (n : Usize) : Result (Option A × core.ops.range.Range A) := do
  if let some minus_n ← stepInst.backward_checked (← stepInst.cloneInst.clone self.end_) n then
    if ← stepInst.partialOrdInst.gt minus_n self.start then
      let end_ ← stepInst.backward_checked minus_n 1#usize
      match end_ with -- This is actually: `std::option::Option::expect`
      | none => fail .panic
      | some end_ =>
        let self := { self with end_ }
        ok (some (← stepInst.cloneInst.clone self.end_), self)
    else
      let self := { self with end_ := ← stepInst.cloneInst.clone self.start}
      ok (none, self)
  else
    let self := { self with end_ := ← stepInst.cloneInst.clone self.start}
    ok (none, self)

def core.iter.range.RangeIteratorImplRange.spec_advance_back_by
  {A : Type} (stepInst : core.iter.range.Step A)
  (self : core.ops.range.Range A) (n : Usize) :
  Result (core.result.Result Unit (std.num.NonZero std.num.ZeroablePrimitiveUsize) × core.ops.range.Range A) := do
  let steps ← stepInst.steps_between self.start self.end_
  let available := core.option.Option.unwrap_or steps.snd steps.fst
  let taken := core.cmp.impls.OrdUsize.min available n
  let end_ ← stepInst.backward_checked (← stepInst.cloneInst.clone self.end_) taken
  match end_ with -- This is actually: `std::option::Option::expect`
  | none => fail .panic
  | some end_ =>
    let self := { self with end_ }
    -- This is actually: `NonZero::new(n - taken).map_or(Ok(()), Err)`
    let n' ← n - taken
    if n' = 0#usize then
      ok (.Ok (), self)
    else ok (.Err n', self)

-- https://doc.rust-lang.org/src/core/iter/range.rs.html#681
def core.iter.range.RangeIteratorImplRange {A : Type} (stepInst : core.iter.range.Step A) :
  core.iter.range.RangeIteratorImpl (core.ops.range.Range A) A := {
    -- Iterator
  spec_next := core.iter.range.RangeIteratorImplRange.spec_next stepInst
  spec_nth := core.iter.range.RangeIteratorImplRange.spec_nth stepInst
  spec_advance_by := core.iter.range.RangeIteratorImplRange.spec_advance_by stepInst
  -- DoubleEndedIterator
  spec_next_back := core.iter.range.RangeIteratorImplRange.spec_next_back stepInst
  spec_nth_back := core.iter.range.RangeIteratorImplRange.spec_nth_back stepInst
  spec_advance_back_by := core.iter.range.RangeIteratorImplRange.spec_advance_back_by stepInst
}

/- [core::iter::range::{core::iter::traits::iterator::Iterator<A> for core::ops::range::Range<A>}#6::next]:
   https://doc.rust-lang.org/src/core/iter/range.rs.html#848
   Name pattern: [core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::next] -/
def core.iter.range.IteratorRange.next
  {A : Type} (stepInst : core.iter.range.Step A)
  (r : core.ops.range.Range A) : Result ((Option A) × (core.ops.range.Range A)) := do
  core.iter.range.RangeIteratorImplRange.spec_next stepInst r

/- Trait implementation: [core::iter::range::{core::iter::traits::iterator::Iterator<A> for core::ops::range::Range<A>}#6]
   Source: '/rustc/library/core/src/iter/range.rs', lines 844:0-844:40
   Name pattern: [core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>] -/
@[reducible]
def core.iter.traits.iterator.IteratorRange {A : Type}
  (stepInst : core.iter.range.Step A) :
  core.iter.traits.iterator.Iterator (core.ops.range.Range A) A := {
  next := core.iter.range.IteratorRange.next stepInst
}



/- [core::iter::range::{core::iter::range::Step for i32}#40::steps_between]:
   Source: '/rustc/library/core/src/iter/range.rs', lines 296:16-296:84
   Name pattern: [core::iter::range::{core::iter::range::Step<i32>}::steps_between] -/
axiom core.iter.range.StepI32.steps_between
  : I32 → I32 → Result (Usize × (Option Usize))

/- [core::iter::range::{core::iter::range::Step for i32}#40::forward_checked]:
   Source: '/rustc/library/core/src/iter/range.rs', lines 311:16-311:73
   Name pattern: [core::iter::range::{core::iter::range::Step<i32>}::forward_checked] -/
axiom core.iter.range.StepI32.forward_checked
  : I32 → Usize → Result (Option I32)

/- [core::iter::range::{core::iter::range::Step for i32}#40::backward_checked]:
   Source: '/rustc/library/core/src/iter/range.rs', lines 332:16-332:74
   Name pattern: [core::iter::range::{core::iter::range::Step<i32>}::backward_checked] -/
axiom core.iter.range.StepI32.backward_checked
  : I32 → Usize → Result (Option I32)

/- Trait implementation: [core::iter::range::{core::iter::range::Step for i32}#40]
   Source: '/rustc/library/core/src/iter/range.rs', lines 291:12-291:37
   Name pattern: [core::iter::range::Step<i32>] -/
@[reducible]
def core.iter.range.StepI32 : core.iter.range.Step I32 := {
  cloneCloneInst := core.clone.CloneI32
  cmpPartialOrdInst := core.cmp.PartialOrdI32
  steps_between := core.iter.range.StepI32.steps_between
  forward_checked := core.iter.range.StepI32.forward_checked
  backward_checked := core.iter.range.StepI32.backward_checked
}

/- [blanket_impl::main]:
   Source: 'tests/src/blanket_impl.rs', lines 2:0-5:1 -/
def main : Result Unit :=
  do
  let _ ←
    core.iter.traits.collect.IntoIterator.into_iter
      (core.iter.traits.iterator.IteratorcoreopsrangeRangeA
      core.iter.range.StepI32) { start := 0#i32, end_ := 1#i32 }
  ok ()



/- Trait implementation: [core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<Clause1_Item, I> for I}#1]
   Source: '/rustc/library/core/src/iter/traits/collect.rs', lines 350:0-350:36
   Name pattern: [core::iter::traits::collect::IntoIterator<@I, @Clause1_Item, @I>] -/
@[reducible]
def core.iter.traits.collect.IntoIterator.blanket {I : Type} {Clause1_Item :
  Type} (iteratorIteratorInst : core.iter.traits.iterator.Iterator I
  Clause1_Item) : core.iter.traits.collect.IntoIterator I Clause1_Item I := {
  iteratorIteratorInst := iteratorIteratorInst
  into_iter := core.iter.traits.collect.IntoIterator.into_iter
    iteratorIteratorInst
}

/- Trait declaration: [core::iter::adapters::zip::TrustedRandomAccessNoCoerce]
   Source: '/rustc/library/core/src/iter/adapters/zip.rs', lines 593:0-593:51
   Name pattern: [core::iter::adapters::zip::TrustedRandomAccessNoCoerce] -/
structure core.iter.adapters.zip.TrustedRandomAccessNoCoerce (Self : Type)
  where
  MAY_HAVE_SIDE_EFFECT : Bool

/- Trait declaration: [core::ops::function::FnOnce]
   Source: '/rustc/library/core/src/ops/function.rs', lines 242:0-242:29
   Name pattern: [core::ops::function::FnOnce] -/
structure core.ops.function.FnOnce (Self : Type) (Args : Type) (Self_Output :
  Type) where
  call_once : Self → Args → Result Self_Output

/- Trait declaration: [core::ops::function::FnMut]
   Source: '/rustc/library/core/src/ops/function.rs', lines 163:0-163:42
   Name pattern: [core::ops::function::FnMut] -/
structure core.ops.function.FnMut (Self : Type) (Args : Type)
  (Self_Clause0_Output : Type) where
  FnOnceInst : core.ops.function.FnOnce Self Args Self_Clause0_Output
  call_mut : Self → Args → Result (Self_Clause0_Output × Self)

/- Trait declaration: [core::iter::traits::collect::FromIterator]
   Source: '/rustc/library/core/src/iter/traits/collect.rs', lines 134:0-134:32
   Name pattern: [core::iter::traits::collect::FromIterator] -/
structure core.iter.traits.collect.FromIterator (Self : Type) (A : Type) where
  from_iter : forall {T : Type} {Clause1_IntoIter : Type} (IntoIteratorInst :
    core.iter.traits.collect.IntoIterator T A Clause1_IntoIter), T → Result
    Self

/- Trait declaration: [core::ops::try_trait::FromResidual]
   Source: '/rustc/library/core/src/ops/try_trait.rs', lines 307:0-307:51
   Name pattern: [core::ops::try_trait::FromResidual] -/
structure core.ops.try_trait.FromResidual (Self : Type) (R : Type) where
  from_residual : R → Result Self

/- [core::ops::control_flow::ControlFlow]
   Source: '/rustc/library/core/src/ops/control_flow.rs', lines 85:0-85:31
   Name pattern: [core::ops::control_flow::ControlFlow] -/
inductive core.ops.control_flow.ControlFlow (B : Type) (C : Type) where
| Continue : C → core.ops.control_flow.ControlFlow B C
| Break : B → core.ops.control_flow.ControlFlow B C

/- Trait declaration: [core::ops::try_trait::Try]
   Source: '/rustc/library/core/src/ops/try_trait.rs', lines 131:0-131:27
   Name pattern: [core::ops::try_trait::Try] -/
structure core.ops.try_trait.Try (Self : Type) (Self_Output : Type)
  (Self_Residual : Type) where
  FromResidualInst : core.ops.try_trait.FromResidual Self Self_Residual
  from_output : Self_Output → Result Self
  branch : Self → Result (core.ops.control_flow.ControlFlow Self_Residual
    Self_Output)

/- Trait declaration: [core::ops::try_trait::Residual]
   Source: '/rustc/library/core/src/ops/try_trait.rs', lines 359:0-359:21
   Name pattern: [core::ops::try_trait::Residual] -/
structure core.ops.try_trait.Residual (Self : Type) (O : Type) (Self_TryType :
  Type) where
  TryInst : core.ops.try_trait.Try Self_TryType O Self

/- Trait declaration: [core::iter::traits::collect::Extend]
   Source: '/rustc/library/core/src/iter/traits/collect.rs', lines 430:0-430:19
   Name pattern: [core::iter::traits::collect::Extend] -/
structure core.iter.traits.collect.Extend (Self : Type) (A : Type) where
  extend : forall {T : Type} {Clause1_IntoIter : Type} (IntoIteratorInst :
    core.iter.traits.collect.IntoIterator T A Clause1_IntoIter), Self → T →
    Result Self

/- Trait declaration: [core::default::Default]
   Source: '/rustc/library/core/src/default.rs', lines 107:0-107:24
   Name pattern: [core::default::Default] -/
structure core.default.Default (Self : Type) where
  default : Result Self

/- Trait declaration: [core::iter::traits::double_ended::DoubleEndedIterator]
   Source: '/rustc/library/core/src/iter/traits/double_ended.rs', lines 41:0-41:39
   Name pattern: [core::iter::traits::double_ended::DoubleEndedIterator] -/
structure core.iter.traits.double_ended.DoubleEndedIterator (Self : Type)
  (Self_Clause0_Item : Type) where
  iteratorIteratorInst : core.iter.traits.iterator.Iterator Self
    Self_Clause0_Item
  next_back : Self → Result ((Option Self_Clause0_Item) × Self)

/- Trait declaration: [core::iter::traits::exact_size::ExactSizeIterator]
   Source: '/rustc/library/core/src/iter/traits/exact_size.rs', lines 86:0-86:37
   Name pattern: [core::iter::traits::exact_size::ExactSizeIterator] -/
structure core.iter.traits.exact_size.ExactSizeIterator (Self : Type)
  (Self_Clause0_Item : Type) where
  iteratorIteratorInst : core.iter.traits.iterator.Iterator Self
    Self_Clause0_Item

/- Trait declaration: [core::iter::traits::accum::Sum]
   Source: '/rustc/library/core/src/iter/traits/accum.rs', lines 17:0-17:30
   Name pattern: [core::iter::traits::accum::Sum] -/
structure core.iter.traits.accum.Sum (Self : Type) (A : Type) where
  sum : forall {I : Type} (iteratorIteratorInst :
    core.iter.traits.iterator.Iterator I A), I → Result Self

/- Trait declaration: [core::iter::traits::accum::Product]
   Source: '/rustc/library/core/src/iter/traits/accum.rs', lines 38:0-38:34
   Name pattern: [core::iter::traits::accum::Product] -/
structure core.iter.traits.accum.Product (Self : Type) (A : Type) where
  product : forall {I : Type} (iteratorIteratorInst :
    core.iter.traits.iterator.Iterator I A), I → Result Self

end Aeneaas.Std
