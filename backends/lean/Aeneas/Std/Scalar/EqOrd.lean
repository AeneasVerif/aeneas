import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

open Result

/-!
# PartialEq, Eq, PartialOrd, Ord
-/

/- [core::cmp::impls::{core::cmp::PartialEq<u8> for u8}::eq]:
   Name pattern: core::cmp::impls::{core::cmp::PartialEq<u8, u8>}::eq -/
@[simp] abbrev core.cmp.impls.PartialEqU8.eq (x y : U8) : Bool := x = y
@[simp] abbrev core.cmp.impls.PartialEqU16.eq (x y : U16) : Bool := x = y
@[simp] abbrev core.cmp.impls.PartialEqU32.eq (x y : U32) : Bool := x = y
@[simp] abbrev core.cmp.impls.PartialEqU64.eq (x y : U64) : Bool := x = y
@[simp] abbrev core.cmp.impls.PartialEqU128.eq (x y : U128) : Bool := x = y
@[simp] abbrev core.cmp.impls.PartialEqUsize.eq (x y : Usize) : Bool := x = y

@[simp] abbrev core.cmp.impls.PartialEqI8.eq (x y : I8) : Bool := x = y
@[simp] abbrev core.cmp.impls.PartialEqI16.eq (x y : I16) : Bool := x = y
@[simp] abbrev core.cmp.impls.PartialEqI32.eq (x y : I32) : Bool := x = y
@[simp] abbrev core.cmp.impls.PartialEqI64.eq (x y : I64) : Bool := x = y
@[simp] abbrev core.cmp.impls.PartialEqI128.eq (x y : I128) : Bool := x = y
@[simp] abbrev core.cmp.impls.PartialEqIsize.eq (x y : Isize) : Bool := x = y

@[simp] abbrev core.cmp.impls.PartialEqU8.ne (x y : U8) : Bool := ¬ x = y
@[simp] abbrev core.cmp.impls.PartialEqU16.ne (x y : U16) : Bool := ¬ x = y
@[simp] abbrev core.cmp.impls.PartialEqU32.ne (x y : U32) : Bool := ¬ x = y
@[simp] abbrev core.cmp.impls.PartialEqU64.ne (x y : U64) : Bool := ¬ x = y
@[simp] abbrev core.cmp.impls.PartialEqU128.ne (x y : U128) : Bool := ¬ x = y
@[simp] abbrev core.cmp.impls.PartialEqUsize.ne (x y : Usize) : Bool := ¬ x = y

@[simp] abbrev core.cmp.impls.PartialEqI8.ne (x y : I8) : Bool := ¬ x = y
@[simp] abbrev core.cmp.impls.PartialEqI16.ne (x y : I16) : Bool := ¬ x = y
@[simp] abbrev core.cmp.impls.PartialEqI32.ne (x y : I32) : Bool := ¬ x = y
@[simp] abbrev core.cmp.impls.PartialEqI64.ne (x y : I64) : Bool := ¬ x = y
@[simp] abbrev core.cmp.impls.PartialEqI128.ne (x y : I128) : Bool := ¬ x = y
@[simp] abbrev core.cmp.impls.PartialEqIsize.ne (x y : Isize) : Bool := ¬ x = y

/- Trait implementation: [core::cmp::impls::{core::cmp::PartialEq<u8> for u8}]
   Name pattern: core::cmp::PartialEq<u8, u8> -/
@[reducible] def core.cmp.PartialEqU8 : core.cmp.PartialEq U8 U8 := {
  eq := liftFun2 core.cmp.impls.PartialEqU8.eq
  ne := liftFun2 core.cmp.impls.PartialEqU8.ne }


@[reducible] def core.cmp.PartialEqU16 : core.cmp.PartialEq U16 U16 := {
  eq := liftFun2 core.cmp.impls.PartialEqU16.eq
  ne := liftFun2 core.cmp.impls.PartialEqU16.ne }

@[reducible] def core.cmp.PartialEqU32 : core.cmp.PartialEq U32 U32 := {
  eq := liftFun2 core.cmp.impls.PartialEqU32.eq
  ne := liftFun2 core.cmp.impls.PartialEqU32.ne }

@[reducible] def core.cmp.PartialEqU64 : core.cmp.PartialEq U64 U64 := {
  eq := liftFun2 core.cmp.impls.PartialEqU64.eq
  ne := liftFun2 core.cmp.impls.PartialEqU64.ne }

@[reducible] def core.cmp.PartialEqU128 : core.cmp.PartialEq U128 U128 := {
  eq := liftFun2 core.cmp.impls.PartialEqU128.eq
  ne := liftFun2 core.cmp.impls.PartialEqU128.ne }

@[reducible] def core.cmp.PartialEqUsize : core.cmp.PartialEq Usize Usize := {
  eq := liftFun2 core.cmp.impls.PartialEqUsize.eq
  ne := liftFun2 core.cmp.impls.PartialEqUsize.ne }

@[reducible] def core.cmp.PartialEqI8 : core.cmp.PartialEq I8 I8 := {
  eq := liftFun2 core.cmp.impls.PartialEqI8.eq
  ne := liftFun2 core.cmp.impls.PartialEqI8.ne }

@[reducible] def core.cmp.PartialEqI16 : core.cmp.PartialEq I16 I16 := {
  eq := liftFun2 core.cmp.impls.PartialEqI16.eq
  ne := liftFun2 core.cmp.impls.PartialEqI16.ne }

@[reducible] def core.cmp.PartialEqI32 : core.cmp.PartialEq I32 I32 := {
  eq := liftFun2 core.cmp.impls.PartialEqI32.eq
  ne := liftFun2 core.cmp.impls.PartialEqI32.ne }

@[reducible] def core.cmp.PartialEqI64 : core.cmp.PartialEq I64 I64 := {
  eq := liftFun2 core.cmp.impls.PartialEqI64.eq
  ne := liftFun2 core.cmp.impls.PartialEqI64.ne }

@[reducible] def core.cmp.PartialEqI128 : core.cmp.PartialEq I128 I128 := {
  eq := liftFun2 core.cmp.impls.PartialEqI128.eq
  ne := liftFun2 core.cmp.impls.PartialEqI128.ne }

@[reducible] def core.cmp.PartialEqIsize : core.cmp.PartialEq Isize Isize := {
  eq := liftFun2 core.cmp.impls.PartialEqIsize.eq
  ne := liftFun2 core.cmp.impls.PartialEqIsize.ne }

/- Trait implementation: [core::cmp::impls::{core::cmp::Eq for u8}]
   Name pattern: core::cmp::Eq<u8> -/
@[reducible] def core.cmp.EqU8 : core.cmp.Eq U8 := {
  partialEqInst := core.cmp.PartialEqU8 }

@[reducible] def core.cmp.EqU16 : core.cmp.Eq U16 := {
  partialEqInst := core.cmp.PartialEqU16 }

@[reducible] def core.cmp.EqU32 : core.cmp.Eq U32 := {
  partialEqInst := core.cmp.PartialEqU32 }

@[reducible] def core.cmp.EqU64 : core.cmp.Eq U64 := {
  partialEqInst := core.cmp.PartialEqU64 }

@[reducible] def core.cmp.EqU128 : core.cmp.Eq U128 := {
  partialEqInst := core.cmp.PartialEqU128 }

@[reducible] def core.cmp.EqUsize : core.cmp.Eq Usize := {
  partialEqInst := core.cmp.PartialEqUsize }

@[reducible] def core.cmp.EqI8 : core.cmp.Eq I8 := {
  partialEqInst := core.cmp.PartialEqI8 }

@[reducible] def core.cmp.EqI16 : core.cmp.Eq I16 := {
  partialEqInst := core.cmp.PartialEqI16 }

@[reducible] def core.cmp.EqI32 : core.cmp.Eq I32 := {
  partialEqInst := core.cmp.PartialEqI32 }

@[reducible] def core.cmp.EqI64 : core.cmp.Eq I64 := {
  partialEqInst := core.cmp.PartialEqI64 }

@[reducible] def core.cmp.EqI128 : core.cmp.Eq I128 := {
  partialEqInst := core.cmp.PartialEqI128 }

@[reducible] def core.cmp.EqIsize : core.cmp.Eq Isize := {
  partialEqInst := core.cmp.PartialEqIsize }

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::partial_cmp]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::partial_cmp -/
def core.cmp.impls.PartialOrdU8.partial_cmp (x y : U8) : Option Ordering := some (compare x.val y.val)
def core.cmp.impls.PartialOrdU16.partial_cmp (x y : U16) : Option Ordering := some (compare x.val y.val)
def core.cmp.impls.PartialOrdU32.partial_cmp (x y : U32) : Option Ordering := some (compare x.val y.val)
def core.cmp.impls.PartialOrdU64.partial_cmp (x y : U64) : Option Ordering := some (compare x.val y.val)
def core.cmp.impls.PartialOrdU128.partial_cmp (x y : U128) : Option Ordering := some (compare x.val y.val)
def core.cmp.impls.PartialOrdUsize.partial_cmp (x y : Usize) : Option Ordering := some (compare x.val y.val)

def core.cmp.impls.PartialOrdI8.partial_cmp (x y : I8) : Option Ordering := some (compare x.val y.val)
def core.cmp.impls.PartialOrdI16.partial_cmp (x y : I16) : Option Ordering := some (compare x.val y.val)
def core.cmp.impls.PartialOrdI32.partial_cmp (x y : I32) : Option Ordering := some (compare x.val y.val)
def core.cmp.impls.PartialOrdI64.partial_cmp (x y : I64) : Option Ordering := some (compare x.val y.val)
def core.cmp.impls.PartialOrdI128.partial_cmp (x y : I128) : Option Ordering := some (compare x.val y.val)
def core.cmp.impls.PartialOrdIsize.partial_cmp (x y : Isize) : Option Ordering := some (compare x.val y.val)

/- [core::cmp::impls::{core::cmp::Ord for u8}::cmp]:
   Name pattern: core::cmp::impls::{core::cmp::Ord<u8>}::cmp -/
@[simp] abbrev core.cmp.impls.OrdU8.cmp (x y : U8) : Ordering := compare x.val y.val
@[simp] abbrev core.cmp.impls.OrdU16.cmp (x y : U16) : Ordering := compare x.val y.val
@[simp] abbrev core.cmp.impls.OrdU32.cmp (x y : U32) : Ordering := compare x.val y.val
@[simp] abbrev core.cmp.impls.OrdU64.cmp (x y : U64) : Ordering := compare x.val y.val
@[simp] abbrev core.cmp.impls.OrdU128.cmp (x y : U128) : Ordering := compare x.val y.val
@[simp] abbrev core.cmp.impls.OrdUsize.cmp (x y : Usize) : Ordering := compare x.val y.val

@[simp] abbrev core.cmp.impls.OrdI8.cmp (x y : I8) : Ordering := compare x.val y.val
@[simp] abbrev core.cmp.impls.OrdI16.cmp (x y : I16) : Ordering := compare x.val y.val
@[simp] abbrev core.cmp.impls.OrdI32.cmp (x y : I32) : Ordering := compare x.val y.val
@[simp] abbrev core.cmp.impls.OrdI64.cmp (x y : I64) : Ordering := compare x.val y.val
@[simp] abbrev core.cmp.impls.OrdI128.cmp (x y : I128) : Ordering := compare x.val y.val
@[simp] abbrev core.cmp.impls.OrdIsize.cmp (x y : Isize) : Ordering := compare x.val y.val

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::lt]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::lt -/
def core.cmp.impls.PartialOrdU8.lt (x y : U8) : Bool := x.val < y.val
def core.cmp.impls.PartialOrdU16.lt (x y : U16) : Bool := x.val < y.val
def core.cmp.impls.PartialOrdU32.lt (x y : U32) : Bool := x.val < y.val
def core.cmp.impls.PartialOrdU64.lt (x y : U64) : Bool := x.val < y.val
def core.cmp.impls.PartialOrdU128.lt (x y : U128) : Bool := x.val < y.val
def core.cmp.impls.PartialOrdUsize.lt (x y : Usize) : Bool := x.val < y.val

def core.cmp.impls.PartialOrdI8.lt (x y : I8) : Bool := x.val < y.val
def core.cmp.impls.PartialOrdI16.lt (x y : I16) : Bool := x.val < y.val
def core.cmp.impls.PartialOrdI32.lt (x y : I32) : Bool := x.val < y.val
def core.cmp.impls.PartialOrdI64.lt (x y : I64) : Bool := x.val < y.val
def core.cmp.impls.PartialOrdI128.lt (x y : I128) : Bool := x.val < y.val
def core.cmp.impls.PartialOrdIsize.lt (x y : Isize) : Bool := x.val < y.val

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::le]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::le -/
def core.cmp.impls.PartialOrdU8.le (x y : U8) : Bool := x.val ≤ y.val
def core.cmp.impls.PartialOrdU16.le (x y : U16) : Bool := x.val ≤ y.val
def core.cmp.impls.PartialOrdU32.le (x y : U32) : Bool := x.val ≤ y.val
def core.cmp.impls.PartialOrdU64.le (x y : U64) : Bool := x.val ≤ y.val
def core.cmp.impls.PartialOrdU128.le (x y : U128) : Bool := x.val ≤ y.val
def core.cmp.impls.PartialOrdUsize.le (x y : Usize) : Bool := x.val ≤ y.val

def core.cmp.impls.PartialOrdI8.le (x y : I8) : Bool := x.val ≤ y.val
def core.cmp.impls.PartialOrdI16.le (x y : I16) : Bool := x.val ≤ y.val
def core.cmp.impls.PartialOrdI32.le (x y : I32) : Bool := x.val ≤ y.val
def core.cmp.impls.PartialOrdI64.le (x y : I64) : Bool := x.val ≤ y.val
def core.cmp.impls.PartialOrdI128.le (x y : I128) : Bool := x.val ≤ y.val
def core.cmp.impls.PartialOrdIsize.le (x y : Isize) : Bool := x.val ≤ y.val

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::gt]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::gt -/
def core.cmp.impls.PartialOrdU8.gt (x y : U8) : Bool := x.val > y.val
def core.cmp.impls.PartialOrdU16.gt (x y : U16) : Bool := x.val > y.val
def core.cmp.impls.PartialOrdU32.gt (x y : U32) : Bool := x.val > y.val
def core.cmp.impls.PartialOrdU64.gt (x y : U64) : Bool := x.val > y.val
def core.cmp.impls.PartialOrdU128.gt (x y : U128) : Bool := x.val > y.val
def core.cmp.impls.PartialOrdUsize.gt (x y : Usize) : Bool := x.val > y.val

def core.cmp.impls.PartialOrdI8.gt (x y : I8) : Bool := x.val > y.val
def core.cmp.impls.PartialOrdI16.gt (x y : I16) : Bool := x.val > y.val
def core.cmp.impls.PartialOrdI32.gt (x y : I32) : Bool := x.val > y.val
def core.cmp.impls.PartialOrdI64.gt (x y : I64) : Bool := x.val > y.val
def core.cmp.impls.PartialOrdI128.gt (x y : I128) : Bool := x.val > y.val
def core.cmp.impls.PartialOrdIsize.gt (x y : Isize) : Bool := x.val > y.val

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::ge]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::ge -/
def core.cmp.impls.PartialOrdU8.ge (x y : U8) : Bool := x.val ≥ y.val
def core.cmp.impls.PartialOrdU16.ge (x y : U16) : Bool := x.val ≥ y.val
def core.cmp.impls.PartialOrdU32.ge (x y : U32) : Bool := x.val ≥ y.val
def core.cmp.impls.PartialOrdU64.ge (x y : U64) : Bool := x.val ≥ y.val
def core.cmp.impls.PartialOrdU128.ge (x y : U128) : Bool := x.val ≥ y.val
def core.cmp.impls.PartialOrdUsize.ge (x y : Usize) : Bool := x.val ≥ y.val

def core.cmp.impls.PartialOrdI8.ge (x y : I8) : Bool := x.val ≥ y.val
def core.cmp.impls.PartialOrdI16.ge (x y : I16) : Bool := x.val ≥ y.val
def core.cmp.impls.PartialOrdI32.ge (x y : I32) : Bool := x.val ≥ y.val
def core.cmp.impls.PartialOrdI64.ge (x y : I64) : Bool := x.val ≥ y.val
def core.cmp.impls.PartialOrdI128.ge (x y : I128) : Bool := x.val ≥ y.val
def core.cmp.impls.PartialOrdIsize.ge (x y : Isize) : Bool := x.val ≥ y.val

/- Trait implementation: [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}]
   Name pattern: core::cmp::PartialOrd<u8, u8> -/
@[reducible] def core.cmp.PartialOrdU8 : core.cmp.PartialOrd U8 U8 := {
  partialEqInst := core.cmp.PartialEqU8
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdU8.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdU8.lt
  le := liftFun2 core.cmp.impls.PartialOrdU8.le
  gt := liftFun2 core.cmp.impls.PartialOrdU8.gt
  ge := liftFun2 core.cmp.impls.PartialOrdU8.ge }

@[reducible] def core.cmp.PartialOrdU16 : core.cmp.PartialOrd U16 U16 := {
  partialEqInst := core.cmp.PartialEqU16
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdU16.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdU16.lt
  le := liftFun2 core.cmp.impls.PartialOrdU16.le
  gt := liftFun2 core.cmp.impls.PartialOrdU16.gt
  ge := liftFun2 core.cmp.impls.PartialOrdU16.ge }

@[reducible] def core.cmp.PartialOrdU32 : core.cmp.PartialOrd U32 U32 := {
  partialEqInst := core.cmp.PartialEqU32
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdU32.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdU32.lt
  le := liftFun2 core.cmp.impls.PartialOrdU32.le
  gt := liftFun2 core.cmp.impls.PartialOrdU32.gt
  ge := liftFun2 core.cmp.impls.PartialOrdU32.ge }

@[reducible] def core.cmp.PartialOrdU64 : core.cmp.PartialOrd U64 U64 := {
  partialEqInst := core.cmp.PartialEqU64
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdU64.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdU64.lt
  le := liftFun2 core.cmp.impls.PartialOrdU64.le
  gt := liftFun2 core.cmp.impls.PartialOrdU64.gt
  ge := liftFun2 core.cmp.impls.PartialOrdU64.ge }

@[reducible] def core.cmp.PartialOrdU128 : core.cmp.PartialOrd U128 U128 := {
  partialEqInst := core.cmp.PartialEqU128
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdU128.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdU128.lt
  le := liftFun2 core.cmp.impls.PartialOrdU128.le
  gt := liftFun2 core.cmp.impls.PartialOrdU128.gt
  ge := liftFun2 core.cmp.impls.PartialOrdU128.ge }

@[reducible] def core.cmp.PartialOrdUsize : core.cmp.PartialOrd Usize Usize := {
  partialEqInst := core.cmp.PartialEqUsize
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdUsize.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdUsize.lt
  le := liftFun2 core.cmp.impls.PartialOrdUsize.le
  gt := liftFun2 core.cmp.impls.PartialOrdUsize.gt
  ge := liftFun2 core.cmp.impls.PartialOrdUsize.ge }

@[reducible] def core.cmp.PartialOrdI8 : core.cmp.PartialOrd I8 I8 := {
  partialEqInst := core.cmp.PartialEqI8
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdI8.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdI8.lt
  le := liftFun2 core.cmp.impls.PartialOrdI8.le
  gt := liftFun2 core.cmp.impls.PartialOrdI8.gt
  ge := liftFun2 core.cmp.impls.PartialOrdI8.ge }

@[reducible] def core.cmp.PartialOrdI16 : core.cmp.PartialOrd I16 I16 := {
  partialEqInst := core.cmp.PartialEqI16
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdI16.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdI16.lt
  le := liftFun2 core.cmp.impls.PartialOrdI16.le
  gt := liftFun2 core.cmp.impls.PartialOrdI16.gt
  ge := liftFun2 core.cmp.impls.PartialOrdI16.ge }

@[reducible] def core.cmp.PartialOrdI32 : core.cmp.PartialOrd I32 I32 := {
  partialEqInst := core.cmp.PartialEqI32
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdI32.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdI32.lt
  le := liftFun2 core.cmp.impls.PartialOrdI32.le
  gt := liftFun2 core.cmp.impls.PartialOrdI32.gt
  ge := liftFun2 core.cmp.impls.PartialOrdI32.ge }

@[reducible] def core.cmp.PartialOrdI64 : core.cmp.PartialOrd I64 I64 := {
  partialEqInst := core.cmp.PartialEqI64
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdI64.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdI64.lt
  le := liftFun2 core.cmp.impls.PartialOrdI64.le
  gt := liftFun2 core.cmp.impls.PartialOrdI64.gt
  ge := liftFun2 core.cmp.impls.PartialOrdI64.ge }

@[reducible] def core.cmp.PartialOrdI128 : core.cmp.PartialOrd I128 I128 := {
  partialEqInst := core.cmp.PartialEqI128
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdI128.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdI128.lt
  le := liftFun2 core.cmp.impls.PartialOrdI128.le
  gt := liftFun2 core.cmp.impls.PartialOrdI128.gt
  ge := liftFun2 core.cmp.impls.PartialOrdI128.ge }

@[reducible] def core.cmp.PartialOrdIsize : core.cmp.PartialOrd Isize Isize := {
  partialEqInst := core.cmp.PartialEqIsize
  partial_cmp := liftFun2 core.cmp.impls.PartialOrdIsize.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrdIsize.lt
  le := liftFun2 core.cmp.impls.PartialOrdIsize.le
  gt := liftFun2 core.cmp.impls.PartialOrdIsize.gt
  ge := liftFun2 core.cmp.impls.PartialOrdIsize.ge }

/- Name pattern: core::cmp::impls::{core::cmp::Ord<SCALAR>}::min -/
def core.cmp.impls.OrdU8.min (x y : U8) : U8 := if x < y then x else y
def core.cmp.impls.OrdU16.min (x y : U16) : U16 := if x < y then x else y
def core.cmp.impls.OrdU32.min (x y : U32) : U32 := if x < y then x else y
def core.cmp.impls.OrdU64.min (x y : U64) : U64 := if x < y then x else y
def core.cmp.impls.OrdU128.min (x y : U128) : U128 := if x < y then x else y
def core.cmp.impls.OrdUsize.min (x y : Usize) : Usize := if x < y then x else y
def core.cmp.impls.OrdI8.min (x y : I8) : I8 := if x < y then x else y
def core.cmp.impls.OrdI16.min (x y : I16) : I16 := if x < y then x else y
def core.cmp.impls.OrdI32.min (x y : I32) : I32 := if x < y then x else y
def core.cmp.impls.OrdI64.min (x y : I64) : I64 := if x < y then x else y
def core.cmp.impls.OrdI128.min (x y : I128) : I128 := if x < y then x else y
def core.cmp.impls.OrdIsize.min (x y : Isize) : Isize := if x < y then x else y

/- Name pattern: core::cmp::impls::{core::cmp::Ord<SCALAR>}::max -/
def core.cmp.impls.OrdU8.max (x y : U8) : U8 := if x < y then y else x
def core.cmp.impls.OrdU16.max (x y : U16) : U16 := if x < y then y else x
def core.cmp.impls.OrdU32.max (x y : U32) : U32 := if x < y then y else x
def core.cmp.impls.OrdU64.max (x y : U64) : U64 := if x < y then y else x
def core.cmp.impls.OrdU128.max (x y : U128) : U128 := if x < y then y else x
def core.cmp.impls.OrdUsize.max (x y : Usize) : Usize := if x < y then y else x
def core.cmp.impls.OrdI8.max (x y : I8) : I8 := if x < y then y else x
def core.cmp.impls.OrdI16.max (x y : I16) : I16 := if x < y then y else x
def core.cmp.impls.OrdI32.max (x y : I32) : I32 := if x < y then y else x
def core.cmp.impls.OrdI64.max (x y : I64) : I64 := if x < y then y else x
def core.cmp.impls.OrdI128.max (x y : I128) : I128 := if x < y then y else x
def core.cmp.impls.OrdIsize.max (x y : Isize) : Isize := if x < y then y else x

/- Name pattern: core::cmp::impls::{core::cmp::Ord<SCALAR>}::clamp -/
def UScalar.clamp {ty} (self min max : UScalar ty) : Result (UScalar ty) := do
  massert (min.val ≤ max.val)
  if self.val < min.val then ok min
  else if self.val > max.val then ok max
  else ok self

def IScalar.clamp {ty} (self min max : IScalar ty) : Result (IScalar ty) := do
  massert (min.val ≤ max.val)
  if self.val < min.val then ok min
  else if self.val > max.val then ok max
  else ok self

def core.cmp.impls.OrdU8.clamp (self min max : U8) : Result U8 := UScalar.clamp self min max
def core.cmp.impls.OrdU16.clamp (self min max : U16) : Result U16 := UScalar.clamp self min max
def core.cmp.impls.OrdU32.clamp (self min max : U32) : Result U32 := UScalar.clamp self min max
def core.cmp.impls.OrdU64.clamp (self min max : U64) : Result U64 := UScalar.clamp self min max
def core.cmp.impls.OrdU128.clamp (self min max : U128) : Result U128 := UScalar.clamp self min max
def core.cmp.impls.OrdUsize.clamp (self min max : Usize) : Result Usize := UScalar.clamp self min max
def core.cmp.impls.OrdI8.clamp (self min max : I8) : Result I8 := IScalar.clamp self min max
def core.cmp.impls.OrdI16.clamp (self min max : I16) : Result I16 := IScalar.clamp self min max
def core.cmp.impls.OrdI32.clamp (self min max : I32) : Result I32 := IScalar.clamp self min max
def core.cmp.impls.OrdI64.clamp (self min max : I64) : Result I64 := IScalar.clamp self min max
def core.cmp.impls.OrdI128.clamp (self min max : I128) : Result I128 := IScalar.clamp self min max
def core.cmp.impls.OrdIsize.clamp (self min max : Isize) : Result Isize := IScalar.clamp self min max

/- Trait implementation: [core::cmp::impls::{core::cmp::Ord for u8}]
   Name pattern: core::cmp::Ord<u8> -/
@[reducible] def core.cmp.OrdU8 : core.cmp.Ord U8 := {
  eqInst := core.cmp.EqU8
  partialOrdInst := core.cmp.PartialOrdU8
  cmp := liftFun2 core.cmp.impls.OrdU8.cmp
  max := liftFun2 core.cmp.impls.OrdU8.max
  min := liftFun2 core.cmp.impls.OrdU8.min
  clamp := core.cmp.impls.OrdU8.clamp }

@[reducible] def core.cmp.OrdU16 : core.cmp.Ord U16 := {
  eqInst := core.cmp.EqU16
  partialOrdInst := core.cmp.PartialOrdU16
  cmp := liftFun2 core.cmp.impls.OrdU16.cmp
  max := liftFun2 core.cmp.impls.OrdU16.max
  min := liftFun2 core.cmp.impls.OrdU16.min
  clamp := core.cmp.impls.OrdU16.clamp }

@[reducible] def core.cmp.OrdU32 : core.cmp.Ord U32 := {
  eqInst := core.cmp.EqU32
  partialOrdInst := core.cmp.PartialOrdU32
  cmp := liftFun2 core.cmp.impls.OrdU32.cmp
  max := liftFun2 core.cmp.impls.OrdU32.max
  min := liftFun2 core.cmp.impls.OrdU32.min
  clamp := core.cmp.impls.OrdU32.clamp}

@[reducible] def core.cmp.OrdU64 : core.cmp.Ord U64 := {
  eqInst := core.cmp.EqU64
  partialOrdInst := core.cmp.PartialOrdU64
  cmp := liftFun2 core.cmp.impls.OrdU64.cmp
  max := liftFun2 core.cmp.impls.OrdU64.max
  min := liftFun2 core.cmp.impls.OrdU64.min
  clamp := core.cmp.impls.OrdU64.clamp }

@[reducible] def core.cmp.OrdU128 : core.cmp.Ord U128 := {
  eqInst := core.cmp.EqU128
  partialOrdInst := core.cmp.PartialOrdU128
  cmp := liftFun2 core.cmp.impls.OrdU128.cmp
  max := liftFun2 core.cmp.impls.OrdU128.max
  min := liftFun2 core.cmp.impls.OrdU128.min
  clamp := core.cmp.impls.OrdU128.clamp }

@[reducible] def core.cmp.OrdUsize : core.cmp.Ord Usize := {
  eqInst := core.cmp.EqUsize
  partialOrdInst := core.cmp.PartialOrdUsize
  cmp := liftFun2 core.cmp.impls.OrdUsize.cmp
  max := liftFun2 core.cmp.impls.OrdUsize.max
  min := liftFun2 core.cmp.impls.OrdUsize.min
  clamp := core.cmp.impls.OrdUsize.clamp }

@[reducible] def core.cmp.OrdI8 : core.cmp.Ord I8 := {
  eqInst := core.cmp.EqI8
  partialOrdInst := core.cmp.PartialOrdI8
  cmp := liftFun2 core.cmp.impls.OrdI8.cmp
  max := liftFun2 core.cmp.impls.OrdI8.max
  min := liftFun2 core.cmp.impls.OrdI8.min
  clamp := core.cmp.impls.OrdI8.clamp }

@[reducible] def core.cmp.OrdI16 : core.cmp.Ord I16 := {
  eqInst := core.cmp.EqI16
  partialOrdInst := core.cmp.PartialOrdI16
  cmp := liftFun2 core.cmp.impls.OrdI16.cmp
  max := liftFun2 core.cmp.impls.OrdI16.max
  min := liftFun2 core.cmp.impls.OrdI16.min
  clamp := core.cmp.impls.OrdI16.clamp }

@[reducible] def core.cmp.OrdI32 : core.cmp.Ord I32 := {
  eqInst := core.cmp.EqI32
  partialOrdInst := core.cmp.PartialOrdI32
  cmp := liftFun2 core.cmp.impls.OrdI32.cmp
  max := liftFun2 core.cmp.impls.OrdI32.max
  min := liftFun2 core.cmp.impls.OrdI32.min
  clamp := core.cmp.impls.OrdI32.clamp }

@[reducible] def core.cmp.OrdI64 : core.cmp.Ord I64 := {
  eqInst := core.cmp.EqI64
  partialOrdInst := core.cmp.PartialOrdI64
  cmp := liftFun2 core.cmp.impls.OrdI64.cmp
  max := liftFun2 core.cmp.impls.OrdI64.max
  min := liftFun2 core.cmp.impls.OrdI64.min
  clamp := core.cmp.impls.OrdI64.clamp }

@[reducible] def core.cmp.OrdI128 : core.cmp.Ord I128 := {
  eqInst := core.cmp.EqI128
  partialOrdInst := core.cmp.PartialOrdI128
  cmp := liftFun2 core.cmp.impls.OrdI128.cmp
  max := liftFun2 core.cmp.impls.OrdI128.max
  min := liftFun2 core.cmp.impls.OrdI128.min
  clamp := core.cmp.impls.OrdI128.clamp }

@[reducible] def core.cmp.OrdIsize : core.cmp.Ord Isize := {
  eqInst := core.cmp.EqIsize
  partialOrdInst := core.cmp.PartialOrdIsize
  cmp := liftFun2 core.cmp.impls.OrdIsize.cmp
  max := liftFun2 core.cmp.impls.OrdIsize.max
  min := liftFun2 core.cmp.impls.OrdIsize.min
  clamp := core.cmp.impls.OrdIsize.clamp }

end Aeneas.Std
