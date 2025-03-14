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

/- Trait implementation: [core::cmp::impls::{core::cmp::PartialEq<u8> for u8}]
   Name pattern: core::cmp::PartialEq<u8, u8> -/
@[reducible] def core.cmp.PartialEqU8 : core.cmp.PartialEq U8 U8 := {
  eq x y := ok (core.cmp.impls.PartialEqU8.eq x y) }

@[reducible] def core.cmp.PartialEqU16 : core.cmp.PartialEq U16 U16 := {
  eq x y := ok (core.cmp.impls.PartialEqU16.eq x y) }

@[reducible] def core.cmp.PartialEqU32 : core.cmp.PartialEq U32 U32 := {
  eq x y := ok (core.cmp.impls.PartialEqU32.eq x y) }

@[reducible] def core.cmp.PartialEqU64 : core.cmp.PartialEq U64 U64 := {
  eq x y := ok (core.cmp.impls.PartialEqU64.eq x y) }

@[reducible] def core.cmp.PartialEqU128 : core.cmp.PartialEq U128 U128 := {
  eq x y := ok (core.cmp.impls.PartialEqU128.eq x y) }

@[reducible] def core.cmp.PartialEqUsize : core.cmp.PartialEq Usize Usize := {
  eq x y := ok (core.cmp.impls.PartialEqUsize.eq x y) }

@[reducible] def core.cmp.PartialEqI8 : core.cmp.PartialEq I8 I8 := {
  eq x y := ok (core.cmp.impls.PartialEqI8.eq x y) }

@[reducible] def core.cmp.PartialEqI16 : core.cmp.PartialEq I16 I16 := {
  eq x y := ok (core.cmp.impls.PartialEqI16.eq x y) }

@[reducible] def core.cmp.PartialEqI32 : core.cmp.PartialEq I32 I32 := {
  eq x y := ok (core.cmp.impls.PartialEqI32.eq x y) }

@[reducible] def core.cmp.PartialEqI64 : core.cmp.PartialEq I64 I64 := {
  eq x y := ok (core.cmp.impls.PartialEqI64.eq x y) }

@[reducible] def core.cmp.PartialEqI128 : core.cmp.PartialEq I128 I128 := {
  eq x y := ok (core.cmp.impls.PartialEqI128.eq x y) }

@[reducible] def core.cmp.PartialEqIsize : core.cmp.PartialEq Isize Isize := {
  eq x y := ok (core.cmp.impls.PartialEqIsize.eq x y) }

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

/- Trait implementation: [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}]
   Name pattern: core::cmp::PartialOrd<u8, u8> -/
@[reducible] def core.cmp.PartialOrdU8 : core.cmp.PartialOrd U8 U8 := {
  partialEqInst := core.cmp.PartialEqU8
  partial_cmp x y := ok (core.cmp.impls.PartialOrdU8.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdU16 : core.cmp.PartialOrd U16 U16 := {
  partialEqInst := core.cmp.PartialEqU16
  partial_cmp x y := ok (core.cmp.impls.PartialOrdU16.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdU32 : core.cmp.PartialOrd U32 U32 := {
  partialEqInst := core.cmp.PartialEqU32
  partial_cmp x y := ok (core.cmp.impls.PartialOrdU32.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdU64 : core.cmp.PartialOrd U64 U64 := {
  partialEqInst := core.cmp.PartialEqU64
  partial_cmp x y := ok (core.cmp.impls.PartialOrdU64.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdU128 : core.cmp.PartialOrd U128 U128 := {
  partialEqInst := core.cmp.PartialEqU128
  partial_cmp x y := ok (core.cmp.impls.PartialOrdU128.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdUsize : core.cmp.PartialOrd Usize Usize := {
  partialEqInst := core.cmp.PartialEqUsize
  partial_cmp x y := ok (core.cmp.impls.PartialOrdUsize.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdI8 : core.cmp.PartialOrd I8 I8 := {
  partialEqInst := core.cmp.PartialEqI8
  partial_cmp x y := ok (core.cmp.impls.PartialOrdI8.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdI16 : core.cmp.PartialOrd I16 I16 := {
  partialEqInst := core.cmp.PartialEqI16
  partial_cmp x y := ok (core.cmp.impls.PartialOrdI16.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdI32 : core.cmp.PartialOrd I32 I32 := {
  partialEqInst := core.cmp.PartialEqI32
  partial_cmp x y := ok (core.cmp.impls.PartialOrdI32.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdI64 : core.cmp.PartialOrd I64 I64 := {
  partialEqInst := core.cmp.PartialEqI64
  partial_cmp x y := ok (core.cmp.impls.PartialOrdI64.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdI128 : core.cmp.PartialOrd I128 I128 := {
  partialEqInst := core.cmp.PartialEqI128
  partial_cmp x y := ok (core.cmp.impls.PartialOrdI128.partial_cmp x y) }

@[reducible] def core.cmp.PartialOrdIsize : core.cmp.PartialOrd Isize Isize := {
  partialEqInst := core.cmp.PartialEqIsize
  partial_cmp x y := ok (core.cmp.impls.PartialOrdIsize.partial_cmp x y) }

/- Trait implementation: [core::cmp::impls::{core::cmp::Ord for u8}]
   Name pattern: core::cmp::Ord<u8> -/
@[reducible] def core.cmp.OrdU8 : core.cmp.Ord U8 := {
  eqInst := core.cmp.EqU8
  partialOrdInst := core.cmp.PartialOrdU8
  cmp x y := ok (core.cmp.impls.OrdU8.cmp x y) }

@[reducible] def core.cmp.OrdU16 : core.cmp.Ord U16 := {
  eqInst := core.cmp.EqU16
  partialOrdInst := core.cmp.PartialOrdU16
  cmp x y := ok (core.cmp.impls.OrdU16.cmp x y) }

@[reducible] def core.cmp.OrdU32 : core.cmp.Ord U32 := {
  eqInst := core.cmp.EqU32
  partialOrdInst := core.cmp.PartialOrdU32
  cmp x y := ok (core.cmp.impls.OrdU32.cmp x y) }

@[reducible] def core.cmp.OrdU64 : core.cmp.Ord U64 := {
  eqInst := core.cmp.EqU64
  partialOrdInst := core.cmp.PartialOrdU64
  cmp x y := ok (core.cmp.impls.OrdU64.cmp x y) }

@[reducible] def core.cmp.OrdU128 : core.cmp.Ord U128 := {
  eqInst := core.cmp.EqU128
  partialOrdInst := core.cmp.PartialOrdU128
  cmp x y := ok (core.cmp.impls.OrdU128.cmp x y) }

@[reducible] def core.cmp.OrdUsize : core.cmp.Ord Usize := {
  eqInst := core.cmp.EqUsize
  partialOrdInst := core.cmp.PartialOrdUsize
  cmp x y := ok (core.cmp.impls.OrdUsize.cmp x y) }

@[reducible] def core.cmp.OrdI8 : core.cmp.Ord I8 := {
  eqInst := core.cmp.EqI8
  partialOrdInst := core.cmp.PartialOrdI8
  cmp x y := ok (core.cmp.impls.OrdI8.cmp x y) }

@[reducible] def core.cmp.OrdI16 : core.cmp.Ord I16 := {
  eqInst := core.cmp.EqI16
  partialOrdInst := core.cmp.PartialOrdI16
  cmp x y := ok (core.cmp.impls.OrdI16.cmp x y) }

@[reducible] def core.cmp.OrdI32 : core.cmp.Ord I32 := {
  eqInst := core.cmp.EqI32
  partialOrdInst := core.cmp.PartialOrdI32
  cmp x y := ok (core.cmp.impls.OrdI32.cmp x y) }

@[reducible] def core.cmp.OrdI64 : core.cmp.Ord I64 := {
  eqInst := core.cmp.EqI64
  partialOrdInst := core.cmp.PartialOrdI64
  cmp x y := ok (core.cmp.impls.OrdI64.cmp x y) }

@[reducible] def core.cmp.OrdI128 : core.cmp.Ord I128 := {
  eqInst := core.cmp.EqI128
  partialOrdInst := core.cmp.PartialOrdI128
  cmp x y := ok (core.cmp.impls.OrdI128.cmp x y) }

@[reducible] def core.cmp.OrdIsize : core.cmp.Ord Isize := {
  eqInst := core.cmp.EqIsize
  partialOrdInst := core.cmp.PartialOrdIsize
  cmp x y := ok (core.cmp.impls.OrdIsize.cmp x y) }

end Aeneas.Std
