import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

open Result Error

/-!
# Clone and Copy
-/

@[reducible, simp] def core.clone.impls.CloneUsize.clone (x : Usize) : Usize := x
@[reducible, simp] def core.clone.impls.CloneU8.clone (x : U8) : U8 := x
@[reducible, simp] def core.clone.impls.CloneU16.clone (x : U16) : U16 := x
@[reducible, simp] def core.clone.impls.CloneU32.clone (x : U32) : U32 := x
@[reducible, simp] def core.clone.impls.CloneU64.clone (x : U64) : U64 := x
@[reducible, simp] def core.clone.impls.CloneU128.clone (x : U128) : U128 := x

@[reducible, simp] def core.clone.impls.CloneUsize.clone_from (_ x : Usize) : Usize := x
@[reducible, simp] def core.clone.impls.CloneU8.clone_from (_ x : U8) : U8 := x
@[reducible, simp] def core.clone.impls.CloneU16.clone_from (_ x : U16) : U16 := x
@[reducible, simp] def core.clone.impls.CloneU32.clone_from (_ x : U32) : U32 := x
@[reducible, simp] def core.clone.impls.CloneU64.clone_from (_ x : U64) : U64 := x
@[reducible, simp] def core.clone.impls.CloneU128.clone_from (_ x : U128) : U128 := x

@[reducible, simp] def core.clone.impls.CloneIsize.clone (x : Isize) : Isize := x
@[reducible, simp] def core.clone.impls.CloneI8.clone (x : I8) : I8 := x
@[reducible, simp] def core.clone.impls.CloneI16.clone (x : I16) : I16 := x
@[reducible, simp] def core.clone.impls.CloneI32.clone (x : I32) : I32 := x
@[reducible, simp] def core.clone.impls.CloneI64.clone (x : I64) : I64 := x
@[reducible, simp] def core.clone.impls.CloneI128.clone (x : I128) : I128 := x

@[reducible, simp] def core.clone.impls.CloneIsize.clone_from (_ x : Isize) : Isize := x
@[reducible, simp] def core.clone.impls.CloneI8.clone_from (_ x : I8) : I8 := x
@[reducible, simp] def core.clone.impls.CloneI16.clone_from (_ x : I16) : I16 := x
@[reducible, simp] def core.clone.impls.CloneI32.clone_from (_ x : I32) : I32 := x
@[reducible, simp] def core.clone.impls.CloneI64.clone_from (_ x : I64) : I64 := x
@[reducible, simp] def core.clone.impls.CloneI128.clone_from (_ x : I128) : I128 := x

@[reducible] def core.clone.CloneU8 : core.clone.Clone U8 := {
  clone := liftFun1 core.clone.impls.CloneU8.clone
  clone_from := liftFun2 core.clone.impls.CloneU8.clone_from }

@[reducible] def core.clone.CloneU16 : core.clone.Clone U16 := {
  clone := liftFun1 core.clone.impls.CloneU16.clone
  clone_from := liftFun2 core.clone.impls.CloneU16.clone_from }

@[reducible] def core.clone.CloneU32 : core.clone.Clone U32 := {
  clone := liftFun1 core.clone.impls.CloneU32.clone
  clone_from := liftFun2 core.clone.impls.CloneU32.clone_from }

@[reducible] def core.clone.CloneU64 : core.clone.Clone U64 := {
  clone := liftFun1 core.clone.impls.CloneU64.clone
  clone_from := liftFun2 core.clone.impls.CloneU64.clone_from }

@[reducible] def core.clone.CloneU128 : core.clone.Clone U128 := {
  clone := liftFun1 core.clone.impls.CloneU128.clone
  clone_from := liftFun2 core.clone.impls.CloneU128.clone_from }

@[reducible] def core.clone.CloneUsize : core.clone.Clone Usize := {
  clone := liftFun1 core.clone.impls.CloneUsize.clone
  clone_from := liftFun2 core.clone.impls.CloneUsize.clone_from }

@[reducible] def core.clone.CloneI8 : core.clone.Clone I8 := {
  clone := liftFun1 core.clone.impls.CloneI8.clone
  clone_from := liftFun2 core.clone.impls.CloneI8.clone_from }

@[reducible] def core.clone.CloneI16 : core.clone.Clone I16 := {
  clone := liftFun1 core.clone.impls.CloneI16.clone
  clone_from := liftFun2 core.clone.impls.CloneI16.clone_from }

@[reducible] def core.clone.CloneI32 : core.clone.Clone I32 := {
  clone := liftFun1 core.clone.impls.CloneI32.clone
  clone_from := liftFun2 core.clone.impls.CloneI32.clone_from }

@[reducible] def core.clone.CloneI64 : core.clone.Clone I64 := {
  clone := liftFun1 core.clone.impls.CloneI64.clone
  clone_from := liftFun2 core.clone.impls.CloneI64.clone_from }

@[reducible] def core.clone.CloneI128 : core.clone.Clone I128 := {
  clone := liftFun1 core.clone.impls.CloneI128.clone
  clone_from := liftFun2 core.clone.impls.CloneI128.clone_from }

@[reducible] def core.clone.CloneIsize : core.clone.Clone Isize := {
  clone := liftFun1 core.clone.impls.CloneIsize.clone
  clone_from := liftFun2 core.clone.impls.CloneIsize.clone_from }

@[reducible]
def core.marker.CopyU8 : core.marker.Copy U8 := {
  cloneInst := core.clone.CloneU8
}

@[reducible]
def core.marker.CopyU16 : core.marker.Copy U16 := {
  cloneInst := core.clone.CloneU16
}

@[reducible]
def core.marker.CopyU32 : core.marker.Copy U32 := {
  cloneInst := core.clone.CloneU32
}

@[reducible]
def core.marker.CopyU64 : core.marker.Copy U64 := {
  cloneInst := core.clone.CloneU64
}

@[reducible]
def core.marker.CopyU128 : core.marker.Copy U128 := {
  cloneInst := core.clone.CloneU128
}

@[reducible]
def core.marker.CopyUsize : core.marker.Copy Usize := {
  cloneInst := core.clone.CloneUsize
}

@[reducible]
def core.marker.CopyI8 : core.marker.Copy I8 := {
  cloneInst := core.clone.CloneI8
}

@[reducible]
def core.marker.CopyI16 : core.marker.Copy I16 := {
  cloneInst := core.clone.CloneI16
}

@[reducible]
def core.marker.CopyI32 : core.marker.Copy I32 := {
  cloneInst := core.clone.CloneI32
}

@[reducible]
def core.marker.CopyI64 : core.marker.Copy I64 := {
  cloneInst := core.clone.CloneI64
}

@[reducible]
def core.marker.CopyI128 : core.marker.Copy I128 := {
  cloneInst := core.clone.CloneI128
}

@[reducible]
def core.marker.CopyIsize : core.marker.Copy Isize := {
  cloneInst := core.clone.CloneIsize
}

end Aeneas.Std
