module

public import Lean
public import AeneasMeta.BvEnumToBitVec

public section

namespace Aeneas.Std

/-- Kinds of unsigned integers. Kept independent of the effectful scalar operations. -/
inductive UScalarTy where
  | Usize
  | U8
  | U16
  | U32
  | U64
  | U128
  deriving BvEnumToBitVec

@[expose, implicit_reducible]
def UScalarTy.numBits (ty : UScalarTy) : Nat :=
  match ty with
  | Usize => System.Platform.numBits
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  | U128 => 128

/-- Unsigned integer. -/
structure UScalar (ty : UScalarTy) where
  bv : BitVec ty.numBits
  deriving Repr, BEq, DecidableEq

@[expose, implicit_reducible]
def UScalar.val {ty} (x : UScalar ty) : Nat := x.bv.toNat

abbrev Usize := UScalar .Usize
abbrev U8 := UScalar .U8
abbrev U16 := UScalar .U16
abbrev U32 := UScalar .U32
abbrev U64 := UScalar .U64
abbrev U128 := UScalar .U128

end Aeneas.Std
