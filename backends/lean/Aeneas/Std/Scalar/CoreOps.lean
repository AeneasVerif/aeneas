module
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Scalar.Bitwise
public import Aeneas.Std.Scalar.Ops
public section

/-! The `core::ops` traits for the integer types (see `core_ops_int_impls` in
`ExtractBuiltin.ml` for the names). -/

namespace Aeneas.Std

open Result Error Arith ScalarElab

scalar @[expose] def «%S».Insts.«CoreOpsArithAdd'S'S».add (x y : «%S») : Result «%S» :=
  x + y

scalar @[expose, reducible] def «%S».Insts.«CoreOpsArithAdd'S'S» : core.ops.arith.Add «%S» «%S» «%S» := {
  add := «%S».Insts.«CoreOpsArithAdd'S'S».add
}

scalar @[expose] def «%S».Insts.«CoreOpsArithAddAssign'S».add_assign (x y : «%S») : Result «%S» :=
  x + y

scalar @[expose, reducible] def «%S».Insts.«CoreOpsArithAddAssign'S» : core.ops.arith.AddAssign «%S» «%S» := {
  add_assign := «%S».Insts.«CoreOpsArithAddAssign'S».add_assign
}

scalar @[expose] def «%S».Insts.«CoreOpsArithSub'S'S».sub (x y : «%S») : Result «%S» :=
  x - y

scalar @[expose, reducible] def «%S».Insts.«CoreOpsArithSub'S'S» : core.ops.arith.Sub «%S» «%S» «%S» := {
  sub := «%S».Insts.«CoreOpsArithSub'S'S».sub
}

scalar @[expose] def «%S».Insts.«CoreOpsArithSubAssign'S».sub_assign (x y : «%S») : Result «%S» :=
  x - y

scalar @[expose, reducible] def «%S».Insts.«CoreOpsArithSubAssign'S» : core.ops.arith.SubAssign «%S» «%S» := {
  sub_assign := «%S».Insts.«CoreOpsArithSubAssign'S».sub_assign
}

scalar @[expose] def «%S».Insts.«CoreOpsArithMul'S'S».mul (x y : «%S») : Result «%S» :=
  x * y

scalar @[expose, reducible] def «%S».Insts.«CoreOpsArithMul'S'S» : core.ops.arith.Mul «%S» «%S» «%S» := {
  mul := «%S».Insts.«CoreOpsArithMul'S'S».mul
}

scalar @[expose] def «%S».Insts.«CoreOpsArithMulAssign'S».mul_assign (x y : «%S») : Result «%S» :=
  x * y

scalar @[expose, reducible] def «%S».Insts.«CoreOpsArithMulAssign'S» : core.ops.arith.MulAssign «%S» «%S» := {
  mul_assign := «%S».Insts.«CoreOpsArithMulAssign'S».mul_assign
}

scalar @[expose] def «%S».Insts.«CoreOpsArithDiv'S'S».div (x y : «%S») : Result «%S» :=
  x / y

scalar @[expose, reducible] def «%S».Insts.«CoreOpsArithDiv'S'S» : core.ops.arith.Div «%S» «%S» «%S» := {
  div := «%S».Insts.«CoreOpsArithDiv'S'S».div
}

scalar @[expose] def «%S».Insts.«CoreOpsArithDivAssign'S».div_assign (x y : «%S») : Result «%S» :=
  x / y

scalar @[expose, reducible] def «%S».Insts.«CoreOpsArithDivAssign'S» : core.ops.arith.DivAssign «%S» «%S» := {
  div_assign := «%S».Insts.«CoreOpsArithDivAssign'S».div_assign
}

scalar @[expose] def «%S».Insts.«CoreOpsBitBitAnd'S'S».bitand (x y : «%S») : Result «%S» :=
  ok (x &&& y)

scalar @[expose, reducible] def «%S».Insts.«CoreOpsBitBitAnd'S'S» : core.ops.bit.BitAnd «%S» «%S» «%S» := {
  bitand := «%S».Insts.«CoreOpsBitBitAnd'S'S».bitand
}

scalar @[expose] def «%S».Insts.«CoreOpsBitBitAndAssign'S».bitand_assign (x y : «%S») : Result «%S» :=
  ok (x &&& y)

scalar @[expose, reducible] def «%S».Insts.«CoreOpsBitBitAndAssign'S» : core.ops.bit.BitAndAssign «%S» «%S» := {
  bitand_assign := «%S».Insts.«CoreOpsBitBitAndAssign'S».bitand_assign
}

scalar @[expose] def «%S».Insts.«CoreOpsBitBitOr'S'S».bitor (x y : «%S») : Result «%S» :=
  ok (x ||| y)

scalar @[expose, reducible] def «%S».Insts.«CoreOpsBitBitOr'S'S» : core.ops.bit.BitOr «%S» «%S» «%S» := {
  bitor := «%S».Insts.«CoreOpsBitBitOr'S'S».bitor
}

scalar @[expose] def «%S».Insts.«CoreOpsBitBitOrAssign'S».bitor_assign (x y : «%S») : Result «%S» :=
  ok (x ||| y)

scalar @[expose, reducible] def «%S».Insts.«CoreOpsBitBitOrAssign'S» : core.ops.bit.BitOrAssign «%S» «%S» := {
  bitor_assign := «%S».Insts.«CoreOpsBitBitOrAssign'S».bitor_assign
}

scalar @[expose] def «%S».Insts.«CoreOpsBitBitXor'S'S».bitxor (x y : «%S») : Result «%S» :=
  ok (x ^^^ y)

scalar @[expose, reducible] def «%S».Insts.«CoreOpsBitBitXor'S'S» : core.ops.bit.BitXor «%S» «%S» «%S» := {
  bitxor := «%S».Insts.«CoreOpsBitBitXor'S'S».bitxor
}

scalar @[expose] def «%S».Insts.«CoreOpsBitBitXorAssign'S».bitxor_assign (x y : «%S») : Result «%S» :=
  ok (x ^^^ y)

scalar @[expose, reducible] def «%S».Insts.«CoreOpsBitBitXorAssign'S» : core.ops.bit.BitXorAssign «%S» «%S» := {
  bitxor_assign := «%S».Insts.«CoreOpsBitBitXorAssign'S».bitxor_assign
}
scalar scalar_rhs @[expose] def «%S».Insts.«CoreOpsBitShl'R'S».shl (x : «%S») (y : «%R») : Result «%S» :=
  x <<< y

scalar scalar_rhs @[expose, reducible] def «%S».Insts.«CoreOpsBitShl'R'S» : core.ops.bit.Shl «%S» «%R» «%S» := {
  shl := «%S».Insts.«CoreOpsBitShl'R'S».shl
}

scalar scalar_rhs @[expose] def «%S».Insts.«CoreOpsBitShr'R'S».shr (x : «%S») (y : «%R») : Result «%S» :=
  x >>> y

scalar scalar_rhs @[expose, reducible] def «%S».Insts.«CoreOpsBitShr'R'S» : core.ops.bit.Shr «%S» «%R» «%S» := {
  shr := «%S».Insts.«CoreOpsBitShr'R'S».shr
}

end Aeneas.Std
