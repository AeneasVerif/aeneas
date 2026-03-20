import Aeneas.Tactic.Solver.BvTac.BvTac

/-!
# Simprocs for scalar bitwise operations

General-purpose simprocs that reduce bitwise operations on scalar literals
by computation, replacing type-specific lemmas.
-/

section
open Lean Meta in

/-- Check if an expression is a numeric literal (Nat or Int, possibly negated). -/
private def isNumLit : Lean.Expr → Bool
  | Lean.Expr.lit (.natVal _) => true
  | Lean.Expr.app f a => isNumLit f || isNumLit a
  | Lean.Expr.const ``Nat.zero _ => true
  | _ => false

/-- Check if an expression is a scalar literal (without whnf). Matches the
    elaborated form of `n#u8`, `n#i32`, etc. which is `U8.ofNat n proof`
    or `I32.ofInt n proof`. -/
private def isScalarLit (x : Lean.Expr) : Bool :=
  match x with
  | Lean.Expr.app (Lean.Expr.app _ value) _ => isNumLit value
  | _ => false

end

section
open Lean Meta in

/-- Reduce `~~~(literal)` for UScalar types by computation. -/
simproc reduceUScalarNot (@Complement.complement (Aeneas.Std.UScalar _) _ _) := fun e => do
  match e.consumeMData.getAppFnArgs with
  | (``Complement.complement, #[_, _, x]) =>
    unless isScalarLit x do return .continue
    let reduced ← withTransparency .all (whnf e)
    if reduced == e then return .continue
    return .done { expr := reduced }
  | _ => return .continue

attribute [simp, simp_scalar_simps, bvify_simps] reduceUScalarNot

end

section
open Lean Meta in

/-- Reduce `~~~(literal)` for IScalar types by computation. -/
simproc reduceIScalarNot (@Complement.complement (Aeneas.Std.IScalar _) _ _) := fun e => do
  match e.consumeMData.getAppFnArgs with
  | (``Complement.complement, #[_, _, x]) =>
    unless isScalarLit x do return .continue
    let reduced ← withTransparency .all (whnf e)
    if reduced == e then return .continue
    return .done { expr := reduced }
  | _ => return .continue

attribute [simp, simp_scalar_simps, bvify_simps] reduceIScalarNot

end

-- Tests
section
open Aeneas.Std

-- UScalar: ~~~0 = maxVal
example : ~~~(0#u8 : U8) = 255#u8 := by native_decide
example : ~~~(0#u16 : U16) = 65535#u16 := by native_decide
example : ~~~(0#u32 : U32) = 4294967295#u32 := by native_decide
example : ~~~(0#u64 : U64) = 18446744073709551615#u64 := by native_decide
example : ~~~(0#u128 : U128) = 340282366920938463463374607431768211455#u128 := by native_decide

-- UScalar: ~~~maxVal = 0
example : ~~~(255#u8 : U8) = 0#u8 := by native_decide
example : ~~~(65535#u16 : U16) = 0#u16 := by native_decide
example : ~~~(4294967295#u32 : U32) = 0#u32 := by native_decide
example : ~~~(18446744073709551615#u64 : U64) = 0#u64 := by native_decide
example : ~~~(340282366920938463463374607431768211455#u128 : U128) = 0#u128 := by native_decide

-- UScalar: arbitrary literals
example : ~~~(42#u8 : U8) = 213#u8 := by native_decide
example : ~~~(1#u32 : U32) = 4294967294#u32 := by native_decide
example : ~~~(0xF0#u8 : U8) = 0x0F#u8 := by native_decide

-- IScalar: ~~~0 = -1
example : ~~~(0#i8 : I8) = (-1)#i8 := by native_decide
example : ~~~(0#i16 : I16) = (-1)#i16 := by native_decide
example : ~~~(0#i32 : I32) = (-1)#i32 := by native_decide
example : ~~~(0#i64 : I64) = (-1)#i64 := by native_decide
example : ~~~(0#i128 : I128) = (-1)#i128 := by native_decide

-- IScalar: ~~~(-1) = 0
example : ~~~((-1)#i8 : I8) = 0#i8 := by native_decide
example : ~~~((-1)#i16 : I16) = 0#i16 := by native_decide
example : ~~~((-1)#i32 : I32) = 0#i32 := by native_decide
example : ~~~((-1)#i64 : I64) = 0#i64 := by native_decide
example : ~~~((-1)#i128 : I128) = 0#i128 := by native_decide

-- IScalar: arbitrary literals
example : ~~~(1#i8 : I8) = (-2)#i8 := by native_decide
example : ~~~(42#i32 : I32) = (-43)#i32 := by native_decide
example : ~~~((-42)#i32 : I32) = 41#i32 := by native_decide
example : ~~~(127#i8 : I8) = (-128)#i8 := by native_decide

-- Large values
example : ~~~(0xDEADBEEF#u64 : U64) = 0xFFFFFFFF21524110#u64 := by native_decide
example : ~~~(0xCAFEBABE#u32 : U32) = 0x35014541#u32 := by native_decide
example : ~~~(170141183460469231731687303715884105727#i128 : I128) =
  (-170141183460469231731687303715884105728)#i128 := by native_decide
example : ~~~(0xFFFFFFFFFFFFFFFF#u128 : U128) =
  0xFFFFFFFFFFFFFFFF0000000000000000#u128 := by native_decide
example : ~~~(1000000000000000000#u64 : U64) = 17446744073709551615#u64 := by native_decide

end
