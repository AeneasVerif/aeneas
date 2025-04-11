import Aeneas.Std.Scalar.Ops.Mul

namespace Aeneas.Std

open Result Error Arith

/-!
# Checked Multiplication: Definitions
-/

/- [core::num::{T}::checked_mul] -/
def core.num.checked_mul_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (UScalar.mul x y)

def U8.checked_mul (x y : U8) : Option U8 := core.num.checked_mul_UScalar x y
def U16.checked_mul (x y : U16) : Option U16 := core.num.checked_mul_UScalar x y
def U32.checked_mul (x y : U32) : Option U32 := core.num.checked_mul_UScalar x y
def U64.checked_mul (x y : U64) : Option U64 := core.num.checked_mul_UScalar x y
def U128.checked_mul (x y : U128) : Option U128 := core.num.checked_mul_UScalar x y
def Usize.checked_mul (x y : Usize) : Option Usize := core.num.checked_mul_UScalar x y

/- [core::num::{T}::checked_mul] -/
def core.num.checked_mul_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (IScalar.mul x y)

def I8.checked_mul (x y : I8) : Option I8 := core.num.checked_mul_IScalar x y
def I16.checked_mul (x y : I16) : Option I16 := core.num.checked_mul_IScalar x y
def I32.checked_mul (x y : I32) : Option I32 := core.num.checked_mul_IScalar x y
def I64.checked_mul (x y : I64) : Option I64 := core.num.checked_mul_IScalar x y
def I128.checked_mul (x y : I128) : Option I128 := core.num.checked_mul_IScalar x y
def Isize.checked_mul (x y : Isize) : Option Isize := core.num.checked_mul_IScalar x y

/-!
# Checked Mul: Theorems
-/

/-!
Unsigned checked mul
-/
theorem core.num.checked_mul_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_mul_UScalar x y with
  | some z => x.val * y.val ≤ UScalar.max ty ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => UScalar.max ty < x.val * y.val := by
  have h := UScalar.mul_equiv x y
  simp [checked_mul_UScalar]
  cases hEq : UScalar.mul x y <;> simp_all [Option.ofResult]

@[progress_pure checked_mul x y]
theorem U8.checked_mul_bv_spec (x y : U8) :
  match U8.checked_mul x y with
  | some z => x.val * y.val ≤ U8.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => U8.max < x.val * y.val := by
  have := core.num.checked_mul_UScalar_bv_spec x y
  simp_all only [U8.checked_mul, UScalar.max, U8.bv, min, max, numBits]
  cases h: core.num.checked_mul_UScalar x y <;> simp_all only [and_self]

@[progress_pure checked_mul x y]
theorem U16.checked_mul_bv_spec (x y : U16) :
  match U16.checked_mul x y with
  | some z => x.val * y.val ≤ U16.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => U16.max < x.val * y.val := by
  have := core.num.checked_mul_UScalar_bv_spec x y
  simp_all only [U16.checked_mul, UScalar.max, U16.bv, min, max, numBits]
  cases h: core.num.checked_mul_UScalar x y <;> simp_all only [and_self]

@[progress_pure checked_mul x y]
theorem U32.checked_mul_bv_spec (x y : U32) :
  match U32.checked_mul x y with
  | some z => x.val * y.val ≤ U32.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => U32.max < x.val * y.val := by
  have := core.num.checked_mul_UScalar_bv_spec x y
  simp_all only [U32.checked_mul, UScalar.max, U32.bv, min, max, numBits]
  cases h: core.num.checked_mul_UScalar x y <;> simp_all only [and_self]

@[progress_pure checked_mul x y]
theorem U64.checked_mul_bv_spec (x y : U64) :
  match U64.checked_mul x y with
  | some z => x.val * y.val ≤ U64.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => U64.max < x.val * y.val := by
  have := core.num.checked_mul_UScalar_bv_spec x y
  simp_all only [U64.checked_mul, UScalar.max, U64.bv, min, max, numBits]
  cases h: core.num.checked_mul_UScalar x y <;> simp_all only [and_self]

@[progress_pure checked_mul x y]
theorem U128.checked_mul_bv_spec (x y : U128) :
  match U128.checked_mul x y with
  | some z => x.val * y.val ≤ U128.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => U128.max < x.val * y.val := by
  have := core.num.checked_mul_UScalar_bv_spec x y
  simp_all only [U128.checked_mul, UScalar.max, U128.bv, min, max, numBits]
  cases h: core.num.checked_mul_UScalar x y <;> simp_all only [and_self]

@[progress_pure checked_mul x y]
theorem Usize.checked_mul_bv_spec (x y : Usize) :
  match Usize.checked_mul x y with
  | some z => x.val * y.val ≤ Usize.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => Usize.max < x.val * y.val := by
  have := core.num.checked_mul_UScalar_bv_spec x y
  simp_all only [Usize.checked_mul, UScalar.max, Usize.bv, min, max, numBits]
  cases h: core.num.checked_mul_UScalar x y <;> simp_all only [and_self]

/-!
Signed checked mul
-/
theorem core.num.checked_mul_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_mul_IScalar x y with
  | some z => IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => ¬ (IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty) := by
  have h := IScalar.mul_equiv x y
  simp [checked_mul_IScalar]
  cases hEq : IScalar.mul x y <;> simp_all [Option.ofResult]

@[progress_pure checked_mul x y]
theorem I8.checked_mul_bv_spec (x y : I8) :
  match core.num.checked_mul_IScalar x y with
  | some z => I8.min ≤ x.val * y.val ∧ x.val * y.val ≤ I8.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => ¬ (I8.min ≤ x.val * y.val ∧ x.val * y.val ≤ I8.max) := by
  have := core.num.checked_mul_IScalar_bv_spec x y
  simp_all only [I8.checked_mul, IScalar.min, IScalar.max, I8.bv, min, max, numBits]
  cases h: core.num.checked_mul_IScalar x y <;> simp_all only [not_false_eq_true, and_self]

@[progress_pure checked_mul x y]
theorem I16.checked_mul_bv_spec (x y : I16) :
  match core.num.checked_mul_IScalar x y with
  | some z => I16.min ≤ x.val * y.val ∧ x.val * y.val ≤ I16.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => ¬ (I16.min ≤ x.val * y.val ∧ x.val * y.val ≤ I16.max) := by
  have := core.num.checked_mul_IScalar_bv_spec x y
  simp_all only [I16.checked_mul, IScalar.min, IScalar.max, I16.bv, min, max, numBits]
  cases h: core.num.checked_mul_IScalar x y <;> simp_all only [not_false_eq_true, and_self]

@[progress_pure checked_mul x y]
theorem I32.checked_mul_bv_spec (x y : I32) :
  match core.num.checked_mul_IScalar x y with
  | some z => I32.min ≤ x.val * y.val ∧ x.val * y.val ≤ I32.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => ¬ (I32.min ≤ x.val * y.val ∧ x.val * y.val ≤ I32.max) := by
  have := core.num.checked_mul_IScalar_bv_spec x y
  simp_all only [I32.checked_mul, IScalar.min, IScalar.max, I32.bv, min, max, numBits]
  cases h: core.num.checked_mul_IScalar x y <;> simp_all only [not_false_eq_true, and_self]

@[progress_pure checked_mul x y]
theorem I64.checked_mul_bv_spec (x y : I64) :
  match core.num.checked_mul_IScalar x y with
  | some z => I64.min ≤ x.val * y.val ∧ x.val * y.val ≤ I64.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => ¬ (I64.min ≤ x.val * y.val ∧ x.val * y.val ≤ I64.max) := by
  have := core.num.checked_mul_IScalar_bv_spec x y
  simp_all only [I64.checked_mul, IScalar.min, IScalar.max, I64.bv, min, max, numBits]
  cases h: core.num.checked_mul_IScalar x y <;> simp_all only [not_false_eq_true, and_self]

@[progress_pure checked_mul x y]
theorem I128.checked_mul_bv_spec (x y : I128) :
  match core.num.checked_mul_IScalar x y with
  | some z => I128.min ≤ x.val * y.val ∧ x.val * y.val ≤ I128.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => ¬ (I128.min ≤ x.val * y.val ∧ x.val * y.val ≤ I128.max) := by
  have := core.num.checked_mul_IScalar_bv_spec x y
  simp_all only [I128.checked_mul, IScalar.min, IScalar.max, I128.bv, min, max, numBits]
  cases h: core.num.checked_mul_IScalar x y <;> simp_all only [not_false_eq_true, and_self]

@[progress_pure checked_mul x y]
theorem Isize.checked_mul_bv_spec (x y : Isize) :
  match core.num.checked_mul_IScalar x y with
  | some z => Isize.min ≤ x.val * y.val ∧ x.val * y.val ≤ Isize.max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => ¬ (Isize.min ≤ x.val * y.val ∧ x.val * y.val ≤ Isize.max) := by
  have := core.num.checked_mul_IScalar_bv_spec x y
  simp_all only [Isize.checked_mul, IScalar.min, IScalar.max, Isize.bv, min, max, numBits]
  cases h: core.num.checked_mul_IScalar x y <;> simp_all only [not_false_eq_true, and_self]

end Aeneas.Std
