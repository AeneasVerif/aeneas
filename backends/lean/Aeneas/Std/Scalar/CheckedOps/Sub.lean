import Aeneas.Std.Scalar.Ops.Sub

namespace Aeneas.Std

open Result Error Arith

/-!
# Checked Subtraction: Definitions
-/

/- [core::num::{T}::checked_sub] -/
def core.num.checked_sub_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (x - y)

def U8.checked_sub (x y : U8) : Option U8 := core.num.checked_sub_UScalar x y
def U16.checked_sub (x y : U16) : Option U16 := core.num.checked_sub_UScalar x y
def U32.checked_sub (x y : U32) : Option U32 := core.num.checked_sub_UScalar x y
def U64.checked_sub (x y : U64) : Option U64 := core.num.checked_sub_UScalar x y
def U128.checked_sub (x y : U128) : Option U128 := core.num.checked_sub_UScalar x y
def Usize.checked_sub (x y : Usize) : Option Usize := core.num.checked_sub_UScalar x y

/- [core::num::{T}::checked_sub] -/
def core.num.checked_sub_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (x - y)

def I8.checked_sub (x y : I8) : Option I8 := core.num.checked_sub_IScalar x y
def I16.checked_sub (x y : I16) : Option I16 := core.num.checked_sub_IScalar x y
def I32.checked_sub (x y : I32) : Option I32 := core.num.checked_sub_IScalar x y
def I64.checked_sub (x y : I64) : Option I64 := core.num.checked_sub_IScalar x y
def I128.checked_sub (x y : I128) : Option I128 := core.num.checked_sub_IScalar x y
def Isize.checked_sub (x y : Isize) : Option Isize := core.num.checked_sub_IScalar x y

/-!
# Checked Sub: Theorems
-/

/-!
Unsigned checked sub
-/
theorem core.num.checked_sub_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_sub_UScalar x y with
  | some z => y.val ≤ x.val ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => x.val < y.val := by
  have h := UScalar.sub_equiv x y
  have hsub : x - y = UScalar.sub x y := by rfl
  rw [hsub] at h
  dcases hEq : UScalar.sub x y <;> simp_all [Option.ofResult, checked_sub_UScalar]

@[progress_pure checked_sub x y]
theorem U8.checked_sub_bv_spec (x y : U8) :
  match U8.checked_sub x y with
  | some z => y.val ≤ x.val ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => x.val < y.val := by
  have := core.num.checked_sub_UScalar_bv_spec x y
  simp_all [U8.checked_sub, UScalar.max, U8.bv]
  cases h: core.num.checked_sub_UScalar x y <;> simp_all

@[progress_pure checked_sub x y]
theorem U16.checked_sub_bv_spec (x y : U16) :
  match U16.checked_sub x y with
  | some z => y.val ≤ x.val ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => x.val < y.val := by
  have := core.num.checked_sub_UScalar_bv_spec x y
  simp_all [U16.checked_sub, UScalar.max, U16.bv]
  cases h: core.num.checked_sub_UScalar x y <;> simp_all

@[progress_pure checked_sub x y]
theorem U32.checked_sub_bv_spec (x y : U32) :
  match U32.checked_sub x y with
  | some z => y.val ≤ x.val ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => x.val < y.val := by
  have := core.num.checked_sub_UScalar_bv_spec x y
  simp_all [U32.checked_sub, UScalar.max, U32.bv]
  cases h: core.num.checked_sub_UScalar x y <;> simp_all

@[progress_pure checked_sub x y]
theorem U64.checked_sub_bv_spec (x y : U64) :
  match U64.checked_sub x y with
  | some z => y.val ≤ x.val ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => x.val < y.val := by
  have := core.num.checked_sub_UScalar_bv_spec x y
  simp_all [U64.checked_sub, UScalar.max, U64.bv]
  cases h: core.num.checked_sub_UScalar x y <;> simp_all

@[progress_pure checked_sub x y]
theorem U128.checked_sub_bv_spec (x y : U128) :
  match U128.checked_sub x y with
  | some z => y.val ≤ x.val ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => x.val < y.val := by
  have := core.num.checked_sub_UScalar_bv_spec x y
  simp_all [U128.checked_sub, UScalar.max, U128.bv]
  cases h: core.num.checked_sub_UScalar x y <;> simp_all

theorem Usize.checked_sub_bv_spec (x y : Usize) :
  match Usize.checked_sub x y with
  | some z => y.val ≤ x.val ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => x.val < y.val := by
  have := core.num.checked_sub_UScalar_bv_spec x y
  simp_all [Usize.checked_sub, UScalar.max, Usize.bv]
  cases h: core.num.checked_sub_UScalar x y <;> simp_all

/-!
Signed checked sub
-/
theorem core.num.checked_sub_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_sub_IScalar x y with
  | some z => IScalar.min ty ≤ x.val - y.val ∧ x.val - y.val ≤ IScalar.max ty ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => ¬ (IScalar.min ty ≤ x.val - y.val ∧ x.val - y.val ≤ IScalar.max ty) := by
  have h := IScalar.sub_equiv x y
  have hsub : x - y = IScalar.sub x y := by rfl
  rw [hsub] at h
  dcases hEq : IScalar.sub x y <;> simp_all [Option.ofResult, checked_sub_IScalar, IScalar.min, IScalar.max] <;>
  (have : 0 < 2^ty.numBits := by simp) <;>
  omega

@[progress_pure checked_sub x y]
theorem I8.checked_sub_bv_spec (x y : I8) :
  match core.num.checked_sub_IScalar x y with
  | some z => I8.min ≤ x.val - y.val ∧ x.val - y.val ≤ I8.max ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => ¬ (I8.min ≤ x.val - y.val ∧ x.val - y.val ≤ I8.max) := by
  have := core.num.checked_sub_IScalar_bv_spec x y
  simp_all only [I8.checked_sub, IScalar.min, IScalar.max, I8.bv, min, max, numBits]
  cases h: core.num.checked_sub_IScalar x y <;> simp_all only <;> simp

@[progress_pure checked_sub x y]
theorem I16.checked_sub_bv_spec (x y : I16) :
  match core.num.checked_sub_IScalar x y with
  | some z => I16.min ≤ x.val - y.val ∧ x.val - y.val ≤ I16.max ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => ¬ (I16.min ≤ x.val - y.val ∧ x.val - y.val ≤ I16.max) := by
  have := core.num.checked_sub_IScalar_bv_spec x y
  simp_all only [I16.checked_sub, IScalar.min, IScalar.max, I16.bv, min, max, numBits]
  cases h: core.num.checked_sub_IScalar x y <;> simp_all only <;> simp

@[progress_pure checked_sub x y]
theorem I32.checked_sub_bv_spec (x y : I32) :
  match core.num.checked_sub_IScalar x y with
  | some z => I32.min ≤ x.val - y.val ∧ x.val - y.val ≤ I32.max ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => ¬ (I32.min ≤ x.val - y.val ∧ x.val - y.val ≤ I32.max) := by
  have := core.num.checked_sub_IScalar_bv_spec x y
  simp_all only [I32.checked_sub, IScalar.min, IScalar.max, I32.bv, min, max, numBits]
  cases h: core.num.checked_sub_IScalar x y <;> simp_all only <;> simp

@[progress_pure checked_sub x y]
theorem I64.checked_sub_bv_spec (x y : I64) :
  match core.num.checked_sub_IScalar x y with
  | some z => I64.min ≤ x.val - y.val ∧ x.val - y.val ≤ I64.max ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => ¬ (I64.min ≤ x.val - y.val ∧ x.val - y.val ≤ I64.max) := by
  have := core.num.checked_sub_IScalar_bv_spec x y
  simp_all only [I64.checked_sub, IScalar.min, IScalar.max, I64.bv, min, max, numBits]
  cases h: core.num.checked_sub_IScalar x y <;> simp_all only <;> simp

@[progress_pure checked_sub x y]
theorem I128.checked_sub_bv_spec (x y : I128) :
  match core.num.checked_sub_IScalar x y with
  | some z => I128.min ≤ x.val - y.val ∧ x.val - y.val ≤ I128.max ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => ¬ (I128.min ≤ x.val - y.val ∧ x.val - y.val ≤ I128.max) := by
  have := core.num.checked_sub_IScalar_bv_spec x y
  simp_all only [I128.checked_sub, IScalar.min, IScalar.max, I128.bv, min, max, numBits]
  cases h: core.num.checked_sub_IScalar x y <;> simp_all only <;> simp

@[progress_pure checked_sub x y]
theorem Isize.checked_sub_bv_spec (x y : Isize) :
  match core.num.checked_sub_IScalar x y with
  | some z => Isize.min ≤ x.val - y.val ∧ x.val - y.val ≤ Isize.max ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => ¬ (Isize.min ≤ x.val - y.val ∧ x.val - y.val ≤ Isize.max) := by
  have := core.num.checked_sub_IScalar_bv_spec x y
  simp_all only [Isize.checked_sub, IScalar.min, IScalar.max, Isize.bv, min, max, numBits]
  cases h: core.num.checked_sub_IScalar x y <;> simp_all only <;> simp

end Aeneas.Std
