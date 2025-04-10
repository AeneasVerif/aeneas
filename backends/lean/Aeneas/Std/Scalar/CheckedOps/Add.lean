import Aeneas.Std.Scalar.Ops.Add

namespace Aeneas.Std

open Result Error Arith

/-!
# Checked Addition: Definitions
-/

/- [core::num::{T}::checked_add] -/
def core.num.checked_add_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (x + y)

def U8.checked_add (x y : U8) : Option U8 := core.num.checked_add_UScalar x y
def U16.checked_add (x y : U16) : Option U16 := core.num.checked_add_UScalar x y
def U32.checked_add (x y : U32) : Option U32 := core.num.checked_add_UScalar x y
def U64.checked_add (x y : U64) : Option U64 := core.num.checked_add_UScalar x y
def U128.checked_add (x y : U128) : Option U128 := core.num.checked_add_UScalar x y
def Usize.checked_add (x y : Usize) : Option Usize := core.num.checked_add_UScalar x y

/- [core::num::{T}::checked_add] -/
def core.num.checked_add_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (x + y)

def I8.checked_add (x y : I8) : Option I8 := core.num.checked_add_IScalar x y
def I16.checked_add (x y : I16) : Option I16 := core.num.checked_add_IScalar x y
def I32.checked_add (x y : I32) : Option I32 := core.num.checked_add_IScalar x y
def I64.checked_add (x y : I64) : Option I64 := core.num.checked_add_IScalar x y
def I128.checked_add (x y : I128) : Option I128 := core.num.checked_add_IScalar x y
def Isize.checked_add (x y : Isize) : Option Isize := core.num.checked_add_IScalar x y

/-!
# Checked Add: Theorems
-/

/-!
Unsigned checked add
-/
theorem core.num.checked_add_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_add_UScalar x y with
  | some z => x.val + y.val ≤ UScalar.max ty ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => UScalar.max ty < x.val + y.val := by
  have h := UScalar.add_equiv x y
  have hAdd : x + y = UScalar.add x y := by rfl
  rw [hAdd] at h
  cases hEq : UScalar.add x y <;> simp_all [Option.ofResult, checked_add_UScalar, UScalar.max] <;>
  (have : 0 < 2^ty.numBits := by simp) <;>
  omega

@[progress_pure checked_add x y]
theorem U8.checked_add_bv_spec (x y : U8) :
  match U8.checked_add x y with
  | some z => x.val + y.val ≤ U8.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => U8.max < x.val + y.val := by
  have := core.num.checked_add_UScalar_bv_spec x y
  simp_all [U8.checked_add, UScalar.max, U8.bv]
  cases h: core.num.checked_add_UScalar x y <;> simp_all [max, numBits]

@[progress_pure checked_add x y]
theorem U16.checked_add_bv_spec (x y : U16) :
  match U16.checked_add x y with
  | some z => x.val + y.val ≤ U16.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => U16.max < x.val + y.val := by
  have := core.num.checked_add_UScalar_bv_spec x y
  simp_all [U16.checked_add, UScalar.max, U16.bv]
  cases h: core.num.checked_add_UScalar x y <;> simp_all [max, numBits]

@[progress_pure checked_add x y]
theorem U32.checked_add_bv_spec (x y : U32) :
  match U32.checked_add x y with
  | some z => x.val + y.val ≤ U32.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => U32.max < x.val + y.val := by
  have := core.num.checked_add_UScalar_bv_spec x y
  simp_all [U32.checked_add, UScalar.max, U32.bv]
  cases h: core.num.checked_add_UScalar x y <;> simp_all [max, numBits]

@[progress_pure checked_add x y]
theorem U64.checked_add_bv_spec (x y : U64) :
  match U64.checked_add x y with
  | some z => x.val + y.val ≤ U64.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => U64.max < x.val + y.val := by
  have := core.num.checked_add_UScalar_bv_spec x y
  simp_all [U64.checked_add, UScalar.max, U64.bv]
  cases h: core.num.checked_add_UScalar x y <;> simp_all [max, numBits]

@[progress_pure checked_add x y]
theorem U128.checked_add_bv_spec (x y : U128) :
  match U128.checked_add x y with
  | some z => x.val + y.val ≤ U128.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => U128.max < x.val + y.val := by
  have := core.num.checked_add_UScalar_bv_spec x y
  simp_all [U128.checked_add, UScalar.max, U128.bv]
  cases h: core.num.checked_add_UScalar x y <;> simp_all [max, numBits]

@[progress_pure checked_add x y]
theorem Usize.checked_add_bv_spec (x y : Usize) :
  match Usize.checked_add x y with
  | some z => x.val + y.val ≤ Usize.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => Usize.max < x.val + y.val := by
  have := core.num.checked_add_UScalar_bv_spec x y
  simp_all [Usize.checked_add, UScalar.max, Usize.bv]
  cases h: core.num.checked_add_UScalar x y <;> simp_all [max, numBits]

/-!
Signed checked add
-/
theorem core.num.checked_add_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_add_IScalar x y with
  | some z => IScalar.min ty ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ty ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => ¬ (IScalar.min ty ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ty) := by
  have h := IScalar.add_equiv x y
  have hAdd : x + y = IScalar.add x y := by rfl
  rw [hAdd] at h
  cases hEq : IScalar.add x y <;> simp_all [Option.ofResult, checked_add_IScalar, IScalar.min, IScalar.max] <;>
  omega

@[progress_pure checked_add x y]
theorem I8.checked_add_bv_spec (x y : I8) :
  match core.num.checked_add_IScalar x y with
  | some z => I8.min ≤ x.val + y.val ∧ x.val + y.val ≤ I8.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => ¬ (I8.min ≤ x.val + y.val ∧ x.val + y.val ≤ I8.max) := by
  have := core.num.checked_add_IScalar_bv_spec x y
  simp_all only [I8.checked_add, IScalar.min, IScalar.max, I8.bv, min, max, numBits]
  cases h: core.num.checked_add_IScalar x y <;> simp_all only [numBits] <;> simp

@[progress_pure checked_add x y]
theorem I16.checked_add_bv_spec (x y : I16) :
  match core.num.checked_add_IScalar x y with
  | some z => I16.min ≤ x.val + y.val ∧ x.val + y.val ≤ I16.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => ¬ (I16.min ≤ x.val + y.val ∧ x.val + y.val ≤ I16.max) := by
  have := core.num.checked_add_IScalar_bv_spec x y
  simp_all only [I16.checked_add, IScalar.min, IScalar.max, I16.bv, min, max, numBits]
  cases h: core.num.checked_add_IScalar x y <;> simp_all only [numBits] <;> simp

@[progress_pure checked_add x y]
theorem I32.checked_add_bv_spec (x y : I32) :
  match core.num.checked_add_IScalar x y with
  | some z => I32.min ≤ x.val + y.val ∧ x.val + y.val ≤ I32.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => ¬ (I32.min ≤ x.val + y.val ∧ x.val + y.val ≤ I32.max) := by
  have := core.num.checked_add_IScalar_bv_spec x y
  simp_all only [I32.checked_add, IScalar.min, IScalar.max, I32.bv, min, max, numBits]
  cases h: core.num.checked_add_IScalar x y <;> simp_all only [numBits] <;> simp

@[progress_pure checked_add x y]
theorem I64.checked_add_bv_spec (x y : I64) :
  match core.num.checked_add_IScalar x y with
  | some z => I64.min ≤ x.val + y.val ∧ x.val + y.val ≤ I64.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => ¬ (I64.min ≤ x.val + y.val ∧ x.val + y.val ≤ I64.max) := by
  have := core.num.checked_add_IScalar_bv_spec x y
  simp_all only [I64.checked_add, IScalar.min, IScalar.max, I64.bv, min, max, numBits]
  cases h: core.num.checked_add_IScalar x y <;> simp_all only [numBits] <;> simp

@[progress_pure checked_add x y]
theorem I128.checked_add_bv_spec (x y : I128) :
  match core.num.checked_add_IScalar x y with
  | some z => I128.min ≤ x.val + y.val ∧ x.val + y.val ≤ I128.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => ¬ (I128.min ≤ x.val + y.val ∧ x.val + y.val ≤ I128.max) := by
  have := core.num.checked_add_IScalar_bv_spec x y
  simp_all only [I128.checked_add, IScalar.min, IScalar.max, I128.bv, min, max, numBits]
  cases h: core.num.checked_add_IScalar x y <;> simp_all only [numBits] <;> simp

@[progress_pure checked_add x y]
theorem Isize.checked_add_bv_spec (x y : Isize) :
  match core.num.checked_add_IScalar x y with
  | some z => Isize.min ≤ x.val + y.val ∧ x.val + y.val ≤ Isize.max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => ¬ (Isize.min ≤ x.val + y.val ∧ x.val + y.val ≤ Isize.max) := by
  have := core.num.checked_add_IScalar_bv_spec x y
  simp_all only [Isize.checked_add, IScalar.min, IScalar.max, Isize.bv, min, max, numBits]
  cases h: core.num.checked_add_IScalar x y <;> simp_all only [numBits] <;> simp

end Aeneas.Std
