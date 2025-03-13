import Aeneas.Std.Scalar.Ops.Div

namespace Aeneas.Std

open Result Error Arith

/-!
# Checked Division: Definitions
-/

/- [core::num::{T}::checked_div] -/
def core.num.checked_div_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (UScalar.div x y)

def U8.checked_div (x y : U8) : Option U8 := core.num.checked_div_UScalar x y
def U16.checked_div (x y : U16) : Option U16 := core.num.checked_div_UScalar x y
def U32.checked_div (x y : U32) : Option U32 := core.num.checked_div_UScalar x y
def U64.checked_div (x y : U64) : Option U64 := core.num.checked_div_UScalar x y
def U128.checked_div (x y : U128) : Option U128 := core.num.checked_div_UScalar x y
def Usize.checked_div (x y : Usize) : Option Usize := core.num.checked_div_UScalar x y

/- [core::num::{T}::checked_div] -/
def core.num.checked_div_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (IScalar.div x y)

def I8.checked_div (x y : I8) : Option I8 := core.num.checked_div_IScalar x y
def I16.checked_div (x y : I16) : Option I16 := core.num.checked_div_IScalar x y
def I32.checked_div (x y : I32) : Option I32 := core.num.checked_div_IScalar x y
def I64.checked_div (x y : I64) : Option I64 := core.num.checked_div_IScalar x y
def I128.checked_div (x y : I128) : Option I128 := core.num.checked_div_IScalar x y
def Isize.checked_div (x y : Isize) : Option Isize := core.num.checked_div_IScalar x y

/-!
# Checked Division: Theorems
-/

/-!
Unsigned checked div
-/
theorem core.num.checked_div_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_div_UScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  simp [checked_div_UScalar, Option.ofResult, UScalar.div]
  split_ifs
  . zify at *
    simp_all
  . rename_i hnz
    simp
    have hnz' : y.val ≠ 0 := by zify at *; simp_all
    have ⟨ z, hz ⟩ := UScalar.div_bv_spec x hnz'
    have : x / y = x.div y := by rfl
    simp [this, UScalar.div, hnz] at hz
    simp [hz, hnz']

@[progress_pure checked_div x y]
theorem U8.checked_div_bv_spec (x y : U8) :
  match U8.checked_div x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  have := core.num.checked_div_UScalar_bv_spec x y
  simp_all [U8.checked_div, UScalar.max, U8.bv]
  cases h: core.num.checked_div_UScalar x y <;> simp_all

@[progress_pure checked_div x y]
theorem U16.checked_div_bv_spec (x y : U16) :
  match U16.checked_div x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  have := core.num.checked_div_UScalar_bv_spec x y
  simp_all [U16.checked_div, UScalar.max, U16.bv]
  cases h: core.num.checked_div_UScalar x y <;> simp_all

@[progress_pure checked_div x y]
theorem U32.checked_div_bv_spec (x y : U32) :
  match U32.checked_div x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  have := core.num.checked_div_UScalar_bv_spec x y
  simp_all [U32.checked_div, UScalar.max, U32.bv]
  cases h: core.num.checked_div_UScalar x y <;> simp_all

@[progress_pure checked_div x y]
theorem U64.checked_div_bv_spec (x y : U64) :
  match U64.checked_div x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  have := core.num.checked_div_UScalar_bv_spec x y
  simp_all [U64.checked_div, UScalar.max, U64.bv]
  cases h: core.num.checked_div_UScalar x y <;> simp_all

@[progress_pure checked_div x y]
theorem U128.checked_div_bv_spec (x y : U128) :
  match U128.checked_div x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  have := core.num.checked_div_UScalar_bv_spec x y
  simp_all [U128.checked_div, UScalar.max, U128.bv]
  cases h: core.num.checked_div_UScalar x y <;> simp_all

@[progress_pure checked_div x y]
theorem Usize.checked_div_bv_spec (x y : Usize) :
  match Usize.checked_div x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  have := core.num.checked_div_UScalar_bv_spec x y
  simp_all [Usize.checked_div, UScalar.max, Usize.bv]
  cases h: core.num.checked_div_UScalar x y <;> simp_all

/-!
Signed checked div
-/
theorem core.num.checked_div_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = IScalar.min ty ∧ y.val = -1) ∧ z.val = Int.tdiv x.val y.val ∧ z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = IScalar.min ty ∧ y.val = -1) := by
  simp [checked_div_IScalar, Option.ofResult, IScalar.div]
  split_ifs
  . zify at *
    simp_all
  . rename_i hnz hNoOverflow
    simp
    have hnz' : y.val ≠ 0 := by zify at *; simp_all
    have ⟨ z, hz ⟩ := @IScalar.div_bv_spec _ x y hnz' (by simp; tauto)
    have : x / y = x.div y := by rfl
    simp [this, IScalar.div, hnz, hNoOverflow] at hz
    split_ifs at hz
    simp at hz
    simp [hz, hnz']
    tauto
  . simp_all

@[progress_pure checked_div x y]
theorem I8.checked_div_bv_spec (x y : I8) :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = I8.min ∧ y.val = -1) ∧ z.val = Int.tdiv x.val y.val ∧ z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = I8.min ∧ y.val = -1) := by
  have := core.num.checked_div_IScalar_bv_spec x y
  simp_all only [I8.checked_div, I8.bv, IScalar.min, min, max, numBits]
  cases h: core.num.checked_div_IScalar x y <;> simp_all only [ne_eq, not_false_eq_true, and_self, this]

@[progress_pure checked_div x y]
theorem I16.checked_div_bv_spec (x y : I16) :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = I16.min ∧ y.val = -1) ∧ z.val = Int.tdiv x.val y.val ∧ z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = I16.min ∧ y.val = -1) := by
  have := core.num.checked_div_IScalar_bv_spec x y
  simp_all only [I16.checked_div, I16.bv, IScalar.min, min, max, numBits]
  cases h: core.num.checked_div_IScalar x y <;> simp_all only [ne_eq, not_false_eq_true, and_self, this]

@[progress_pure checked_div x y]
theorem I32.checked_div_bv_spec (x y : I32) :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = I32.min ∧ y.val = -1) ∧ z.val = Int.tdiv x.val y.val ∧ z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = I32.min ∧ y.val = -1) := by
  have := core.num.checked_div_IScalar_bv_spec x y
  simp_all only [I32.checked_div, I32.bv, IScalar.min, min, max, numBits]
  cases h: core.num.checked_div_IScalar x y <;> simp_all only [ne_eq, not_false_eq_true, and_self, this]

@[progress_pure checked_div x y]
theorem I64.checked_div_bv_spec (x y : I64) :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = I64.min ∧ y.val = -1) ∧ z.val = Int.tdiv x.val y.val ∧ z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = I64.min ∧ y.val = -1) := by
  have := core.num.checked_div_IScalar_bv_spec x y
  simp_all only [I64.checked_div, I64.bv, IScalar.min, min, max, numBits]
  cases h: core.num.checked_div_IScalar x y <;> simp_all only [ne_eq, not_false_eq_true, and_self, this]

@[progress_pure checked_div x y]
theorem I128.checked_div_bv_spec (x y : I128) :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = I128.min ∧ y.val = -1) ∧ z.val = Int.tdiv x.val y.val ∧ z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = I128.min ∧ y.val = -1) := by
  have := core.num.checked_div_IScalar_bv_spec x y
  simp_all only [I128.checked_div, I128.bv, IScalar.min, min, max, numBits]
  cases h: core.num.checked_div_IScalar x y <;> simp_all only [ne_eq, not_false_eq_true, and_self, this]

@[progress_pure checked_div x y]
theorem Isize.checked_div_bv_spec (x y : Isize) :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = Isize.min ∧ y.val = -1) ∧ z.val = Int.tdiv x.val y.val ∧ z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = Isize.min ∧ y.val = -1) := by
  have := core.num.checked_div_IScalar_bv_spec x y
  simp_all only [Isize.checked_div, Isize.bv, IScalar.min, min, max, numBits]
  cases h: core.num.checked_div_IScalar x y <;> simp_all only [ne_eq, not_false_eq_true, and_self, this]

end Aeneas.Std
