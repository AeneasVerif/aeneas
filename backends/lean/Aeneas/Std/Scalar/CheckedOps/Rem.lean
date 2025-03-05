import Aeneas.Std.Scalar.Ops.Rem

namespace Aeneas.Std

open Result Error Arith

/-!
# Checked Remainder: Definitions
-/

/- [core::num::{T}::checked_rem] -/
def core.num.checked_rem_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (UScalar.rem x y)

def U8.checked_rem (x y : U8) : Option U8 := core.num.checked_rem_UScalar x y
def U16.checked_rem (x y : U16) : Option U16 := core.num.checked_rem_UScalar x y
def U32.checked_rem (x y : U32) : Option U32 := core.num.checked_rem_UScalar x y
def U64.checked_rem (x y : U64) : Option U64 := core.num.checked_rem_UScalar x y
def U128.checked_rem (x y : U128) : Option U128 := core.num.checked_rem_UScalar x y
def Usize.checked_rem (x y : Usize) : Option Usize := core.num.checked_rem_UScalar x y

/- [core::num::{T}::checked_rem] -/
def core.num.checked_rem_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (IScalar.rem x y)

def I8.checked_rem (x y : I8) : Option I8 := core.num.checked_rem_IScalar x y
def I16.checked_rem (x y : I16) : Option I16 := core.num.checked_rem_IScalar x y
def I32.checked_rem (x y : I32) : Option I32 := core.num.checked_rem_IScalar x y
def I64.checked_rem (x y : I64) : Option I64 := core.num.checked_rem_IScalar x y
def I128.checked_rem (x y : I128) : Option I128 := core.num.checked_rem_IScalar x y
def Isize.checked_rem (x y : Isize) : Option Isize := core.num.checked_rem_IScalar x y

/-!
# Checked Remained
-/

/-!
Unsigned checked remainder
-/
theorem core.num.checked_rem_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_rem_UScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  simp [checked_rem_UScalar, Option.ofResult, UScalar.rem]
  split_ifs
  . zify at *
    simp_all
  . rename_i hnz
    simp
    have hnz' : y.val ≠ 0 := by zify at *; simp_all
    have ⟨ z, hz ⟩ := UScalar.rem_bv_spec x hnz'
    have : x % y = x.rem y := by rfl
    simp [this, UScalar.rem, hnz] at hz
    simp [hz, hnz']

@[progress_pure checked_rem x y]
theorem U8.checked_rem_bv_spec (x y : U8) :
  match U8.checked_rem x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_UScalar_bv_spec x y
  simp_all [U8.checked_rem, UScalar.max, U8.bv]
  cases h: core.num.checked_rem_UScalar x y <;> simp_all

@[progress_pure checked_rem x y]
theorem U16.checked_rem_bv_spec (x y : U16) :
  match U16.checked_rem x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_UScalar_bv_spec x y
  simp_all [U16.checked_rem, UScalar.max, U16.bv]
  cases h: core.num.checked_rem_UScalar x y <;> simp_all

@[progress_pure checked_rem x y]
theorem U32.checked_rem_bv_spec (x y : U32) :
  match U32.checked_rem x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_UScalar_bv_spec x y
  simp_all [U32.checked_rem, UScalar.max, U32.bv]
  cases h: core.num.checked_rem_UScalar x y <;> simp_all

@[progress_pure checked_rem x y]
theorem U64.checked_rem_bv_spec (x y : U64) :
  match U64.checked_rem x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_UScalar_bv_spec x y
  simp_all [U64.checked_rem, UScalar.max, U64.bv]
  cases h: core.num.checked_rem_UScalar x y <;> simp_all

@[progress_pure checked_rem x y]
theorem U128.checked_rem_bv_spec (x y : U128) :
  match U128.checked_rem x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_UScalar_bv_spec x y
  simp_all [U128.checked_rem, UScalar.max, U128.bv]
  cases h: core.num.checked_rem_UScalar x y <;> simp_all

@[progress_pure checked_rem x y]
theorem Usize.checked_rem_bv_spec (x y : Usize) :
  match Usize.checked_rem x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_UScalar_bv_spec x y
  simp_all [Usize.checked_rem, UScalar.max, Usize.bv]
  cases h: core.num.checked_rem_UScalar x y <;> simp_all

/-!
Signed checked rem
-/
theorem core.num.checked_rem_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = Int.tmod x.val y.val ∧ z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 := by
  simp [checked_rem_IScalar, Option.ofResult, IScalar.rem]
  split_ifs
  . zify at *
    simp_all
  . rename_i hnz
    simp
    have hnz' : y.val ≠ 0 := by zify at *; simp_all
    have ⟨ z, hz ⟩ := @IScalar.rem_bv_spec _ x y hnz'
    have : x % y = x.rem y := by rfl
    simp [this, IScalar.rem, hnz] at hz
    simp [*]

@[progress_pure checked_rem x y]
theorem I8.checked_rem_bv_spec (x y : I8) :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = Int.tmod x.val y.val ∧ z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_IScalar_bv_spec x y
  simp_all only [I8.checked_rem, I8.bv, IScalar.min]
  cases h: core.num.checked_rem_IScalar x y <;> simp_all

@[progress_pure checked_rem x y]
theorem I16.checked_rem_bv_spec (x y : I16) :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = Int.tmod x.val y.val ∧ z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_IScalar_bv_spec x y
  simp_all only [I16.checked_rem, I16.bv, IScalar.min]
  cases h: core.num.checked_rem_IScalar x y <;> simp_all

@[progress_pure checked_rem x y]
theorem I32.checked_rem_bv_spec (x y : I32) :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = Int.tmod x.val y.val ∧ z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_IScalar_bv_spec x y
  simp_all only [I32.checked_rem, I32.bv, IScalar.min]
  cases h: core.num.checked_rem_IScalar x y <;> simp_all

@[progress_pure checked_rem x y]
theorem I64.checked_rem_bv_spec (x y : I64) :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = Int.tmod x.val y.val ∧ z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_IScalar_bv_spec x y
  simp_all only [I64.checked_rem, I64.bv, IScalar.min]
  cases h: core.num.checked_rem_IScalar x y <;> simp_all

@[progress_pure checked_rem x y]
theorem I128.checked_rem_bv_spec (x y : I128) :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = Int.tmod x.val y.val ∧ z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_IScalar_bv_spec x y
  simp_all only [I128.checked_rem, I128.bv, IScalar.min]
  cases h: core.num.checked_rem_IScalar x y <;> simp_all

@[progress_pure checked_rem x y]
theorem Isize.checked_rem_bv_spec (x y : Isize) :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = Int.tmod x.val y.val ∧ z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_IScalar_bv_spec x y
  simp_all only [Isize.checked_rem, Isize.bv, IScalar.min]
  cases h: core.num.checked_rem_IScalar x y <;> simp_all

end Aeneas.Std
