import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Linarith
import Aeneas.Std.Scalar
import Aeneas.Std.ScalarNotations
import Aeneas.Std.ArraySlice
import Aeneas.ScalarTac
import Aeneas.Progress.Core
import Aeneas.Arith.Lemmas

namespace Aeneas

namespace Std

open Result Error

namespace core.convert

namespace num -- core.convert.num

-- Conversions
def FromUsizeBool.from (b : Bool) : Usize :=
  if b then 1#usize else 0#usize

def FromU8Bool.from (b : Bool) : U8 :=
  if b then 1#u8 else 0#u8

def FromU16Bool.from (b : Bool) : U16 :=
  if b then 1#u16 else 0#u16

def FromU32Bool.from (b : Bool) : U32 :=
  if b then 1#u32 else 0#u32

def FromU64Bool.from (b : Bool) : U64 :=
  if b then 1#u64 else 0#u64

def FromU128Bool.from (b : Bool) : U128 :=
  if b then 1#u128 else 0#u128

def FromIsizeBool.from (b : Bool) : Isize :=
  if b then 1#isize else 0#isize

def FromI8Bool.from (b : Bool) : I8 :=
  if b then 1#i8 else 0#i8

def FromI16Bool.from (b : Bool) : I16 :=
  if b then 1#i16 else 0#i16

def FromI32Bool.from (b : Bool) : I32 :=
  if b then 1#i32 else 0#i32

def FromI64Bool.from (b : Bool) : I64 :=
  if b then 1#i64 else 0#i64

def FromI128Bool.from (b : Bool) : I128 :=
  if b then 1#i128 else 0#i128

def FromUsizeU8.from (x : U8) : Usize := ⟨ x.val ⟩
def FromUsizeU16.from (x : U16) : Usize := ⟨ x.val ⟩
def FromUsizeU32.from (x : U32) : Usize := ⟨ x.val ⟩
def FromUsizeUsize.from (x : Usize) : Usize := ⟨ x.val ⟩

def FromU8U8.from (x : U8) : U8 := ⟨ x.val ⟩

def FromU16U8.from (x : U8) : U16 := ⟨ x.val ⟩
def FromU16U16.from (x : U16) : U16 := ⟨ x.val ⟩

def FromU32U8.from (x : U8) : U32 := ⟨ x.val ⟩
def FromU32U16.from (x : U16) : U32 := ⟨ x.val ⟩
def FromU32U32.from (x : U32) : U32 := ⟨ x.val ⟩

def FromU64U8.from (x : U8) : U64 := ⟨ x.val ⟩
def FromU64U16.from (x : U16) : U64 := ⟨ x.val ⟩
def FromU64U32.from (x : U32) : U64 := ⟨ x.val ⟩
def FromU64U64.from (x : U64) : U64 := ⟨ x.val ⟩

def FromU128U8.from (x : U8) : U128 := ⟨ x.val ⟩
def FromU128U16.from (x : U16) : U128 := ⟨ x.val ⟩
def FromU128U32.from (x : U32) : U128 := ⟨ x.val ⟩
def FromU128U64.from (x : U64) : U128 := ⟨ x.val ⟩
def FromU128U128.from (x : U128) : U128 := ⟨ x.val ⟩

def FromIsizeI8.from (x : I8) : Isize := ⟨ x.val ⟩
def FromIsizeI16.from (x : I16) : Isize := ⟨ x.val ⟩
def FromIsizeI32.from (x : I32) : Isize := ⟨ x.val ⟩
def FromIsizeIsize.from (x : Isize) : Isize := ⟨ x.val ⟩

def FromI8I8.from (x : I8) : I8 := ⟨ x.val ⟩

def FromI16I8.from (x : I8) : I16 := ⟨ x.val ⟩
def FromI16I16.from (x : I16) : I16 := ⟨ x.val ⟩

def FromI32I8.from (x : I8) : I32 := ⟨ x.val ⟩
def FromI32I16.from (x : I16) : I32 := ⟨ x.val ⟩
def FromI32I32.from (x : I32) : I32 := ⟨ x.val ⟩

def FromI64I8.from (x : I8) : I64 := ⟨ x.val ⟩
def FromI64I16.from (x : I16) : I64 := ⟨ x.val ⟩
def FromI64I32.from (x : I32) : I64 := ⟨ x.val ⟩
def FromI64I64.from (x : I64) : I64 := ⟨ x.val ⟩

def FromI128I8.from (x : I8) : I128 := ⟨ x.val ⟩
def FromI128I16.from (x : I16) : I128 := ⟨ x.val ⟩
def FromI128I32.from (x : I32) : I128 := ⟨ x.val ⟩
def FromI128I64.from (x : I64) : I128 := ⟨ x.val ⟩
def FromI128I128.from (x : I128) : I128 := ⟨ x.val ⟩

@[simp] def FromUsizeU8.from_val_eq (x : U8) : (FromUsizeU8.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromUsizeU16.from_val_eq (x : U16) : (FromUsizeU16.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromUsizeU32.from_val_eq (x : U32) : (FromUsizeU32.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromUsizeUsize.from_val_eq (x : Usize) : (FromUsizeUsize.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU8U8.from_val_eq (x : U8) : (FromU8U8.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU16U8.from_val_eq (x : U8) : (FromU16U8.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU16U16.from_val_eq (x : U16) : (FromU16U16.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU32U8.from_val_eq (x : U8) : (FromU32U8.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU32U16.from_val_eq (x : U16) : (FromU32U16.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU32U32.from_val_eq (x : U32) : (FromU32U32.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU64U8.from_val_eq (x : U8) : (FromU64U8.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU64U16.from_val_eq (x : U16) : (FromU64U16.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU64U32.from_val_eq (x : U32) : (FromU64U32.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU64U64.from_val_eq (x : U64) : (FromU64U64.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU128U8.from_val_eq (x : U8) : (FromU128U8.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU128U16.from_val_eq (x : U16) : (FromU128U16.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU128U32.from_val_eq (x : U32) : (FromU128U32.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU128U64.from_val_eq (x : U64) : (FromU128U64.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[simp] def FromU128U128.from_val_eq (x : U128) : (FromU128U128.from x).val = x.val := by
  simp only [UScalar.val]; simp; apply Nat.mod_eq_of_lt; scalar_tac

@[local simp] private theorem zero_lt_size_num_bits : 0 < System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp [*]

private theorem bmod_pow2_eq_of_inBounds' (n : ℕ) (x : ℤ) (h : 0 < n) (h0 : -2 ^ (n - 1) ≤ x) (h1 : x < 2 ^ (n - 1)) :
  x.bmod (2 ^ n) = x := by
  have hn : n - 1 + 1 = n := by omega
  have := Arith.Int.bmod_pow2_eq_of_inBounds (n - 1) x (by omega) (by assumption)
  simp [hn] at this
  apply this

@[simp] def FromIsizeI8.from_val_eq (x : I8) : (FromIsizeI8.from x).val = x.val := by
  simp only [FromIsizeI8.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromIsizeI16.from_val_eq (x : I16) : (FromIsizeI16.from x).val = x.val := by
  simp only [FromIsizeI16.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromIsizeI32.from_val_eq (x : I32) : (FromIsizeI32.from x).val = x.val := by
  simp only [FromIsizeI32.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromIsizeIsize.from_val_eq (x : Isize) : (FromIsizeIsize.from x).val = x.val := by
  simp only [FromIsizeIsize.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromI8I8.from_val_eq (x : I8) : (FromI8I8.from x).val = x.val := by
  simp only [FromI8I8.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromI16I8.from_val_eq (x : I8) : (FromI16I8.from x).val = x.val := by
  simp only [FromI16I8.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromI16I16.from_val_eq (x : I16) : (FromI16I16.from x).val = x.val := by
  simp only [FromI16I16.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromI32I8.from_val_eq (x : I8) : (FromI32I8.from x).val = x.val := by
  simp only [FromI32I8.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromI32I16.from_val_eq (x : I16) : (FromI32I16.from x).val = x.val := by
  simp only [FromI32I16.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromI32I32.from_val_eq (x : I32) : (FromI32I32.from x).val = x.val := by
  simp only [FromI32I32.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromI64I8.from_val_eq (x : I8) : (FromI64I8.from x).val = x.val := by
  simp only [FromI64I8.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> simp <;> scalar_tac

@[simp] def FromI64I16.from_val_eq (x : I16) : (FromI64I16.from x).val = x.val := by
  simp only [FromI64I16.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> simp <;> scalar_tac

@[simp] def FromI64I32.from_val_eq (x : I32) : (FromI64I32.from x).val = x.val := by
  simp only [FromI64I32.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> simp <;> scalar_tac

@[simp] def FromI64I64.from_val_eq (x : I64) : (FromI64I64.from x).val = x.val := by
  simp only [FromI64I64.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

@[simp] def FromI128I8.from_val_eq (x : I8) : (FromI128I8.from x).val = x.val := by
  simp only [FromI128I8.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> simp <;> scalar_tac

@[simp] def FromI128I16.from_val_eq (x : I16) : (FromI128I16.from x).val = x.val := by
  simp only [FromI128I16.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> simp <;> scalar_tac

@[simp] def FromI128I32.from_val_eq (x : I32) : (FromI128I32.from x).val = x.val := by
  simp only [FromI128I32.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> simp <;> scalar_tac

@[simp] def FromI128I64.from_val_eq (x : I64) : (FromI128I64.from x).val = x.val := by
  simp only [FromI128I64.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> simp <;> scalar_tac

@[simp] def FromI128I128.from_val_eq (x : I128) : (FromI128I128.from x).val = x.val := by
  simp only [FromI128I128.from, IScalar.val]
  simp [-IScalar.bv_toInt_eq, Int.cast, IntCast.intCast, -Nat.reducePow]
  apply bmod_pow2_eq_of_inBounds' <;> (try simp) <;> scalar_tac

end num -- core.convert.num

@[reducible]
def FromUsizeU8 : core.convert.From Usize U8 := {
  from_ := fun x => ok (num.FromUsizeU8.from x)
}

@[reducible]
def FromUsizeU16 : core.convert.From Usize U16 := {
  from_ := fun x => ok (num.FromUsizeU16.from x)
}

@[reducible]
def FromUsizeU32 : core.convert.From Usize U32 := {
  from_ := fun x => ok (num.FromUsizeU32.from x)
}

@[reducible]
def FromUsizeUsize : core.convert.From Usize Usize := {
  from_ := fun x => ok (num.FromUsizeUsize.from x)
}

@[reducible]
def FromU8U8 : core.convert.From U8 U8 := {
  from_ := fun x => ok (num.FromU8U8.from x)
}

@[reducible]
def FromU16U8 : core.convert.From U16 U8 := {
  from_ := fun x => ok (num.FromU16U8.from x)
}

@[reducible]
def FromU16U16 : core.convert.From U16 U16 := {
  from_ := fun x => ok (num.FromU16U16.from x)
}

@[reducible]
def FromU32U8 : core.convert.From U32 U8 := {
  from_ := fun x => ok (num.FromU32U8.from x)
}

@[reducible]
def FromU32U16 : core.convert.From U32 U16 := {
  from_ := fun x => ok (num.FromU32U16.from x)
}

@[reducible]
def FromU32U32 : core.convert.From U32 U32 := {
  from_ := fun x => ok (num.FromU32U32.from x)
}

@[reducible]
def FromU64U8 : core.convert.From U64 U8 := {
  from_ := fun x => ok (num.FromU64U8.from x)
}

@[reducible]
def FromU64U16 : core.convert.From U64 U16 := {
  from_ := fun x => ok (num.FromU64U16.from x)
}

@[reducible]
def FromU64U32 : core.convert.From U64 U32 := {
  from_ := fun x => ok (num.FromU64U32.from x)
}

@[reducible]
def FromU64U64 : core.convert.From U64 U64 := {
  from_ := fun x => ok (num.FromU64U64.from x)
}

@[reducible]
def FromU128U8 : core.convert.From U128 U8 := {
  from_ := fun x => ok (num.FromU128U8.from x)
}

@[reducible]
def FromU128U16 : core.convert.From U128 U16 := {
  from_ := fun x => ok (num.FromU128U16.from x)
}

@[reducible]
def FromU128U32 : core.convert.From U128 U32 := {
  from_ := fun x => ok (num.FromU128U32.from x)
}

@[reducible]
def FromU128U64 : core.convert.From U128 U64 := {
  from_ := fun x => ok (num.FromU128U64.from x)
}

@[reducible]
def FromU128U128 : core.convert.From U128 U128 := {
  from_ := fun x => ok (num.FromU128U128.from x)
}

@[reducible]
def FromIsizeI8 : core.convert.From Isize I8 := {
  from_ := fun x => ok (num.FromIsizeI8.from x)
}

@[reducible]
def FromIsizeI16 : core.convert.From Isize I16 := {
  from_ := fun x => ok (num.FromIsizeI16.from x)
}

@[reducible]
def FromIsizeI32 : core.convert.From Isize I32 := {
  from_ := fun x => ok (num.FromIsizeI32.from x)
}

@[reducible]
def FromIsizeIsize : core.convert.From Isize Isize := {
  from_ := fun x => ok (num.FromIsizeIsize.from x)
}

@[reducible]
def FromI8I8 : core.convert.From I8 I8 := {
  from_ := fun x => ok (num.FromI8I8.from x)
}

@[reducible]
def FromI16I8 : core.convert.From I16 I8 := {
  from_ := fun x => ok (num.FromI16I8.from x)
}

@[reducible]
def FromI16I16 : core.convert.From I16 I16 := {
  from_ := fun x => ok (num.FromI16I16.from x)
}

@[reducible]
def FromI32I8 : core.convert.From I32 I8 := {
  from_ := fun x => ok (num.FromI32I8.from x)
}

@[reducible]
def FromI32I16 : core.convert.From I32 I16 := {
  from_ := fun x => ok (num.FromI32I16.from x)
}

@[reducible]
def FromI32I32 : core.convert.From I32 I32 := {
  from_ := fun x => ok (num.FromI32I32.from x)
}

@[reducible]
def FromI64I8 : core.convert.From I64 I8 := {
  from_ := fun x => ok (num.FromI64I8.from x)
}

@[reducible]
def FromI64I16 : core.convert.From I64 I16 := {
  from_ := fun x => ok (num.FromI64I16.from x)
}

@[reducible]
def FromI64I32 : core.convert.From I64 I32 := {
  from_ := fun x => ok (num.FromI64I32.from x)
}

@[reducible]
def FromI64I64 : core.convert.From I64 I64 := {
  from_ := fun x => ok (num.FromI64I64.from x)
}

@[reducible]
def FromI128I8 : core.convert.From I128 I8 := {
  from_ := fun x => ok (num.FromI128I8.from x)
}

@[reducible]
def FromI128I16 : core.convert.From I128 I16 := {
  from_ := fun x => ok (num.FromI128I16.from x)
}

@[reducible]
def FromI128I32 : core.convert.From I128 I32 := {
  from_ := fun x => ok (num.FromI128I32.from x)
}

@[reducible]
def FromI128I64 : core.convert.From I128 I64 := {
  from_ := fun x => ok (num.FromI128I64.from x)
}

@[reducible]
def FromI128I128 : core.convert.From I128 I128 := {
  from_ := fun x => ok (num.FromI128I128.from x)
}

end core.convert

-- to_le_bytes
def core.num.U8.to_le_bytes (x : U8) : Array U8 1#usize := ⟨ [x], by simp ⟩
def core.num.U16.to_le_bytes (x : U16) : Array U8 2#usize := sorry
def core.num.U32.to_le_bytes (x : U32) : Array U8 4#usize := sorry
def core.num.U64.to_le_bytes (x : U64) : Array U8 8#usize := sorry
def core.num.U128.to_le_bytes (x : U128) : Array U8 128#usize := sorry

-- to_be_bytes
def core.num.U8.to_be_bytes (x : U8) : Array U8 1#usize := ⟨ [x], by simp ⟩
def core.num.U16.to_be_bytes (x : U16) : Array U8 2#usize := sorry
def core.num.U32.to_be_bytes (x : U32) : Array U8 4#usize := sorry
def core.num.U64.to_be_bytes (x : U64) : Array U8 8#usize := sorry
def core.num.U128.to_be_bytes (x : U128) : Array U8 128#usize := sorry

-- from_le_bytes
def core.num.U8.from_le_bytes (a : Array U8 1#usize) : U8 := a.val[0]
def core.num.U16.from_le_bytes (a : Array U8 2#usize) : U16 := sorry
def core.num.U32.from_le_bytes (a : Array U8 4#usize) : U32 := sorry
def core.num.U64.from_le_bytes (a : Array U8 8#usize) : U64 := sorry
def core.num.U128.from_le_bytes (a : Array U8 128#usize) : U128 := sorry

-- from_be_bytes
def core.num.U8.from_be_bytes (a : Array U8 1#usize) : U8 := a.val[0]
def core.num.U16.from_be_bytes (a : Array U8 2#usize) : U16 := sorry
def core.num.U32.from_be_bytes (a : Array U8 4#usize) : U32 := sorry
def core.num.U64.from_be_bytes (a : Array U8 8#usize) : U64 := sorry
def core.num.U128.from_be_bytes (a : Array U8 128#usize) : U128 := sorry

end Std

end Aeneas
