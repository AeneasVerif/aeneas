import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Linarith
import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Notations
import Aeneas.Std.Scalar.Elab
import Aeneas.Std.Scalar.Casts
import Aeneas.Std.Core.Result
import Aeneas.Std.Array.Array
import Aeneas.Tactic.Solver.ScalarTac
import Aeneas.Tactic.Step.Init
import Aeneas.Tactic.Solver.Arith.Lemmas
import Aeneas.Data.BitVec

namespace Aeneas

namespace Std

open Result Error ScalarElab WP

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

def FromUsizeU8.from (x : U8) : Usize := ⟨ x.bv.setWidth _ ⟩
def FromUsizeU16.from (x : U16) : Usize := ⟨ x.bv.setWidth _ ⟩
def FromUsizeU32.from (x : U32) : Usize := ⟨ x.bv.setWidth _ ⟩
def FromUsizeUsize.from (x : Usize) : Usize := ⟨ x.bv.setWidth _ ⟩

def FromU8U8.from (x : U8) : U8 := ⟨ x.bv.setWidth _ ⟩

def FromU16U8.from (x : U8) : U16 := ⟨ x.bv.setWidth _ ⟩
def FromU16U16.from (x : U16) : U16 := ⟨ x.bv.setWidth _ ⟩

def FromU32U8.from (x : U8) : U32 := ⟨ x.bv.setWidth _ ⟩
def FromU32U16.from (x : U16) : U32 := ⟨ x.bv.setWidth _ ⟩
def FromU32U32.from (x : U32) : U32 := ⟨ x.bv.setWidth _ ⟩

def FromU64U8.from (x : U8) : U64 := ⟨ x.bv.setWidth _ ⟩
def FromU64U16.from (x : U16) : U64 := ⟨ x.bv.setWidth _ ⟩
def FromU64U32.from (x : U32) : U64 := ⟨ x.bv.setWidth _ ⟩
def FromU64U64.from (x : U64) : U64 := ⟨ x.bv.setWidth _ ⟩

def FromU128U8.from (x : U8) : U128 := ⟨ x.bv.setWidth _ ⟩
def FromU128U16.from (x : U16) : U128 := ⟨ x.bv.setWidth _ ⟩
def FromU128U32.from (x : U32) : U128 := ⟨ x.bv.setWidth _ ⟩
def FromU128U64.from (x : U64) : U128 := ⟨ x.bv.setWidth _ ⟩
def FromU128U128.from (x : U128) : U128 := ⟨ x.bv.setWidth _ ⟩

def FromIsizeI8.from (x : I8) : Isize := ⟨ x.bv.signExtend _ ⟩
def FromIsizeI16.from (x : I16) : Isize := ⟨ x.bv.signExtend _ ⟩
def FromIsizeI32.from (x : I32) : Isize := ⟨ x.bv.signExtend _ ⟩
def FromIsizeIsize.from (x : Isize) : Isize := ⟨ x.bv.signExtend _ ⟩

def FromI8I8.from (x : I8) : I8 := ⟨ x.bv.signExtend _ ⟩

def FromI16I8.from (x : I8) : I16 := ⟨ x.bv.signExtend _ ⟩
def FromI16I16.from (x : I16) : I16 := ⟨ x.bv.signExtend _ ⟩

def FromI32I8.from (x : I8) : I32 := ⟨ x.bv.signExtend _ ⟩
def FromI32I16.from (x : I16) : I32 := ⟨ x.bv.signExtend _ ⟩
def FromI32I32.from (x : I32) : I32 := ⟨ x.bv.signExtend _ ⟩

def FromI64I8.from (x : I8) : I64 := ⟨ x.bv.signExtend _ ⟩
def FromI64I16.from (x : I16) : I64 := ⟨ x.bv.signExtend _ ⟩
def FromI64I32.from (x : I32) : I64 := ⟨ x.bv.signExtend _ ⟩
def FromI64I64.from (x : I64) : I64 := ⟨ x.bv.signExtend _ ⟩

def FromI128I8.from (x : I8) : I128 := ⟨ x.bv.signExtend _ ⟩
def FromI128I16.from (x : I16) : I128 := ⟨ x.bv.signExtend _ ⟩
def FromI128I32.from (x : I32) : I128 := ⟨ x.bv.signExtend _ ⟩
def FromI128I64.from (x : I64) : I128 := ⟨ x.bv.signExtend _ ⟩
def FromI128I128.from (x : I128) : I128 := ⟨ x.bv.signExtend _ ⟩

private theorem BitVec.setWidth_toNat_le (m : Nat) (x : BitVec n) (h : n ≤ m) :
  (x.setWidth m).toNat = x.toNat := by
  have : x.toNat < 2^n := by cases x; simp
  simp only [BitVec.toNat_setWidth]
  have : 2 ^ n ≤ 2 ^m := by apply Nat.pow_le_pow_right <;> omega
  apply Nat.mod_eq_of_lt
  omega

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromUsizeU8.from_val_eq (x : U8) : (FromUsizeU8.from x).val = x.val := by
  simp only [FromUsizeU8.from]; apply BitVec.setWidth_toNat_le
  cases System.Platform.numBits_eq <;> simp [*]

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromUsizeU16.from_val_eq (x : U16) : (FromUsizeU16.from x).val = x.val := by
  simp only [FromUsizeU16.from]; apply BitVec.setWidth_toNat_le
  cases System.Platform.numBits_eq <;> simp [*]

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromUsizeU32.from_val_eq (x : U32) : (FromUsizeU32.from x).val = x.val := by
  simp only [FromUsizeU32.from]; apply BitVec.setWidth_toNat_le
  cases System.Platform.numBits_eq <;> simp [*]

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromUsizeUsize.from_val_eq (x : Usize) : (FromUsizeUsize.from x).val = x.val := by
  simp only [FromUsizeUsize.from]; apply BitVec.setWidth_toNat_le
  cases System.Platform.numBits_eq <;> simp [*]

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU8U8.from_val_eq (x : U8) : (FromU8U8.from x).val = x.val := by
  simp only [FromU8U8.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU16U8.from_val_eq (x : U8) : (FromU16U8.from x).val = x.val := by
  simp only [FromU16U8.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU16U16.from_val_eq (x : U16) : (FromU16U16.from x).val = x.val := by
  simp only [FromU16U16.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU32U8.from_val_eq (x : U8) : (FromU32U8.from x).val = x.val := by
  simp only [FromU32U8.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU32U16.from_val_eq (x : U16) : (FromU32U16.from x).val = x.val := by
  simp only [FromU32U16.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU32U32.from_val_eq (x : U32) : (FromU32U32.from x).val = x.val := by
  simp only [FromU32U32.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU64U8.from_val_eq (x : U8) : (FromU64U8.from x).val = x.val := by
  simp only [FromU64U8.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU64U16.from_val_eq (x : U16) : (FromU64U16.from x).val = x.val := by
  simp only [FromU64U16.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU64U32.from_val_eq (x : U32) : (FromU64U32.from x).val = x.val := by
  simp only [FromU64U32.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU64U64.from_val_eq (x : U64) : (FromU64U64.from x).val = x.val := by
  simp only [FromU64U64.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU128U8.from_val_eq (x : U8) : (FromU128U8.from x).val = x.val := by
  simp only [FromU128U8.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU128U16.from_val_eq (x : U16) : (FromU128U16.from x).val = x.val := by
  simp only [FromU128U16.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU128U32.from_val_eq (x : U32) : (FromU128U32.from x).val = x.val := by
  simp only [FromU128U32.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU128U64.from_val_eq (x : U64) : (FromU128U64.from x).val = x.val := by
  simp only [FromU128U64.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromU128U128.from_val_eq (x : U128) : (FromU128U128.from x).val = x.val := by
  simp only [FromU128U128.from]; apply BitVec.setWidth_toNat_le; simp

@[simp, bvify, grind =, agrind =] theorem FromUsizeU8.from_bv_eq (x : U8) : (FromUsizeU8.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromUsizeU16.from_bv_eq (x : U16) : (FromUsizeU16.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromUsizeU32.from_bv_eq (x : U32) : (FromUsizeU32.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromUsizeUsize.from_bv_eq (x : Usize) : (FromUsizeUsize.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU8U8.from_bv_eq (x : U8) : (FromU8U8.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU16U8.from_bv_eq (x : U8) : (FromU16U8.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU16U16.from_bv_eq (x : U16) : (FromU16U16.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU32U8.from_bv_eq (x : U8) : (FromU32U8.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU32U16.from_bv_eq (x : U16) : (FromU32U16.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU32U32.from_bv_eq (x : U32) : (FromU32U32.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU64U8.from_bv_eq (x : U8) : (FromU64U8.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU64U16.from_bv_eq (x : U16) : (FromU64U16.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU64U32.from_bv_eq (x : U32) : (FromU64U32.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU64U64.from_bv_eq (x : U64) : (FromU64U64.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU128U8.from_bv_eq (x : U8) : (FromU128U8.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU128U16.from_bv_eq (x : U16) : (FromU128U16.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU128U32.from_bv_eq (x : U32) : (FromU128U32.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU128U64.from_bv_eq (x : U64) : (FromU128U64.from x).bv = x.bv.setWidth _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromU128U128.from_bv_eq (x : U128) : (FromU128U128.from x).bv = x.bv.setWidth _ := by rfl

@[local simp] private theorem zero_lt_size_num_bits : 0 < System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp [*]

private theorem bmod_pow2_eq_of_inBounds' (n : ℕ) (x : ℤ) (h : 0 < n ∧ -2 ^ (n - 1) ≤ x ∧ x < 2 ^ (n - 1)) :
  x.bmod (2 ^ n) = x := by
  have hn : n - 1 + 1 = n := by omega
  have := Arith.Int.bmod_pow2_eq_of_inBounds (n - 1) x (by omega) (by simp [*])
  simp [hn] at this
  apply this

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromIsizeI8.from_val_eq (x : I8) : (FromIsizeI8.from x).val = x.val := by
  cases System.Platform.numBits_eq <;>
  simp only [FromIsizeI8.from, IScalar.val, BitVec.signExtend] <;> simp <;>
  apply bmod_pow2_eq_of_inBounds' _ x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromIsizeI16.from_val_eq (x : I16) : (FromIsizeI16.from x).val = x.val := by
  cases System.Platform.numBits_eq <;>
  simp only [FromIsizeI16.from, IScalar.val, BitVec.signExtend] <;> simp <;>
  apply bmod_pow2_eq_of_inBounds' _ x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromIsizeI32.from_val_eq (x : I32) : (FromIsizeI32.from x).val = x.val := by
  cases System.Platform.numBits_eq <;>
  simp only [FromIsizeI32.from, IScalar.val, BitVec.signExtend] <;> simp <;>
  apply bmod_pow2_eq_of_inBounds' _ x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromIsizeIsize.from_val_eq (x : Isize) : (FromIsizeIsize.from x).val = x.val := by
  cases System.Platform.numBits_eq <;>
  simp only [FromIsizeIsize.from, IScalar.val, BitVec.signExtend] <;> simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI8I8.from_val_eq (x : I8) : (FromI8I8.from x).val = x.val := by
  simp only [FromI8I8.from, IScalar.val, BitVec.signExtend]; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI16I8.from_val_eq (x : I8) : (FromI16I8.from x).val = x.val := by
  simp only [FromI16I8.from, IScalar.val, BitVec.signExtend]; simp
  apply bmod_pow2_eq_of_inBounds' 16 x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI16I16.from_val_eq (x : I16) : (FromI16I16.from x).val = x.val := by
  simp only [FromI16I16.from, IScalar.val, BitVec.signExtend]; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI32I8.from_val_eq (x : I8) : (FromI32I8.from x).val = x.val := by
  simp only [FromI32I8.from, IScalar.val, BitVec.signExtend]; simp
  apply bmod_pow2_eq_of_inBounds' 32 x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI32I16.from_val_eq (x : I16) : (FromI32I16.from x).val = x.val := by
  simp only [FromI32I16.from, IScalar.val, BitVec.signExtend]; simp
  apply bmod_pow2_eq_of_inBounds' 32 x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI32I32.from_val_eq (x : I32) : (FromI32I32.from x).val = x.val := by
  simp only [FromI32I32.from, IScalar.val, BitVec.signExtend]; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI64I8.from_val_eq (x : I8) : (FromI64I8.from x).val = x.val := by
  simp only [FromI64I8.from, IScalar.val, BitVec.signExtend]; simp
  apply bmod_pow2_eq_of_inBounds' 64 x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI64I16.from_val_eq (x : I16) : (FromI64I16.from x).val = x.val := by
  simp only [FromI64I16.from, IScalar.val, BitVec.signExtend]; simp
  apply bmod_pow2_eq_of_inBounds' 64 x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI64I32.from_val_eq (x : I32) : (FromI64I32.from x).val = x.val := by
  simp only [FromI64I32.from, IScalar.val, BitVec.signExtend]; simp
  apply bmod_pow2_eq_of_inBounds' 64 x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI64I64.from_val_eq (x : I64) : (FromI64I64.from x).val = x.val := by
  simp only [FromI64I64.from, IScalar.val, BitVec.signExtend]; simp

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI128I8.from_val_eq (x : I8) : (FromI128I8.from x).val = x.val := by
  simp only [FromI128I8.from, IScalar.val, BitVec.signExtend]; simp
  apply bmod_pow2_eq_of_inBounds' 128 x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI128I16.from_val_eq (x : I16) : (FromI128I16.from x).val = x.val := by
  simp only [FromI128I16.from, IScalar.val, BitVec.signExtend]; simp
  apply bmod_pow2_eq_of_inBounds' 128 x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI128I32.from_val_eq (x : I32) : (FromI128I32.from x).val = x.val := by
  simp only [FromI128I32.from, IScalar.val, BitVec.signExtend]; simp
  apply bmod_pow2_eq_of_inBounds' 128 x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI128I64.from_val_eq (x : I64) : (FromI128I64.from x).val = x.val := by
  simp only [FromI128I64.from, IScalar.val, BitVec.signExtend]; simp
  apply bmod_pow2_eq_of_inBounds' 128 x.val (by scalar_tac)

@[simp, scalar_tac_simps, simp_scalar_safe, grind =, agrind =]
theorem FromI128I128.from_val_eq (x : I128) : (FromI128I128.from x).val = x.val := by
  simp only [FromI128I128.from, IScalar.val, BitVec.signExtend]; simp

@[simp, bvify, grind =, agrind =] theorem FromIsizeI8.from_bv_eq (x : I8) : (FromIsizeI8.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromIsizeI16.from_bv_eq (x : I16) : (FromIsizeI16.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromIsizeI32.from_bv_eq (x : I32) : (FromIsizeI32.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromIsizeIsize.from_bv_eq (x : Isize) : (FromIsizeIsize.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI8I8.from_bv_eq (x : I8) : (FromI8I8.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI16I8.from_bv_eq (x : I8) : (FromI16I8.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI16I16.from_bv_eq (x : I16) : (FromI16I16.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI32I8.from_bv_eq (x : I8) : (FromI32I8.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI32I16.from_bv_eq (x : I16) : (FromI32I16.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI32I32.from_bv_eq (x : I32) : (FromI32I32.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI64I8.from_bv_eq (x : I8) : (FromI64I8.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI64I16.from_bv_eq (x : I16) : (FromI64I16.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI64I32.from_bv_eq (x : I32) : (FromI64I32.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI64I64.from_bv_eq (x : I64) : (FromI64I64.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI128I8.from_bv_eq (x : I8) : (FromI128I8.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI128I16.from_bv_eq (x : I16) : (FromI128I16.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI128I32.from_bv_eq (x : I32) : (FromI128I32.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI128I64.from_bv_eq (x : I64) : (FromI128I64.from x).bv = x.bv.signExtend _ := by rfl

@[simp, bvify, grind =, agrind =] theorem FromI128I128.from_bv_eq (x : I128) : (FromI128I128.from x).bv = x.bv.signExtend _ := by rfl


end num -- core.convert.num

@[reducible]
def FromUsizeU8 : core.convert.From Usize U8 := {
  «from» := fun x => ok (num.FromUsizeU8.from x)
}

@[reducible]
def FromUsizeU16 : core.convert.From Usize U16 := {
  «from» := fun x => ok (num.FromUsizeU16.from x)
}

@[reducible]
def FromUsizeU32 : core.convert.From Usize U32 := {
  «from» := fun x => ok (num.FromUsizeU32.from x)
}

@[reducible]
def FromUsizeUsize : core.convert.From Usize Usize := {
  «from» := fun x => ok (num.FromUsizeUsize.from x)
}

@[reducible]
def FromU8U8 : core.convert.From U8 U8 := {
  «from» := fun x => ok (num.FromU8U8.from x)
}

@[reducible]
def FromU16U8 : core.convert.From U16 U8 := {
  «from» := fun x => ok (num.FromU16U8.from x)
}

@[reducible]
def FromU16U16 : core.convert.From U16 U16 := {
  «from» := fun x => ok (num.FromU16U16.from x)
}

@[reducible]
def FromU32U8 : core.convert.From U32 U8 := {
  «from» := fun x => ok (num.FromU32U8.from x)
}

@[reducible]
def FromU32U16 : core.convert.From U32 U16 := {
  «from» := fun x => ok (num.FromU32U16.from x)
}

@[reducible]
def FromU32U32 : core.convert.From U32 U32 := {
  «from» := fun x => ok (num.FromU32U32.from x)
}

@[reducible]
def FromU64U8 : core.convert.From U64 U8 := {
  «from» := fun x => ok (num.FromU64U8.from x)
}

@[reducible]
def FromU64U16 : core.convert.From U64 U16 := {
  «from» := fun x => ok (num.FromU64U16.from x)
}

@[reducible]
def FromU64U32 : core.convert.From U64 U32 := {
  «from» := fun x => ok (num.FromU64U32.from x)
}

@[reducible]
def FromU64U64 : core.convert.From U64 U64 := {
  «from» := fun x => ok (num.FromU64U64.from x)
}

@[reducible]
def FromU128U8 : core.convert.From U128 U8 := {
  «from» := fun x => ok (num.FromU128U8.from x)
}

@[reducible]
def FromU128U16 : core.convert.From U128 U16 := {
  «from» := fun x => ok (num.FromU128U16.from x)
}

@[reducible]
def FromU128U32 : core.convert.From U128 U32 := {
  «from» := fun x => ok (num.FromU128U32.from x)
}

@[reducible]
def FromU128U64 : core.convert.From U128 U64 := {
  «from» := fun x => ok (num.FromU128U64.from x)
}

@[reducible]
def FromU128U128 : core.convert.From U128 U128 := {
  «from» := fun x => ok (num.FromU128U128.from x)
}

@[reducible]
def FromIsizeI8 : core.convert.From Isize I8 := {
  «from» := fun x => ok (num.FromIsizeI8.from x)
}

@[reducible]
def FromIsizeI16 : core.convert.From Isize I16 := {
  «from» := fun x => ok (num.FromIsizeI16.from x)
}

@[reducible]
def FromIsizeI32 : core.convert.From Isize I32 := {
  «from» := fun x => ok (num.FromIsizeI32.from x)
}

@[reducible]
def FromIsizeIsize : core.convert.From Isize Isize := {
  «from» := fun x => ok (num.FromIsizeIsize.from x)
}

@[reducible]
def FromI8I8 : core.convert.From I8 I8 := {
  «from» := fun x => ok (num.FromI8I8.from x)
}

@[reducible]
def FromI16I8 : core.convert.From I16 I8 := {
  «from» := fun x => ok (num.FromI16I8.from x)
}

@[reducible]
def FromI16I16 : core.convert.From I16 I16 := {
  «from» := fun x => ok (num.FromI16I16.from x)
}

@[reducible]
def FromI32I8 : core.convert.From I32 I8 := {
  «from» := fun x => ok (num.FromI32I8.from x)
}

@[reducible]
def FromI32I16 : core.convert.From I32 I16 := {
  «from» := fun x => ok (num.FromI32I16.from x)
}

@[reducible]
def FromI32I32 : core.convert.From I32 I32 := {
  «from» := fun x => ok (num.FromI32I32.from x)
}

@[reducible]
def FromI64I8 : core.convert.From I64 I8 := {
  «from» := fun x => ok (num.FromI64I8.from x)
}

@[reducible]
def FromI64I16 : core.convert.From I64 I16 := {
  «from» := fun x => ok (num.FromI64I16.from x)
}

@[reducible]
def FromI64I32 : core.convert.From I64 I32 := {
  «from» := fun x => ok (num.FromI64I32.from x)
}

@[reducible]
def FromI64I64 : core.convert.From I64 I64 := {
  «from» := fun x => ok (num.FromI64I64.from x)
}

@[reducible]
def FromI128I8 : core.convert.From I128 I8 := {
  «from» := fun x => ok (num.FromI128I8.from x)
}

@[reducible]
def FromI128I16 : core.convert.From I128 I16 := {
  «from» := fun x => ok (num.FromI128I16.from x)
}

@[reducible]
def FromI128I32 : core.convert.From I128 I32 := {
  «from» := fun x => ok (num.FromI128I32.from x)
}

@[reducible]
def FromI128I64 : core.convert.From I128 I64 := {
  «from» := fun x => ok (num.FromI128I64.from x)
}

@[reducible]
def FromI128I128 : core.convert.From I128 I128 := {
  «from» := fun x => ok (num.FromI128I128.from x)
}

end core.convert

open ScalarElab

/-!
# To Little-Endian
-/
uscalar_no_usize def core.num.«%S».to_le_bytes (x : «%S») : Array U8 (%Size)#usize := ⟨ x.bv.toLEBytes.map UScalar.mk, by
  simp [BitVec.toLEBytes_length] ⟩
iscalar_no_isize def core.num.«%S».to_le_bytes (x : «%S») : Array I8 (%Size)#usize := ⟨ x.bv.toLEBytes.map IScalar.mk, by
  simp [BitVec.toLEBytes_length] ⟩

/-!
# To Big-Endian
-/
uscalar_no_usize def core.num.«%S».to_be_bytes (x : «%S») : Array U8 (%Size)#usize := ⟨ x.bv.toBEBytes.map UScalar.mk, by
  simp [BitVec.toBEBytes_length] ⟩
iscalar_no_isize def core.num.«%S».to_be_bytes (x : «%S») : Array I8 (%Size)#usize := ⟨ x.bv.toBEBytes.map IScalar.mk, by
  simp [BitVec.toBEBytes_length] ⟩

/-!
# From Little-Endian
-/
uscalar_no_usize def core.num.«%S».from_le_bytes (a : Array U8 (%Size)#usize) : «%S» :=
  ⟨ (BitVec.fromLEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

iscalar_no_isize def core.num.«%S».from_le_bytes (a : Array I8 (%Size)#usize) : «%S» :=
  ⟨ (BitVec.fromLEBytes (List.map I8.bv a.val)).cast (by simp) ⟩

/-!
# From Big-Endian
-/
uscalar_no_usize def core.num.«%S».from_be_bytes (a : Array U8 (%Size)#usize) : «%S» :=
  ⟨ (BitVec.fromBEBytes (List.map U8.bv a.val)).cast (by simp) ⟩

iscalar_no_isize def core.num.«%S».from_be_bytes (a : Array I8 (%Size)#usize) : «%S» :=
  ⟨ (BitVec.fromBEBytes (List.map I8.bv a.val)).cast (by simp) ⟩

/-!
# Progress theorems: To Little-Endian
-/
uscalar_no_usize @[step]
theorem core.num.«%S».to_le_bytes.step_spec (x : «%S») :
  lift (core.num.«%S».to_le_bytes x) ⦃ y => y.val = x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8) ⦄ := by
  simp only [spec_ok, lift, to_le_bytes, UScalarTy.U8_numBits_eq]

iscalar_no_isize @[step]
theorem core.num.«%S».to_le_bytes.step_spec (x : «%S») :
  lift (core.num.«%S».to_le_bytes x) ⦃ y => y.val = x.bv.toLEBytes.map (@IScalar.mk IScalarTy.I8) ⦄ := by
  simp only [spec_ok, lift, to_le_bytes, IScalarTy.I8_numBits_eq]

/-!
# Progress theorems: From Little-Endian
-/
uscalar_no_usize @[step]
theorem core.num.«%S».from_le_bytes.step_spec (x : Array U8 (%Size)#usize) :
  lift (core.num.«%S».from_le_bytes x) ⦃ y => y.bv = (BitVec.fromLEBytes (x.val.map U8.bv)).cast (by simp) ⦄ := by
  simp only [spec_ok, lift, from_le_bytes]

iscalar_no_isize @[step]
theorem core.num.«%S».from_le_bytes.step_spec (x : Array I8 (%Size)#usize) :
  lift (core.num.«%S».from_le_bytes x) ⦃ y => y.bv = (BitVec.fromLEBytes (x.val.map I8.bv)).cast (by simp) ⦄  := by
  simp only [spec_ok, lift, from_le_bytes]

/-!
# Progress theorems: To Big-Endian
-/
uscalar_no_usize @[step]
theorem core.num.«%S».to_be_bytes.step_spec (x : «%S») :
  lift (core.num.«%S».to_be_bytes x) ⦃ y => y.val = x.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8) ⦄ := by
  simp only [spec_ok, lift, to_be_bytes, UScalarTy.U8_numBits_eq]

iscalar_no_isize @[step]
theorem core.num.«%S».to_be_bytes.step_spec (x : «%S») :
  lift (core.num.«%S».to_be_bytes x) ⦃ y => y.val = x.bv.toBEBytes.map (@IScalar.mk IScalarTy.I8) ⦄ := by
  simp only [spec_ok, lift, to_be_bytes, IScalarTy.I8_numBits_eq]

/-!
# Progress theorems: From Big-Endian
-/
uscalar_no_usize @[step]
theorem core.num.«%S».from_be_bytes.step_spec (x : Array U8 (%Size)#usize) :
  lift (core.num.«%S».from_be_bytes x) ⦃ y => y.bv = (BitVec.fromBEBytes (x.val.map U8.bv)).cast (by simp) ⦄ := by
  simp only [spec_ok, lift, from_be_bytes]

iscalar_no_isize @[step]
theorem core.num.«%S».from_be_bytes.step_spec (x : Array I8 (%Size)#usize) :
  lift (core.num.«%S».from_be_bytes x) ⦃ y => y.bv = (BitVec.fromBEBytes (x.val.map I8.bv)).cast (by simp) ⦄  := by
  simp only [spec_ok, lift, from_be_bytes]

/-!
# `cast_signed` / `cast_unsigned`
-/

@[rust_fun "core::num::{u8}::cast_signed"]
def core.num.U8.cast_signed (x : U8) : Result I8 := ok ⟨x.bv⟩

@[rust_fun "core::num::{i8}::cast_unsigned"]
def core.num.I8.cast_unsigned (x : I8) : Result U8 := ok ⟨x.bv⟩

@[rust_fun "core::num::{u16}::cast_signed"]
def core.num.U16.cast_signed (x : U16) : Result I16 := ok ⟨x.bv⟩

@[rust_fun "core::num::{i16}::cast_unsigned"]
def core.num.I16.cast_unsigned (x : I16) : Result U16 := ok ⟨x.bv⟩

@[rust_fun "core::num::{u32}::cast_signed"]
def core.num.U32.cast_signed (x : U32) : Result I32 := ok ⟨x.bv⟩

@[rust_fun "core::num::{i32}::cast_unsigned"]
def core.num.I32.cast_unsigned (x : I32) : Result U32 := ok ⟨x.bv⟩

@[rust_fun "core::num::{u64}::cast_signed"]
def core.num.U64.cast_signed (x : U64) : Result I64 := ok ⟨x.bv⟩

@[rust_fun "core::num::{i64}::cast_unsigned"]
def core.num.I64.cast_unsigned (x : I64) : Result U64 := ok ⟨x.bv⟩

@[rust_fun "core::num::{u128}::cast_signed"]
def core.num.U128.cast_signed (x : U128) : Result I128 := ok ⟨x.bv⟩

@[rust_fun "core::num::{i128}::cast_unsigned"]
def core.num.I128.cast_unsigned (x : I128) : Result U128 := ok ⟨x.bv⟩

@[rust_fun "core::num::{usize}::cast_signed"]
def core.num.Usize.cast_signed (x : Usize) : Result Isize := ok ⟨x.bv⟩

@[rust_fun "core::num::{isize}::cast_unsigned"]
def core.num.Isize.cast_unsigned (x : Isize) : Result Usize := ok ⟨x.bv⟩

@[step]
theorem core.num.U8.cast_signed.step_spec (x : U8) :
    core.num.U8.cast_signed x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.U8.cast_signed]

@[step]
theorem core.num.I8.cast_unsigned.step_spec (x : I8) :
    core.num.I8.cast_unsigned x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.I8.cast_unsigned]

@[step]
theorem core.num.U16.cast_signed.step_spec (x : U16) :
    core.num.U16.cast_signed x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.U16.cast_signed]

@[step]
theorem core.num.I16.cast_unsigned.step_spec (x : I16) :
    core.num.I16.cast_unsigned x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.I16.cast_unsigned]

@[step]
theorem core.num.U32.cast_signed.step_spec (x : U32) :
    core.num.U32.cast_signed x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.U32.cast_signed]

@[step]
theorem core.num.I32.cast_unsigned.step_spec (x : I32) :
    core.num.I32.cast_unsigned x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.I32.cast_unsigned]

@[step]
theorem core.num.U64.cast_signed.step_spec (x : U64) :
    core.num.U64.cast_signed x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.U64.cast_signed]

@[step]
theorem core.num.I64.cast_unsigned.step_spec (x : I64) :
    core.num.I64.cast_unsigned x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.I64.cast_unsigned]

@[step]
theorem core.num.U128.cast_signed.step_spec (x : U128) :
    core.num.U128.cast_signed x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.U128.cast_signed]

@[step]
theorem core.num.I128.cast_unsigned.step_spec (x : I128) :
    core.num.I128.cast_unsigned x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.I128.cast_unsigned]

@[step]
theorem core.num.Usize.cast_signed.step_spec (x : Usize) :
    core.num.Usize.cast_signed x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.Usize.cast_signed]

@[step]
theorem core.num.Isize.cast_unsigned.step_spec (x : Isize) :
    core.num.Isize.cast_unsigned x ⦃ y => y.bv = x.bv ⦄ := by
  simp only [spec_ok, core.num.Isize.cast_unsigned]

/-! ## `{u8,u16,...}::is_multiple_of`

`n.is_multiple_of(m)` ≡ `n % m == 0`.
Note that with `Nat` we have: `x % 0 = x`, meaning `x % 0 = 0 ↔ x = 0`,
which matches Rust's definition of `is_multiple_of`. -/

def UScalar.is_multiple_of (n m : UScalar ty) : Result Bool :=
  ok (n.val % m.val == 0)

@[rust_fun "core::num::{u8}::is_multiple_of"]
def core.num.U8.is_multiple_of (n m : U8) : Result Bool := UScalar.is_multiple_of n m

@[rust_fun "core::num::{u16}::is_multiple_of"]
def core.num.U16.is_multiple_of (n m : U16) : Result Bool := UScalar.is_multiple_of n m

@[rust_fun "core::num::{u32}::is_multiple_of"]
def core.num.U32.is_multiple_of (n m : U32) : Result Bool := UScalar.is_multiple_of n m

@[rust_fun "core::num::{u64}::is_multiple_of"]
def core.num.U64.is_multiple_of (n m : U64) : Result Bool := UScalar.is_multiple_of n m

@[rust_fun "core::num::{u128}::is_multiple_of"]
def core.num.U128.is_multiple_of (n m : U128) : Result Bool := UScalar.is_multiple_of n m

@[rust_fun "core::num::{usize}::is_multiple_of"]
def core.num.Usize.is_multiple_of (n m : Usize) : Result Bool := UScalar.is_multiple_of n m

/-! ## `TryFrom` between integer types -/

theorem UScalar.is_multiple_of.spec (a b : UScalar ty) :
    UScalar.is_multiple_of a b
    ⦃ (r : Bool) => r = (a.val % b.val = 0) ⦄ := by
  simp [UScalar.is_multiple_of]

uscalar
@[step]
theorem core.num.«%S».is_multiple_of.spec (a b : «%S») :
    core.num.«%S».is_multiple_of a b
    ⦃ (r : Bool) => r = (a.val % b.val = 0) ⦄ := UScalar.is_multiple_of.spec a b

@[reducible, rust_type "core::num::error::TryFromIntError"]
def core.num.error.TryFromIntError : Type := Unit

/-- General fallible conversion between unsigned scalar types. -/
def core.num.tryFromUScalar {srcTy : UScalarTy} (tgtTy : UScalarTy) (i : UScalar srcTy) :
  Result (core.result.Result (UScalar tgtTy) core.num.error.TryFromIntError) :=
  if i.val ≤ UScalar.max tgtTy then
    ok (.Ok (UScalar.cast tgtTy i))
  else
    ok (.Err ())

-- TODO: define for all scalar pairs
@[rust_fun "core::convert::num::ptr_try_from_impls::{core::convert::TryFrom<u32, usize, core::num::error::TryFromIntError>}::try_from"]
def core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (i : Usize) :
  Result (core.result.Result U32 core.num.error.TryFromIntError) :=
  core.num.tryFromUScalar .U32 i

-- TODO: define for all scalar pairs
@[step]
theorem core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from.step_spec
    (i : Usize) :
    core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from i
    ⦃ (r : core.result.Result U32 core.num.error.TryFromIntError) =>
      (i.val ≤ U32.max →
         ∃ x : U32, r = .Ok x ∧ x.val = i.val) ∧
      (U32.max < i.val → r = .Err ()) ⦄ := by
  unfold core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
    core.num.tryFromUScalar
  split <;> rename_i hb <;> simp only [WP.spec_ok]
  · refine ⟨fun _ => ⟨_, rfl, ?_⟩, fun habsurd => by scalar_tac⟩
    have hcast :=
      (UScalar.cast_inBounds_spec (src_ty := .Usize) (tgt_ty := .U32) i
        (by scalar_tac))
    simp only [lift, WP.spec_ok] at hcast
    exact hcast
  · refine ⟨fun habsurd => by scalar_tac, fun _ => trivial⟩

end Std

end Aeneas
