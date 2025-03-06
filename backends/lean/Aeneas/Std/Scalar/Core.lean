import Lean
import Lean.Meta.Tactic.Simp
import Aeneas.Std.Core
import Aeneas.Std.Core
import Aeneas.Diverge.Core
import Aeneas.Progress.Core
import Aeneas.ScalarTac.ScalarTac
import Aeneas.Bvify.Init

namespace Aeneas

namespace Std

-- Deactivate the warnings which appear when we use `#assert`
set_option linter.hashCommand false

/-!
# Machine Integers

Because they tend to behave quite differently, we have two classes of machine integers: one for
signed integers, and another for unsigned integers. Inside of each class, we factor out definitions.
-/

open Result Error
open System.Platform.getNumBits

/-- Kinds of unsigned integers -/
inductive UScalarTy where
| Usize
| U8
| U16
| U32
| U64
| U128

/-- Kinds of signed integers -/
inductive IScalarTy where
| Isize
| I8
| I16
| I32
| I64
| I128

def UScalarTy.numBits (ty : UScalarTy) : Nat :=
  match ty with
  | Usize => System.Platform.numBits
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  | U128 => 128

def IScalarTy.numBits (ty : IScalarTy) : Nat :=
  match ty with
  | Isize => System.Platform.numBits
  | I8 => 8
  | I16 => 16
  | I32 => 32
  | I64 => 64
  | I128 => 128

/-- Signed integer -/
structure UScalar (ty : UScalarTy) where
  /- The internal representation is a bit-vector -/
  bv : BitVec ty.numBits
deriving Repr, BEq, DecidableEq

def UScalar.val {ty} (x : UScalar ty) : ℕ := x.bv.toNat

/-- Unsigned integer -/
structure IScalar (ty : IScalarTy) where
  /- The internal representation is a bit-vector -/
  bv : BitVec ty.numBits
deriving Repr, BEq, DecidableEq

def IScalar.val {ty} (x : IScalar ty) : ℤ := x.bv.toInt

/-!
# Bounds, Size

**Remark:** we mark most constants as irreducible because otherwise it leads to issues
when using tactics like `assumption`: it often happens that unification attempts to reduce
complex expressions (for instance by trying to reduce an expression like `2^128`, which
is extremely expensive).
-/

irreducible_def UScalar.max (ty : UScalarTy) : Nat := 2^ty.numBits-1
irreducible_def IScalar.min (ty : IScalarTy) : Int := -2^(ty.numBits - 1)
irreducible_def IScalar.max (ty : IScalarTy) : Int := 2^(ty.numBits - 1)-1

irreducible_def UScalar.size (ty : UScalarTy) : Nat := 2^ty.numBits
irreducible_def IScalar.size (ty : IScalarTy) : Int := 2^ty.numBits

/-! ## Num Bits -/
irreducible_def U8.numBits    : Nat := UScalarTy.U8.numBits
irreducible_def U16.numBits   : Nat := UScalarTy.U16.numBits
irreducible_def U32.numBits   : Nat := UScalarTy.U32.numBits
irreducible_def U64.numBits   : Nat := UScalarTy.U64.numBits
irreducible_def U128.numBits  : Nat := UScalarTy.U128.numBits
irreducible_def Usize.numBits : Nat := UScalarTy.Usize.numBits

irreducible_def I8.numBits    : Nat := IScalarTy.I8.numBits
irreducible_def I16.numBits   : Nat := IScalarTy.I16.numBits
irreducible_def I32.numBits   : Nat := IScalarTy.I32.numBits
irreducible_def I64.numBits   : Nat := IScalarTy.I64.numBits
irreducible_def I128.numBits  : Nat := IScalarTy.I128.numBits
irreducible_def Isize.numBits : Nat := IScalarTy.Isize.numBits

/-! ## Bounds -/
irreducible_def U8.max    : Nat := 2^U8.numBits - 1
irreducible_def U16.max   : Nat := 2^U16.numBits - 1
irreducible_def U32.max   : Nat := 2^U32.numBits - 1
irreducible_def U64.max   : Nat := 2^U64.numBits - 1
irreducible_def U128.max  : Nat := 2^U128.numBits - 1
irreducible_def Usize.max : Nat := 2^Usize.numBits - 1

irreducible_def I8.min    : Int := -2^(I8.numBits - 1)
irreducible_def I8.max    : Int := 2^(I8.numBits - 1) - 1
irreducible_def I16.min   : Int := -2^(I16.numBits - 1)
irreducible_def I16.max   : Int := 2^(I16.numBits - 1) - 1
irreducible_def I32.min   : Int := -2^(I32.numBits - 1)
irreducible_def I32.max   : Int := 2^(I32.numBits - 1) - 1
irreducible_def I64.min   : Int := -2^(I64.numBits - 1)
irreducible_def I64.max   : Int := 2^(I64.numBits - 1) - 1
irreducible_def I128.min  : Int := -2^(I128.numBits - 1)
irreducible_def I128.max  : Int := 2^(I128.numBits - 1) - 1
irreducible_def Isize.min : Int := -2^(Isize.numBits - 1)
irreducible_def Isize.max : Int := 2^(Isize.numBits - 1) - 1

/-! ## Size -/
irreducible_def U8.size    : Nat := 2^U8.numBits
irreducible_def U16.size   : Nat := 2^U16.numBits
irreducible_def U32.size   : Nat := 2^U32.numBits
irreducible_def U64.size   : Nat := 2^U64.numBits
irreducible_def U128.size  : Nat := 2^U128.numBits
irreducible_def Usize.size : Nat := 2^Usize.numBits

irreducible_def I8.size    : Nat := 2^I8.numBits
irreducible_def I16.size   : Nat := 2^I16.numBits
irreducible_def I32.size   : Nat := 2^I32.numBits
irreducible_def I64.size   : Nat := 2^I64.numBits
irreducible_def I128.size  : Nat := 2^I128.numBits
irreducible_def Isize.size : Nat := 2^Isize.numBits

/-! ## "Reduced" Constants -/
/-! ### Size -/
def I8.rSize   : Int := 256
def I16.rSize  : Int := 65536
def I32.rSize  : Int := 4294967296
def I64.rSize  : Int := 18446744073709551616
def I128.rSize : Int := 340282366920938463463374607431768211456

def U8.rSize   : Nat := 256
def U16.rSize  : Nat := 65536
def U32.rSize  : Nat := 4294967296
def U64.rSize  : Nat := 18446744073709551616
def U128.rSize : Nat := 340282366920938463463374607431768211456

/-! ### Bounds -/
def U8.rMax   : Nat := 255
def U16.rMax  : Nat := 65535
def U32.rMax  : Nat := 4294967295
def U64.rMax  : Nat := 18446744073709551615
def U128.rMax : Nat := 340282366920938463463374607431768211455
def Usize.rMax : Nat := 2^System.Platform.numBits-1

def I8.rMin   : Int := -128
def I8.rMax   : Int := 127
def I16.rMin  : Int := -32768
def I16.rMax  : Int := 32767
def I32.rMin  : Int := -2147483648
def I32.rMax  : Int := 2147483647
def I64.rMin  : Int := -9223372036854775808
def I64.rMax  : Int := 9223372036854775807
def I128.rMin : Int := -170141183460469231731687303715884105728
def I128.rMax : Int := 170141183460469231731687303715884105727
def Isize.rMin : Int := -2^(System.Platform.numBits - 1)
def Isize.rMax : Int := 2^(System.Platform.numBits - 1)-1

def UScalar.rMax (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => Usize.rMax
  | .U8    => U8.rMax
  | .U16   => U16.rMax
  | .U32   => U32.rMax
  | .U64   => U64.rMax
  | .U128  => U128.rMax

def IScalar.rMin (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => Isize.rMin
  | .I8    => I8.rMin
  | .I16   => I16.rMin
  | .I32   => I32.rMin
  | .I64   => I64.rMin
  | .I128  => I128.rMin

def IScalar.rMax (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => Isize.rMax
  | .I8    => I8.rMax
  | .I16   => I16.rMax
  | .I32   => I32.rMax
  | .I64   => I64.rMax
  | .I128  => I128.rMax

/-! # Theorems -/
theorem UScalarTy.numBits_nonzero (ty : UScalarTy) : ty.numBits ≠ 0 := by
  dcases ty <;> simp [numBits]
  dcases System.Platform.numBits_eq <;> simp_all

theorem IScalarTy.numBits_nonzero (ty : IScalarTy) : ty.numBits ≠ 0 := by
  dcases ty <;> simp [numBits]
  dcases System.Platform.numBits_eq <;> simp_all

@[simp, scalar_tac_simp, bvify_simps] theorem UScalarTy.U8_numBits_eq    : UScalarTy.U8.numBits    = 8 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem UScalarTy.U16_numBits_eq   : UScalarTy.U16.numBits   = 16 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem UScalarTy.U32_numBits_eq   : UScalarTy.U32.numBits   = 32 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem UScalarTy.U64_numBits_eq   : UScalarTy.U64.numBits   = 64 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem UScalarTy.U128_numBits_eq  : UScalarTy.U128.numBits  = 128 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem UScalarTy.Usize_numBits_eq : UScalarTy.Usize.numBits = System.Platform.numBits := by rfl

@[simp, scalar_tac_simp, bvify_simps] theorem IScalarTy.I8_numBits_eq    : IScalarTy.I8.numBits    = 8 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem IScalarTy.I16_numBits_eq   : IScalarTy.I16.numBits   = 16 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem IScalarTy.I32_numBits_eq   : IScalarTy.I32.numBits   = 32 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem IScalarTy.I64_numBits_eq   : IScalarTy.I64.numBits   = 64 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem IScalarTy.I128_numBits_eq  : IScalarTy.I128.numBits  = 128 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem IScalarTy.Isize_numBits_eq : IScalarTy.Isize.numBits = System.Platform.numBits := by rfl

@[simp] theorem UScalar.max_UScalarTy_U8_eq    : UScalar.max .U8 = U8.max := by simp [UScalar.max, U8.max, U8.numBits]
@[simp] theorem UScalar.max_UScalarTy_U16_eq   : UScalar.max .U16 = U16.max := by simp [UScalar.max, U16.max, U16.numBits]
@[simp] theorem UScalar.max_UScalarTy_U32_eq   : UScalar.max .U32 = U32.max := by simp [UScalar.max, U32.max, U32.numBits]
@[simp] theorem UScalar.max_UScalarTy_U64_eq   : UScalar.max .U64 = U64.max := by simp [UScalar.max, U64.max, U64.numBits]
@[simp] theorem UScalar.max_UScalarTy_U128_eq  : UScalar.max .U128 = U128.max := by simp [UScalar.max, U128.max, U128.numBits]

@[simp] theorem IScalar.min_IScalarTy_I8_eq    : IScalar.min .I8 = I8.min := by simp [IScalar.min, I8.min, I8.numBits]
@[simp] theorem IScalar.max_IScalarTy_I8_eq    : IScalar.max .I8 = I8.max := by simp [IScalar.max, I8.max, I8.numBits]
@[simp] theorem IScalar.min_IScalarTy_I16_eq   : IScalar.min .I16 = I16.min := by simp [IScalar.min, I16.min, I16.numBits]
@[simp] theorem IScalar.max_IScalarTy_I16_eq   : IScalar.max .I16 = I16.max := by simp [IScalar.max, I16.max, I16.numBits]
@[simp] theorem IScalar.min_IScalarTy_I32_eq   : IScalar.min .I32 = I32.min := by simp [IScalar.min, I32.min, I32.numBits]
@[simp] theorem IScalar.max_IScalarTy_I32_eq   : IScalar.max .I32 = I32.max := by simp [IScalar.max, I32.max, I32.numBits]
@[simp] theorem IScalar.min_IScalarTy_I64_eq   : IScalar.min .I64 = I64.min := by simp [IScalar.min, I64.min, I64.numBits]
@[simp] theorem IScalar.max_IScalarTy_I64_eq   : IScalar.max .I64 = I64.max := by simp [IScalar.max, I64.max, I64.numBits]
@[simp] theorem IScalar.min_IScalarTy_I128_eq  : IScalar.min .I128 = I128.min := by simp [IScalar.min, I128.min, I128.numBits]
@[simp] theorem IScalar.max_IScalarTy_I128_eq  : IScalar.max .I128 = I128.max := by simp [IScalar.max, I128.max, I128.numBits]

local syntax "simp_bounds" : tactic
local macro_rules
| `(tactic|simp_bounds) =>
  `(tactic|
      simp [
      UScalar.rMax, UScalar.max,
      Usize.rMax, Usize.rMax, Usize.max,
      U8.rMax, U8.max, U16.rMax, U16.max, U32.rMax, U32.max,
      U64.rMax, U64.max, U128.rMax, U128.max,
      U8.numBits, U16.numBits, U32.numBits, U64.numBits, U128.numBits, Usize.numBits,
      UScalar.size, U8.size, U16.size, U32.size, U64.size, U128.size, Usize.size,
      IScalar.rMax, IScalar.max,
      IScalar.rMin, IScalar.min,
      Isize.rMax, Isize.rMax, Isize.max,
      I8.rMax, I8.max, I16.rMax, I16.max, I32.rMax, I32.max,
      I64.rMax, I64.max, I128.rMax, I128.max,
      Isize.rMin, Isize.rMin, Isize.min,
      I8.rMin, I8.min, I16.rMin, I16.min, I32.rMin, I32.min,
      I64.rMin, I64.min, I128.rMin, I128.min,
      I8.numBits, I16.numBits, I32.numBits, I64.numBits, I128.numBits, Isize.numBits,
      IScalar.size, I8.size, I16.size, I32.size, I64.size, I128.size, Isize.size])

theorem Usize.bounds_eq :
  Usize.max = U32.max ∨ Usize.max = U64.max := by
  simp [Usize.max, UScalar.max, Usize.numBits]
  cases System.Platform.numBits_eq <;>
  simp [*] <;>
  simp_bounds

theorem Isize.bounds_eq :
  (Isize.min = I32.min ∧ Isize.max = I32.max)
  ∨ (Isize.min = I64.min ∧ Isize.max = I64.max) := by
  simp [Isize.min, Isize.max, IScalar.min, IScalar.max, Isize.numBits]
  cases System.Platform.numBits_eq <;>
  simp [*] <;> simp [*, I32.min, I32.numBits, I32.max, I64.min, I64.numBits, I64.max]

theorem UScalar.rMax_eq_max (ty : UScalarTy) : UScalar.rMax ty = UScalar.max ty := by
  dcases ty <;>
  simp_bounds

theorem IScalar.rbound_eq_bound (ty : IScalarTy) :
  IScalar.rMin ty = IScalar.min ty ∧ IScalar.rMax ty = IScalar.max ty := by
  dcases ty <;> split_conjs <;>
  simp_bounds

theorem IScalar.rMin_eq_min (ty : IScalarTy) : IScalar.rMin ty = IScalar.min ty := by
  apply (IScalar.rbound_eq_bound ty).left

theorem IScalar.rMax_eq_max (ty : IScalarTy) : IScalar.rMax ty = IScalar.max ty := by
  apply (IScalar.rbound_eq_bound ty).right

/-!
# "Conservative" Bounds

We use those because we can't compare to the isize bounds (which can't
reduce at compile-time). Whenever we perform an arithmetic operation like
addition we need to check that the result is in bounds: we first compare
to the conservative bounds, which reduces, then compare to the real bounds.

This is useful for the various #asserts that we want to reduce at
type-checking time, or when defining constants.
-/

def UScalarTy.cNumBits (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => U32.numBits
  | _ => ty.numBits

def IScalarTy.cNumBits (ty : IScalarTy) : Nat :=
  match ty with
  | .Isize => I32.numBits
  | _ => ty.numBits

theorem UScalarTy.cNumBits_le (ty : UScalarTy) : ty.cNumBits ≤ ty.numBits := by
  dcases ty <;> simp [cNumBits, numBits, U32.numBits]
  dcases System.Platform.numBits_eq <;> simp [*]

theorem IScalarTy.cNumBits_le (ty : IScalarTy) : ty.cNumBits ≤ ty.numBits := by
  dcases ty <;> simp [cNumBits, numBits, I32.numBits]
  dcases System.Platform.numBits_eq <;> simp [*]

theorem UScalarTy.cNumBits_nonzero (ty : UScalarTy) : ty.cNumBits ≠ 0 := by
  dcases ty <;> simp [cNumBits, U32.numBits]

theorem IScalarTy.cNumBits_nonzero (ty : IScalarTy) : ty.cNumBits ≠ 0 := by
  dcases ty <;> simp [cNumBits, I32.numBits]

def UScalar.cMax (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => UScalar.rMax .U32
  | _ => UScalar.rMax ty

def IScalar.cMin (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => IScalar.rMin .I32
  | _ => IScalar.rMin ty

def IScalar.cMax (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => IScalar.rMax .I32
  | _ => IScalar.rMax ty

def UScalar.hBounds {ty} (x : UScalar ty) : x.val < 2^ty.numBits := by
  dcases h: x.bv
  simp [h, val]

def UScalar.hSize {ty} (x : UScalar ty) : x.val < UScalar.size ty := by
  dcases h: x.bv
  simp [h, val, size]

def UScalar.rMax_eq_pow_numBits (ty : UScalarTy) : UScalar.rMax ty = 2^ty.numBits - 1 := by
  dcases ty <;> simp [rMax] <;> simp_bounds

def UScalar.cMax_eq_pow_cNumBits (ty : UScalarTy) : UScalar.cMax ty = 2^ty.cNumBits - 1 := by
  dcases ty <;> simp [cMax, UScalarTy.cNumBits] <;> simp_bounds

def UScalar.cMax_le_rMax (ty : UScalarTy) : UScalar.cMax ty ≤ UScalar.rMax ty := by
  have := rMax_eq_pow_numBits ty
  have := cMax_eq_pow_cNumBits ty
  have := ty.cNumBits_le
  have := @Nat.pow_le_pow_of_le_right 2 (by simp) ty.cNumBits ty.numBits ty.cNumBits_le
  omega

def UScalar.hrBounds {ty} (x : UScalar ty) : x.val ≤ UScalar.rMax ty := by
  have := UScalar.hBounds x
  have := UScalar.rMax_eq_pow_numBits ty
  omega

def UScalar.hmax {ty} (x : UScalar ty) : x.val < 2^ty.numBits := x.hBounds

def IScalar.hBounds {ty} (x : IScalar ty) :
  -2^(ty.numBits - 1) ≤ x.val ∧ x.val < 2^(ty.numBits - 1) := by
  match x with
  | ⟨ ⟨ fin ⟩ ⟩ =>
    simp [val, min, max, BitVec.toInt]
    dcases ty <;> simp at * <;> try omega
    have hFinLt := fin.isLt
    cases h: System.Platform.numBits_eq <;>
    simp_all only [IScalarTy.Isize_numBits_eq, true_or, Nat.add_one_sub_one] <;>
    omega

def IScalar.rMin_eq_pow_numBits (ty : IScalarTy) : IScalar.rMin ty = -2^(ty.numBits - 1) := by
  dcases ty <;> simp [cMax] <;> simp_bounds

def IScalar.rMax_eq_pow_numBits (ty : IScalarTy) : IScalar.rMax ty = 2^(ty.numBits - 1) - 1 := by
  dcases ty <;> simp [rMax] <;> simp_bounds

def IScalar.cMin_eq_pow_cNumBits (ty : IScalarTy) : IScalar.cMin ty = -2^(ty.cNumBits - 1) := by
  dcases ty <;> simp [cMin, IScalarTy.cNumBits] <;> simp_bounds

def IScalar.cMax_eq_pow_cNumBits (ty : IScalarTy) : IScalar.cMax ty = 2^(ty.cNumBits - 1) - 1 := by
  dcases ty <;> simp [cMax, IScalarTy.cNumBits] <;> simp_bounds

def IScalar.rMin_le_cMin (ty : IScalarTy) : IScalar.rMin ty ≤ IScalar.cMin ty := by
  have := rMin_eq_pow_numBits ty
  have := cMin_eq_pow_cNumBits ty
  have := ty.cNumBits_le
  have := ty.cNumBits_nonzero
  have := @Int.pow_le_pow_of_le_right 2 (by simp) (ty.cNumBits - 1) (ty.numBits - 1) (by omega)
  zify at this
  omega

def IScalar.cMax_le_rMax (ty : IScalarTy) : IScalar.cMax ty ≤ IScalar.rMax ty := by
  have := rMax_eq_pow_numBits ty
  have := cMax_eq_pow_cNumBits ty
  have := ty.cNumBits_le
  have := ty.cNumBits_nonzero
  have := @Int.pow_le_pow_of_le_right 2 (by simp) (ty.cNumBits - 1) (ty.numBits - 1) (by omega)
  zify at this
  omega

def IScalar.hrBounds {ty} (x : IScalar ty) :
  IScalar.rMin ty ≤ x.val ∧ x.val ≤ IScalar.rMax ty := by
  have := IScalar.hBounds x
  have := IScalar.rMin_eq_pow_numBits ty
  have := IScalar.rMax_eq_pow_numBits ty
  omega

def IScalar.hmin {ty} (x : IScalar ty) : -2^(ty.numBits - 1) ≤ x.val := x.hBounds.left
def IScalar.hmax {ty} (x : IScalar ty) : x.val < 2^(ty.numBits - 1) := x.hBounds.right

instance {ty} : BEq (UScalar ty) where
  beq a b := a.bv = b.bv

instance {ty} : BEq (IScalar ty) where
  beq a b := a.bv = b.bv

instance {ty} : LawfulBEq (UScalar ty) where
  eq_of_beq {a b} := by cases a; cases b; simp [BEq.beq]
  rfl {a} := by cases a; simp [BEq.beq]

instance {ty} : LawfulBEq (IScalar ty) where
  eq_of_beq {a b} := by cases a; cases b; simp[BEq.beq]
  rfl {a} := by cases a; simp [BEq.beq]

instance (ty : UScalarTy) : CoeOut (UScalar ty) Nat where
  coe := λ v => v.val

instance (ty : IScalarTy) : CoeOut (IScalar ty) Int where
  coe := λ v => v.val

/- Activate the ↑ notation -/
attribute [coe] UScalar.val IScalar.val

theorem UScalar.bound_suffices (ty : UScalarTy) (x : Nat) :
  x ≤ UScalar.cMax ty -> x < 2^ty.numBits
  := by
  intro h
  have := UScalar.rMax_eq_pow_numBits ty
  have : 0 < 2^ty.numBits := by simp
  have := cMax_le_rMax ty
  omega

theorem IScalar.bound_suffices (ty : IScalarTy) (x : Int) :
  IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty ->
  -2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)
  := by
  intro h
  have := ty.cNumBits_nonzero
  have := ty.numBits_nonzero
  have := ty.cNumBits_le
  have := IScalar.rMin_eq_pow_numBits ty
  have := IScalar.rMax_eq_pow_numBits ty
  have := rMin_le_cMin ty
  have := cMax_le_rMax ty
  omega

/- TODO: remove? Having a check on the bounds is a good sanity check, and it allows to prove
   nice theorems like `(ofIntCore x ..).val = x`. But on the other hand `BitVec` also has powerful
   simplification lemmas. -/
def UScalar.ofNatCore {ty : UScalarTy} (x : Nat) (_ : x < 2^ty.numBits) : UScalar ty :=
  { bv := BitVec.ofNat _ x }

-- TODO: remove?
def IScalar.ofIntCore {ty : IScalarTy} (x : Int) (_ : -2^(ty.numBits-1) ≤ x ∧ x < 2^(ty.numBits - 1)) : IScalar ty :=
  { bv := BitVec.ofInt _ x }

@[reducible] def UScalar.ofNat {ty : UScalarTy} (x : Nat)
  (hInBounds : x ≤ UScalar.cMax ty := by decide) : UScalar ty :=
  UScalar.ofNatCore x (UScalar.bound_suffices ty x hInBounds)

@[reducible] def IScalar.ofInt {ty : IScalarTy} (x : Int)
  (hInBounds : IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty := by decide) : IScalar ty :=
  IScalar.ofIntCore x (IScalar.bound_suffices ty x hInBounds)

@[simp] abbrev UScalar.inBounds (ty : UScalarTy) (x : Nat) : Prop :=
  x < 2^ty.numBits

@[simp] abbrev IScalar.inBounds (ty : IScalarTy) (x : Int) : Prop :=
  - 2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)

@[simp] abbrev UScalar.check_bounds (ty : UScalarTy) (x : Nat) : Bool :=
  x < 2^ty.numBits

@[simp] abbrev IScalar.check_bounds (ty : IScalarTy) (x : Int) : Bool :=
  -2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)

/- Discussion:
   This coercion can be slightly annoying at times, because if we write
   something like `u = 3` (where `u` is, for instance, a `U32`), then instead of
   coercing `u` to `Nat`, Lean will lift `3` to `U32`).
   For now we deactivate it.

-- TODO(raitobezarius): the inbounds constraint is a bit ugly as we can pretty trivially
-- discharge the lhs on ≥ 0.
instance {ty: ScalarTy} [InBounds ty (Int.ofNat n)]: OfNat (Scalar ty) (n: ℕ) where
  ofNat := Scalar.ofInt n
-/

theorem UScalar.check_bounds_imp_inBounds {ty : UScalarTy} {x : Nat}
  (h: UScalar.check_bounds ty x) :
  UScalar.inBounds ty x := by
  simp at *; apply h

theorem UScalar.check_bounds_eq_inBounds (ty : UScalarTy) (x : Nat) :
  UScalar.check_bounds ty x ↔ UScalar.inBounds ty x := by
  constructor <;> intro h
  . apply (check_bounds_imp_inBounds h)
  . simp_all

theorem IScalar.check_bounds_imp_inBounds {ty : IScalarTy} {x : Int}
  (h: IScalar.check_bounds ty x) :
  IScalar.inBounds ty x := by
  simp at *; apply h

theorem IScalar.check_bounds_eq_inBounds (ty : IScalarTy) (x : Int) :
  IScalar.check_bounds ty x ↔ IScalar.inBounds ty x := by
  constructor <;> intro h
  . apply (check_bounds_imp_inBounds h)
  . simp_all

def UScalar.tryMkOpt (ty : UScalarTy) (x : Nat) : Option (UScalar ty) :=
  if h:UScalar.check_bounds ty x then
    some (UScalar.ofNatCore x (UScalar.check_bounds_imp_inBounds h))
  else none

def UScalar.tryMk (ty : UScalarTy) (x : Nat) : Result (UScalar ty) :=
  Result.ofOption (tryMkOpt ty x) integerOverflow

def IScalar.tryMkOpt (ty : IScalarTy) (x : Int) : Option (IScalar ty) :=
  if h:IScalar.check_bounds ty x then
    some (IScalar.ofIntCore x (IScalar.check_bounds_imp_inBounds h))
  else none

def IScalar.tryMk (ty : IScalarTy) (x : Int) : Result (IScalar ty) :=
  Result.ofOption (tryMkOpt ty x) integerOverflow

theorem UScalar.tryMkOpt_eq (ty : UScalarTy) (x : Nat) :
  match tryMkOpt ty x with
  | some y => y.val = x ∧ inBounds ty x
  | none => ¬ (inBounds ty x) := by
  simp [tryMkOpt, ofNatCore]
  have h := check_bounds_eq_inBounds ty x
  split_ifs <;> simp_all
  simp [UScalar.val, UScalarTy.numBits, max] at *
  dcases ty <;> simp_all [U8.max, U16.max, U32.max, U64.max, U128.max, Usize.max, max]
  cases h: System.Platform.numBits_eq <;> simp_all

theorem UScalar.tryMk_eq (ty : UScalarTy) (x : Nat) :
  match tryMk ty x with
  | ok y => y.val = x ∧ inBounds ty x
  | fail _ => ¬ (inBounds ty x)
  | _ => False := by
  have := UScalar.tryMkOpt_eq ty x
  simp [tryMk, ofOption]
  dcases h: tryMkOpt ty x <;> simp_all

theorem IScalar.tryMkOpt_eq (ty : IScalarTy) (x : Int) :
  match tryMkOpt ty x with
  | some y => y.val = x ∧ inBounds ty x
  | none => ¬ (inBounds ty x) := by
  simp [tryMkOpt, ofIntCore]
  have h := check_bounds_eq_inBounds ty x
  split_ifs <;> simp_all
  simp [IScalar.val, IScalarTy.numBits, min, max] at *
  dcases ty <;>
  simp_all [I8.min, I16.min, I32.min, I64.min, I128.min, Isize.min,
            I8.max, I16.max, I32.max, I64.max, I128.max, Isize.max,
            min, max] <;>
  simp [Int.bmod] <;> split <;> (try omega) <;>
  cases h: System.Platform.numBits_eq <;> simp_all <;> omega

theorem IScalar.tryMk_eq (ty : IScalarTy) (x : Int) :
  match tryMk ty x with
  | ok y => y.val = x ∧ inBounds ty x
  | fail _ => ¬ (inBounds ty x)
  | _ => False := by
  have := tryMkOpt_eq ty x
  simp [tryMk, ofIntCore]
  dcases h : tryMkOpt ty x <;> simp_all

@[simp] theorem UScalar.zero_in_cbounds {ty : UScalarTy} : 0 < 2^ty.numBits := by
  simp

@[simp] theorem IScalar.zero_in_cbounds {ty : IScalarTy} :
  -2^(ty.numBits - 1) ≤ 0 ∧ 0 < 2^(ty.numBits - 1) := by
  cases ty <;> simp

/-! The scalar types. -/
abbrev  Usize := UScalar .Usize
abbrev  U8    := UScalar .U8
abbrev  U16   := UScalar .U16
abbrev  U32   := UScalar .U32
abbrev  U64   := UScalar .U64
abbrev  U128  := UScalar .U128
abbrev  Isize := IScalar .Isize
abbrev  I8    := IScalar .I8
abbrev  I16   := IScalar .I16
abbrev  I32   := IScalar .I32
abbrev  I64   := IScalar .I64
abbrev  I128  := IScalar .I128

/-!  ofNatCore -/
-- TODO: typeclass?
def Usize.ofNatCore := @UScalar.ofNatCore .Usize
def U8.ofNatCore    := @UScalar.ofNatCore .U8
def U16.ofNatCore   := @UScalar.ofNatCore .U16
def U32.ofNatCore   := @UScalar.ofNatCore .U32
def U64.ofNatCore   := @UScalar.ofNatCore .U64
def U128.ofNatCore  := @UScalar.ofNatCore .U128

/-!  ofIntCore -/
def Isize.ofIntCore := @IScalar.ofIntCore .Isize
def I8.ofIntCore    := @IScalar.ofIntCore .I8
def I16.ofIntCore   := @IScalar.ofIntCore .I16
def I32.ofIntCore   := @IScalar.ofIntCore .I32
def I64.ofIntCore   := @IScalar.ofIntCore .I64
def I128.ofIntCore  := @IScalar.ofIntCore .I128

/-!  ofNat -/
-- TODO: typeclass?
abbrev Usize.ofNat := @UScalar.ofNat .Usize
abbrev U8.ofNat    := @UScalar.ofNat .U8
abbrev U16.ofNat   := @UScalar.ofNat .U16
abbrev U32.ofNat   := @UScalar.ofNat .U32
abbrev U64.ofNat   := @UScalar.ofNat .U64
abbrev U128.ofNat  := @UScalar.ofNat .U128

/-!  ofInt -/
abbrev Isize.ofInt := @IScalar.ofInt .Isize
abbrev I8.ofInt    := @IScalar.ofInt .I8
abbrev I16.ofInt   := @IScalar.ofInt .I16
abbrev I32.ofInt   := @IScalar.ofInt .I32
abbrev I64.ofInt   := @IScalar.ofInt .I64
abbrev I128.ofInt  := @IScalar.ofInt .I128

@[simp, scalar_tac_simp, bvify_simps] theorem UScalar.ofNat_val_eq {ty : UScalarTy} (h : x < 2^ty.numBits) :
  (UScalar.ofNatCore x h).val = x := by
  simp [UScalar.ofNat, UScalar.ofNatCore, UScalar.val, max]
  dcases ty <;> simp_all
  cases h: System.Platform.numBits_eq <;> simp_all

@[simp, scalar_tac_simp] theorem U8.ofNat_val_eq (h : x < 2^UScalarTy.U8.numBits) : (U8.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp, scalar_tac_simp] theorem U16.ofNat_val_eq (h : x < 2^UScalarTy.U16.numBits) : (U16.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp, scalar_tac_simp] theorem U32.ofNat_val_eq (h : x < 2^UScalarTy.U32.numBits) : (U32.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp, scalar_tac_simp] theorem U64.ofNat_val_eq (h : x < 2^UScalarTy.U64.numBits) : (U64.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp, scalar_tac_simp] theorem U128.ofNat_val_eq (h : x < 2^UScalarTy.U128.numBits) : (U128.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp, scalar_tac_simp] theorem Usize.ofNat_val_eq (h : x < 2^UScalarTy.Usize.numBits) : (Usize.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp, scalar_tac_simp, bvify_simps] theorem IScalar.ofInt_val_eq {ty : IScalarTy} (h : - 2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)) :
  (IScalar.ofIntCore x h).val = x := by
  simp [IScalar.ofInt, IScalar.ofIntCore, IScalar.val]
  dcases ty <;>
  simp_all <;>
  simp [Int.bmod] <;> split <;> (try omega) <;>
  cases h: System.Platform.numBits_eq <;> simp_all <;> omega

@[simp, scalar_tac_simp] theorem I8.ofInt_val_eq (h : -2^(IScalarTy.I8.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I8.numBits-1)) : (I8.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

@[simp, scalar_tac_simp] theorem I16.ofInt_val_eq (h : -2^(IScalarTy.I16.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I16.numBits-1)) : (I16.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

@[simp, scalar_tac_simp] theorem I32.ofInt_val_eq (h : -2^(IScalarTy.I32.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I32.numBits-1)) : (I32.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

@[simp, scalar_tac_simp] theorem I64.ofInt_val_eq (h : -2^(IScalarTy.I64.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I64.numBits-1)) : (I64.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

@[simp, scalar_tac_simp] theorem I128.ofInt_val_eq (h : -2^(IScalarTy.I128.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I128.numBits-1)) : (I128.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

@[simp, scalar_tac_simp] theorem Isize.ofInt_val_eq (h : -2^(IScalarTy.Isize.numBits-1) ≤ x ∧ x < 2^(IScalarTy.Isize.numBits-1)) : (Isize.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

theorem UScalar.eq_equiv_bv_eq {ty : UScalarTy} (x y : UScalar ty) :
  x = y ↔ x.bv = y.bv := by
  cases x; cases y; simp

@[bvify_simps] theorem U8.eq_equiv_bv_eq (x y : U8) : x = y ↔ x.bv = y.bv := by apply UScalar.eq_equiv_bv_eq
@[bvify_simps] theorem U16.eq_equiv_bv_eq (x y : U16) : x = y ↔ x.bv = y.bv := by apply UScalar.eq_equiv_bv_eq
@[bvify_simps] theorem U32.eq_equiv_bv_eq (x y : U32) : x = y ↔ x.bv = y.bv := by apply UScalar.eq_equiv_bv_eq
@[bvify_simps] theorem U64.eq_equiv_bv_eq (x y : U64) : x = y ↔ x.bv = y.bv := by apply UScalar.eq_equiv_bv_eq
@[bvify_simps] theorem U128.eq_equiv_bv_eq (x y : U128) : x = y ↔ x.bv = y.bv := by apply UScalar.eq_equiv_bv_eq
@[bvify_simps] theorem Usize.eq_equiv_bv_eq (x y : Usize) : x = y ↔ x.bv = y.bv := by apply UScalar.eq_equiv_bv_eq

theorem UScalar.ofNatCore_bv {ty : UScalarTy} (x : Nat) h :
  (@UScalar.ofNatCore ty x h).bv = BitVec.ofNat _ x := by
  simp only [ofNatCore, bv]

@[simp, bvify_simps] theorem U8.ofNat_bv (x : Nat) h : (U8.ofNat x h).bv = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv
@[simp, bvify_simps] theorem U16.ofNat_bv (x : Nat) h : (U16.ofNat x h).bv = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv
@[simp, bvify_simps] theorem U32.ofNat_bv (x : Nat) h : (U32.ofNat x h).bv = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv
@[simp, bvify_simps] theorem U64.ofNat_bv (x : Nat) h : (U64.ofNat x h).bv = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv
@[simp, bvify_simps] theorem U128.ofNat_bv (x : Nat) h : (U128.ofNat x h).bv = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv
@[simp, bvify_simps] theorem Usize.ofNat_bv (x : Nat) h : (Usize.ofNat x h).bv = BitVec.ofNat _ x := by apply UScalar.ofNatCore_bv

theorem IScalar.eq_equiv_bv_eq {ty : IScalarTy} (x y : IScalar ty) :
  x = y ↔ x.bv = y.bv := by
  cases x; cases y; simp

@[bvify_simps] theorem I8.eq_equiv_bv_eq (x y : I8) : x = y ↔ x.bv = y.bv := by apply IScalar.eq_equiv_bv_eq
@[bvify_simps] theorem I16.eq_equiv_bv_eq (x y : I16) : x = y ↔ x.bv = y.bv := by apply IScalar.eq_equiv_bv_eq
@[bvify_simps] theorem I32.eq_equiv_bv_eq (x y : I32) : x = y ↔ x.bv = y.bv := by apply IScalar.eq_equiv_bv_eq
@[bvify_simps] theorem I64.eq_equiv_bv_eq (x y : I64) : x = y ↔ x.bv = y.bv := by apply IScalar.eq_equiv_bv_eq
@[bvify_simps] theorem I128.eq_equiv_bv_eq (x y : I128) : x = y ↔ x.bv = y.bv := by apply IScalar.eq_equiv_bv_eq
@[bvify_simps] theorem Isize.eq_equiv_bv_eq (x y : Isize) : x = y ↔ x.bv = y.bv := by apply IScalar.eq_equiv_bv_eq

theorem IScalar.ofIntCore_bv {ty : IScalarTy} (x : Int) h :
  (@IScalar.ofIntCore ty x h).bv = BitVec.ofInt _ x := by
  simp only [ofIntCore, bv]

@[simp, bvify_simps] theorem I8.ofInt_bv (x : Int) h : (I8.ofInt x h).bv = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv
@[simp, bvify_simps] theorem I16.ofInt_bv (x : Int) h : (I16.ofInt x h).bv = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv
@[simp, bvify_simps] theorem I32.ofInt_bv (x : Int) h : (I32.ofInt x h).bv = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv
@[simp, bvify_simps] theorem I64.ofInt_bv (x : Int) h : (I64.ofInt x h).bv = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv
@[simp, bvify_simps] theorem I128.ofInt_bv (x : Int) h : (I128.ofInt x h).bv = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv
@[simp, bvify_simps] theorem Isize.ofInt_bv (x : Int) h : (Isize.ofInt x h).bv = BitVec.ofInt _ x := by apply IScalar.ofIntCore_bv

instance (ty : UScalarTy) : Inhabited (UScalar ty) := by
  constructor; cases ty <;> apply (UScalar.ofNat 0 (by simp))

instance (ty : IScalarTy) : Inhabited (IScalar ty) := by
  constructor; cases ty <;> apply (IScalar.ofInt 0 (by simp [IScalar.cMin, IScalar.cMax, IScalar.rMin, IScalar.rMax]; simp_bounds))

theorem IScalar.min_lt_max (ty : IScalarTy) : IScalar.min ty < IScalar.max ty := by
  cases ty <;> simp [IScalar.min, IScalar.max] <;> (try simp_bounds)
  have : (0 : Int) < 2 ^ (System.Platform.numBits - 1) := by simp
  omega

theorem IScalar.min_le_max (ty : IScalarTy) : IScalar.min ty ≤ IScalar.max ty := by
  have := IScalar.min_lt_max ty
  scalar_tac

@[reducible] def core_u8_min : U8 := UScalar.ofNat 0
@[reducible] def core_u8_max : U8 := UScalar.ofNat U8.rMax
@[reducible] def core_u16_min : U16 := UScalar.ofNat 0
@[reducible] def core_u16_max : U16 := UScalar.ofNat U16.rMax
@[reducible] def core_u32_min : U32 := UScalar.ofNat 0
@[reducible] def core_u32_max : U32 := UScalar.ofNat U32.rMax
@[reducible] def core_u64_min : U64 := UScalar.ofNat 0
@[reducible] def core_u64_max : U64 := UScalar.ofNat U64.rMax
@[reducible] def core_u128_min : U128 := UScalar.ofNat 0
@[reducible] def core_u128_max : U128 := UScalar.ofNat U128.rMax
@[reducible] def core_usize_min : Usize := UScalar.ofNatCore 0 (by simp)
@[reducible] def core_usize_max : Usize := UScalar.ofNatCore Usize.max (by simp [Usize.max, Usize.numBits, UScalar.rMax])

@[reducible] def core_i8_min : I8 := IScalar.ofInt I8.rMin
@[reducible] def core_i8_max : I8 := IScalar.ofInt I8.rMax
@[reducible] def core_i16_min : I16 := IScalar.ofInt I16.rMin
@[reducible] def core_i16_max : I16 := IScalar.ofInt I16.rMax
@[reducible] def core_i32_min : I32 := IScalar.ofInt I32.rMin
@[reducible] def core_i32_max : I32 := IScalar.ofInt I32.rMax
@[reducible] def core_i64_min : I64 := IScalar.ofInt I64.rMin
@[reducible] def core_i64_max : I64 := IScalar.ofInt I64.rMax
@[reducible] def core_i128_min : I128 := IScalar.ofInt I128.rMin
@[reducible] def core_i128_max : I128 := IScalar.ofInt I128.rMax
@[reducible] def core_isize_min : Isize := IScalar.ofIntCore Isize.min (by simp [Isize.min, Isize.numBits, Isize.rMin])
@[reducible] def core_isize_max : Isize := IScalar.ofIntCore Isize.max (by simp [Isize.max, Isize.numBits, Isize.rMax]; (have : (0 : Int) < 2 ^ (System.Platform.numBits - 1) := by simp); omega)


/-! # Comparisons -/
instance {ty} : LT (UScalar ty) where
  lt a b := LT.lt a.val b.val

instance {ty} : LE (UScalar ty) where le a b := LE.le a.val b.val

instance {ty} : LT (IScalar ty) where
  lt a b := LT.lt a.val b.val

instance {ty} : LE (IScalar ty) where le a b := LE.le a.val b.val

/- Not marking this one with @[simp] on purpose: if we have `x = y` somewhere in the context,
   we may want to use it to substitute `y` with `x` somewhere. -/
@[scalar_tac_simp] theorem UScalar.eq_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x = y ↔ (↑x : Nat) = ↑y := by
  cases x; cases y; simp_all [UScalar.val, BitVec.toNat_eq]

@[simp] theorem UScalar.eq_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) = ↑y → x = y := (eq_equiv x y).mpr

@[simp, scalar_tac_simp] theorem UScalar.lt_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x < y ↔ (↑x : Nat) < ↑y := by
  rw [LT.lt, instLTUScalar]

@[simp] theorem UScalar.lt_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) < (↑y) → x < y := (lt_equiv x y).mpr

@[simp, scalar_tac_simp] theorem UScalar.le_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x ≤ y ↔ (↑x : Nat) ≤ ↑y := by
  rw [LE.le, instLEUScalar]

@[simp] theorem UScalar.le_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

@[scalar_tac_simp] theorem IScalar.eq_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x = y ↔ (↑x : Int) = ↑y := by
  cases x; cases y; simp_all [IScalar.val]
  constructor <;> intro <;>
  first | simp [*] | apply BitVec.eq_of_toInt_eq; simp [*]

@[simp] theorem IScalar.eq_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) = ↑y → x = y := (eq_equiv x y).mpr

@[simp, scalar_tac_simp] theorem IScalar.lt_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x < y ↔ (↑x : Int) < ↑y := by
  rw [LT.lt, instLTIScalar]

@[simp, scalar_tac_simp] theorem IScalar.lt_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) < (↑y) → x < y := (lt_equiv x y).mpr

@[simp] theorem IScalar.le_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x ≤ y ↔ (↑x : Int) ≤ ↑y := by simp [LE.le]

@[simp] theorem IScalar.le_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

instance UScalar.decLt {ty} (a b : UScalar ty) : Decidable (LT.lt a b) := Nat.decLt ..
instance UScalar.decLe {ty} (a b : UScalar ty) : Decidable (LE.le a b) := Nat.decLe ..
instance IScalar.decLt {ty} (a b : IScalar ty) : Decidable (LT.lt a b) := Int.decLt ..
instance IScalar.decLe {ty} (a b : IScalar ty) : Decidable (LE.le a b) := Int.decLe ..

theorem UScalar.eq_of_val_eq {ty} : ∀ {i j : UScalar ty}, Eq i.val j.val → Eq i j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem IScalar.eq_of_val_eq {ty} : ∀ {i j : IScalar ty}, Eq i.val j.val → Eq i j := by
  intro i j hEq
  dcases i; dcases j
  simp [IScalar.val] at hEq; simp
  apply BitVec.eq_of_toInt_eq; assumption

theorem UScalar.val_eq_of_eq {ty} {i j : UScalar ty} (h : Eq i j) : Eq i.val j.val := h ▸ rfl
theorem IScalar.val_eq_of_eq {ty} {i j : IScalar ty} (h : Eq i j) : Eq i.val j.val := h ▸ rfl

theorem UScalar.ne_of_val_ne {ty} {i j : UScalar ty} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h

theorem IScalar.ne_of_val_ne {ty} {i j : IScalar ty} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h

instance (ty : UScalarTy) : DecidableEq (UScalar ty) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (UScalar.eq_of_val_eq h)
    | isFalse h => isFalse (UScalar.ne_of_val_ne h)

instance (ty : IScalarTy) : DecidableEq (IScalar ty) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (IScalar.eq_of_val_eq h)
    | isFalse h => isFalse (IScalar.ne_of_val_ne h)

@[simp, scalar_tac_simp] theorem UScalar.neq_to_neq_val {ty} : ∀ {i j : UScalar ty}, (¬ i = j) ↔ ¬ i.val = j.val := by
  simp [eq_equiv]

@[simp, scalar_tac_simp] theorem IScalar.neq_to_neq_val {ty} : ∀ {i j : IScalar ty}, (¬ i = j) ↔ ¬ i.val = j.val := by
  simp [eq_equiv]

@[simp]
theorem UScalar.val_not_eq_imp_not_eq (x y : UScalar ty) (h : ScalarTac.Nat.not_eq x.val y.val) :
  ¬ x = y := by
  simp_all; scalar_tac

@[simp]
theorem IScalar.val_not_eq_imp_not_eq (x y : IScalar ty) (h : ScalarTac.Int.not_eq x.val y.val) :
  ¬ x = y := by
  simp_all; scalar_tac

instance (ty: UScalarTy) : Preorder (UScalar ty) where
  le_refl := fun a => by simp
  le_trans := fun a b c => by
    intro Hab Hbc
    exact (le_trans ((UScalar.le_equiv _ _).1 Hab) ((UScalar.le_equiv _ _).1 Hbc))
  lt_iff_le_not_le := fun a b => by
    trans (a: Nat) < (b: Nat); exact (UScalar.lt_equiv _ _)
    trans (a: Nat) ≤ (b: Nat) ∧ ¬ (b: Nat) ≤ (a: Nat); exact lt_iff_le_not_le
    repeat rewrite [← UScalar.le_equiv]; rfl

instance (ty: IScalarTy) : Preorder (IScalar ty) where
  le_refl := fun a => by simp
  le_trans := fun a b c => by
    intro Hab Hbc
    exact (le_trans ((IScalar.le_equiv _ _).1 Hab) ((IScalar.le_equiv _ _).1 Hbc))
  lt_iff_le_not_le := fun a b => by
    trans (a: Int) < (b: Int); exact (IScalar.lt_equiv _ _)
    trans (a: Int) ≤ (b: Int) ∧ ¬ (b: Int) ≤ (a: Int); exact lt_iff_le_not_le
    repeat rewrite [← IScalar.le_equiv]; rfl

instance (ty: UScalarTy) : PartialOrder (UScalar ty) where
  le_antisymm := fun a b Hab Hba =>
    UScalar.eq_imp _ _ ((@le_antisymm Nat _ _ _ ((UScalar.le_equiv a b).1 Hab) ((UScalar.le_equiv b a).1 Hba)))

instance (ty: IScalarTy) : PartialOrder (IScalar ty) where
  le_antisymm := fun a b Hab Hba =>
    IScalar.eq_imp _ _ ((@le_antisymm Int _ _ _ ((IScalar.le_equiv a b).1 Hab) ((IScalar.le_equiv b a).1 Hba)))

instance UScalarDecidableLE (ty: UScalarTy) : DecidableRel (· ≤ · : UScalar ty -> UScalar ty -> Prop) := by
  simp [instLEUScalar]
  -- Lift this to the decidability of the Int version.
  infer_instance

instance IScalarDecidableLE (ty: IScalarTy) : DecidableRel (· ≤ · : IScalar ty -> IScalar ty -> Prop) := by
  simp [instLEIScalar]
  -- Lift this to the decidability of the Int version.
  infer_instance

instance (ty: UScalarTy) : LinearOrder (UScalar ty) where
  le_total := fun a b => by
    rcases (Nat.le_total a b) with H | H
    left; exact (UScalar.le_equiv _ _).2 H
    right; exact (UScalar.le_equiv _ _).2 H
  decidableLE := UScalarDecidableLE ty

instance (ty: IScalarTy) : LinearOrder (IScalar ty) where
  le_total := fun a b => by
    rcases (Int.le_total a b) with H | H
    left; exact (IScalar.le_equiv _ _).2 H
    right; exact (IScalar.le_equiv _ _).2 H
  decidableLE := IScalarDecidableLE ty

/-! # Coercion Theorems

    This is helpful whenever you want to "push" casts to the innermost nodes
    and make the cast normalization happen more magically. -/

@[simp, norm_cast]
theorem UScalar.coe_max {ty: UScalarTy} (a b: UScalar ty): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℕ) := by
  rw[_root_.max_def, _root_.max_def]
  split_ifs <;> simp_all

@[simp, norm_cast]
theorem IScalar.coe_max {ty: IScalarTy} (a b: IScalar ty): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℤ) := by
  rw[_root_.max_def, _root_.max_def]
  split_ifs <;> simp_all

/-! Max theory -/
-- TODO: do the min theory later on.

theorem UScalar.zero_le {ty} (x: UScalar ty): UScalar.ofNat 0 (by simp) ≤ x := by simp

@[simp]
theorem UScalar.max_left_zero_eq {ty} (x: UScalar ty):
  Max.max (UScalar.ofNat 0 (by simp)) x = x := max_eq_right (UScalar.zero_le x)

@[simp]
theorem UScalar.max_right_zero_eq {ty} (x: UScalar ty):
  Max.max x (UScalar.ofNat 0 (by simp)) = x := max_eq_left (UScalar.zero_le x)

/-! Some conversions -/
@[simp, bvify_simps] abbrev IScalar.toNat (x : IScalar ty) : Nat := x.val.toNat
@[simp, bvify_simps] abbrev I8.toNat      (x : I8) : Nat := x.val.toNat
@[simp, bvify_simps] abbrev I16.toNat     (x : I16) : Nat := x.val.toNat
@[simp, bvify_simps] abbrev I32.toNat     (x : I32) : Nat := x.val.toNat
@[simp, bvify_simps] abbrev I64.toNat     (x : I64) : Nat := x.val.toNat
@[simp, bvify_simps] abbrev I128.toNat    (x : I128) : Nat := x.val.toNat
@[simp, bvify_simps] abbrev Isize.toNat   (x : Isize) : Nat := x.val.toNat

abbrev U8.bv (x : U8)   : BitVec 8 := UScalar.bv x
abbrev U16.bv (x : U16) : BitVec 16 := UScalar.bv x
abbrev U32.bv (x : U32) : BitVec 32 := UScalar.bv x
abbrev U64.bv (x : U64) : BitVec 64 := UScalar.bv x
abbrev U128.bv (x : U128) : BitVec 128 := UScalar.bv x
abbrev Usize.bv (x : Usize) : BitVec System.Platform.numBits := UScalar.bv x

abbrev I8.bv (x : I8) : BitVec 8 := IScalar.bv x
abbrev I16.bv (x : I16) : BitVec 16 := IScalar.bv x
abbrev I32.bv (x : I32) : BitVec 32 := IScalar.bv x
abbrev I64.bv (x : I64) : BitVec 64 := IScalar.bv x
abbrev I128.bv (x : I128) : BitVec 128 := IScalar.bv x
abbrev Isize.bv (x : Isize) : BitVec System.Platform.numBits := IScalar.bv x

@[simp, scalar_tac_simp] theorem UScalar.bv_toNat_eq {ty : UScalarTy} (x : UScalar ty) :
  (UScalar.bv x).toNat  = x.val := by
  simp [val]

@[simp, scalar_tac_simp] theorem U8.bv_toNat_eq (x : U8) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq
@[simp, scalar_tac_simp] theorem U16.bv_toNat_eq (x : U16) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq
@[simp, scalar_tac_simp] theorem U32.bv_toNat_eq (x : U32) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq
@[simp, scalar_tac_simp] theorem U64.bv_toNat_eq (x : U64) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq
@[simp, scalar_tac_simp] theorem U128.bv_toNat_eq (x : U128) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq
@[simp, scalar_tac_simp] theorem Usize.bv_toNat_eq (x : Usize) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq

@[simp, scalar_tac_simp] theorem IScalar.bv_toInt_eq {ty : IScalarTy} (x : IScalar ty) :
  (IScalar.bv x).toInt  = x.val := by
  simp [val]

@[simp, scalar_tac_simp] theorem I8.bv_toInt_eq (x : I8) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq
@[simp, scalar_tac_simp] theorem I16.bv_toInt_eq (x : I16) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq
@[simp, scalar_tac_simp] theorem I32.bv_toInt_eq (x : I32) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq
@[simp, scalar_tac_simp] theorem I64.bv_toInt_eq (x : I64) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq
@[simp, scalar_tac_simp] theorem I128.bv_toInt_eq (x : I128) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq
@[simp, scalar_tac_simp] theorem Isize.bv_toInt_eq (x : Isize) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq

@[bvify_simps] theorem U8.lt_succ_max (x: U8) : x.val < 256 := by have := x.hBounds; simp at this; omega
@[bvify_simps] theorem U16.lt_succ_max (x: U16) : x.val < 65536 := by have := x.hBounds; simp at this; omega
@[bvify_simps] theorem U32.lt_succ_max (x: U32) : x.val < 4294967296 := by have := x.hBounds; simp at this; omega
@[bvify_simps] theorem U64.lt_succ_max (x: U64) : x.val < 18446744073709551616 := by have := x.hBounds; simp at this; omega
@[bvify_simps] theorem U128.lt_succ_max (x: U128) : x.val < 340282366920938463463374607431768211456 := by have := x.hBounds; simp at this; omega

@[bvify_simps] theorem U8.le_max (x: U8) : x.val ≤ 255 := by have := x.hBounds; simp at this; omega
@[bvify_simps] theorem U16.le_max (x: U16) : x.val ≤ 65535 := by have := x.hBounds; simp at this; omega
@[bvify_simps] theorem U32.le_max (x: U32) : x.val ≤ 4294967295 := by have := x.hBounds; simp at this; omega
@[bvify_simps] theorem U64.le_max (x: U64) : x.val ≤ 18446744073709551615 := by have := x.hBounds; simp at this; omega
@[bvify_simps] theorem U128.le_max (x: U128) : x.val ≤ 340282366920938463463374607431768211455 := by have := x.hBounds; simp at this; omega

@[simp, bvify_simps] theorem UScalar.BitVec_ofNat_val_eq (x : UScalar ty) : BitVec.ofNat ty.numBits x.val = x.bv := by
  cases x; simp only [val, BitVec.ofNat_toNat, BitVec.setWidth_eq]

@[bvify_simps] theorem U8.BitVec_ofNat_val_eq (x : U8) : BitVec.ofNat 8 x.val = x.bv := by apply UScalar.BitVec_ofNat_val_eq
@[bvify_simps] theorem U16.BitVec_ofNat_val_eq (x : U16) : BitVec.ofNat 16 x.val = x.bv := by apply UScalar.BitVec_ofNat_val_eq
@[bvify_simps] theorem U32.BitVec_ofNat_val_eq (x : U32) : BitVec.ofNat 32 x.val = x.bv := by apply UScalar.BitVec_ofNat_val_eq
@[bvify_simps] theorem U64.BitVec_ofNat_val_eq (x : U64) : BitVec.ofNat 64 x.val = x.bv := by apply UScalar.BitVec_ofNat_val_eq
@[bvify_simps] theorem U128.BitVec_ofNat_val_eq (x : U128) : BitVec.ofNat 128 x.val = x.bv := by apply UScalar.BitVec_ofNat_val_eq
@[bvify_simps] theorem Usize.BitVec_ofNat_val_eq (x : Usize) : BitVec.ofNat System.Platform.numBits x.val = x.bv := by apply UScalar.BitVec_ofNat_val_eq

/-!
Adding theorems to the `zify_simps` simplification set.
-/
attribute [zify_simps] UScalar.eq_equiv IScalar.eq_equiv
                       UScalar.lt_equiv IScalar.lt_equiv
                       UScalar.le_equiv IScalar.le_equiv

attribute [zify_simps] U8.bv_toNat_eq U16.bv_toNat_eq U32.bv_toNat_eq
                       U64.bv_toNat_eq U128.bv_toNat_eq Usize.bv_toNat_eq

@[simp, progress_post_simp] theorem UScalar.size_UScalarTyU8 : UScalar.size .U8 = U8.size := by simp_bounds
@[simp, progress_post_simp] theorem UScalar.size_UScalarTyU16 : UScalar.size .U16 = U16.size := by simp_bounds
@[simp, progress_post_simp] theorem UScalar.size_UScalarTyU32 : UScalar.size .U32 = U32.size := by simp_bounds
@[simp, progress_post_simp] theorem UScalar.size_UScalarTyU64 : UScalar.size .U64 = U64.size := by simp_bounds
@[simp, progress_post_simp] theorem UScalar.size_UScalarTyU128 : UScalar.size .U128 = U128.size := by simp_bounds
@[simp, progress_post_simp] theorem UScalar.size_UScalarTyUsize : UScalar.size .Usize = Usize.size := by simp_bounds

@[simp, progress_post_simp] theorem IScalar.size_IScalarTyI8 : IScalar.size .I8 = I8.size := by simp_bounds
@[simp, progress_post_simp] theorem IScalar.size_IScalarTyI16 : IScalar.size .I16 = I16.size := by simp_bounds
@[simp, progress_post_simp] theorem IScalar.size_IScalarTyI32 : IScalar.size .I32 = I32.size := by simp_bounds
@[simp, progress_post_simp] theorem IScalar.size_IScalarTyI64 : IScalar.size .I64 = I64.size := by simp_bounds
@[simp, progress_post_simp] theorem IScalar.size_IScalarTyI128 : IScalar.size .I128 = I128.size := by simp_bounds
@[simp, progress_post_simp] theorem IScalar.size_IScalarTyIsize : IScalar.size .Isize = Isize.size := by simp_bounds

end Std

end Aeneas
