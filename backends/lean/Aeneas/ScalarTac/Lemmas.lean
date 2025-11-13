import Mathlib.Data.ZMod.Basic
import Aeneas.ScalarTac.ScalarTac
import Aeneas.Std.Scalar.Core
import Aeneas.ReduceZMod.ReduceZMod

namespace Aeneas

namespace Std

open ScalarTac

set_option maxRecDepth 1024

instance (x y : UScalar ty) : IsLinearIntProp (x < y) where
instance (x y : UScalar ty) : IsLinearIntProp (x > y) where
instance (x y : UScalar ty) : IsLinearIntProp (x ≤ y) where
instance (x y : UScalar ty) : IsLinearIntProp (x ≥ y) where
instance (x y : UScalar ty) : IsLinearIntProp (x ≥ y) where
instance (x y : UScalar ty) : IsLinearIntProp (x = y) where

instance (x y : IScalar ty) : IsLinearIntProp (x < y) where
instance (x y : IScalar ty) : IsLinearIntProp (x > y) where
instance (x y : IScalar ty) : IsLinearIntProp (x ≤ y) where
instance (x y : IScalar ty) : IsLinearIntProp (x ≥ y) where
instance (x y : IScalar ty) : IsLinearIntProp (x ≥ y) where
instance (x y : IScalar ty) : IsLinearIntProp (x = y) where

attribute [scalar_tac_simps] Prod.mk.injEq Membership.mem Int.ofNat_toNat zero_add bne_iff_ne

local syntax "simp_scalar_consts" : tactic
local macro_rules
| `(tactic|simp_scalar_consts) =>
  `(tactic|
      simp [
      UScalar.rMax, UScalar.max,
      Usize.rMax, Usize.rMax, Usize.max,
      U8.rMax, U8.max, U16.rMax, U16.max, U32.rMax, U32.max,
      U64.rMax, U64.max, U128.rMax, U128.max,
      U8.numBits, U16.numBits, U32.numBits, U64.numBits, U128.numBits, Usize.numBits,
      U8.size, U16.size, U32.size, U64.size, U128.size, Usize.size,
      IScalar.rMax, IScalar.max,
      IScalar.rMin, IScalar.min,
      Isize.rMax, Isize.rMax, Isize.max,
      I8.rMax, I8.max, I16.rMax, I16.max, I32.rMax, I32.max,
      I64.rMax, I64.max, I128.rMax, I128.max,
      Isize.rMin, Isize.rMin, Isize.min,
      I8.rMin, I8.min, I16.rMin, I16.min, I32.rMin, I32.min,
      I64.rMin, I64.min, I128.rMin, I128.min,
      I8.numBits, I16.numBits, I32.numBits, I64.numBits, I128.numBits, Isize.numBits,
      I8.size, I16.size, I32.size, I64.size, I128.size, Isize.size,
      UScalar.size, IScalar.size,
      UScalar.cMax, IScalar.cMin, IScalar.cMax])

@[scalar_tac_simps] theorem UScalar.max_USize_eq : UScalar.max .Usize = Usize.max := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.min_ISize_eq : IScalar.min .Isize = Isize.min := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.max_ISize_eq : IScalar.max .Isize = Isize.max := by simp_scalar_consts

theorem Usize.max_succ_eq_pow : Usize.max + 1 = 2^System.Platform.numBits := by
  simp [Usize.max, Usize.numBits]
  have : 0 < 2^System.Platform.numBits := by simp
  omega

@[scalar_tac Usize.max]
theorem Usize.cMax_bound : UScalar.cMax .Usize ≤ Usize.max ∧ Usize.max + 1 = 2^System.Platform.numBits := by
  simp [Usize.max, UScalar.cMax, UScalar.rMax, U32.rMax, Usize.numBits]
  have := System.Platform.numBits_eq; cases this <;> simp [*]

@[scalar_tac Usize.size]
theorem Usize.size_scalarTac_eq : Usize.size = Usize.max + 1 ∧ Usize.size = 2^System.Platform.numBits := by
  simp [Usize.max, Usize.numBits, Usize.size]
  have := System.Platform.numBits_eq; cases this <;> simp [*]

abbrev Usize.maxAbbrevPow := 2^System.Platform.numBits
@[scalar_tac Usize.maxAbbrevPow]
theorem Usize.cMax_bound' : UScalar.cMax .Usize ≤ Usize.max ∧ Usize.max + 1 = 2^System.Platform.numBits := Usize.cMax_bound

abbrev Usize.maxAbbrevPow' := 2^Usize.numBits
@[scalar_tac Usize.maxAbbrevPow']
theorem Usize.cMax_bound'' : UScalar.cMax .Usize ≤ Usize.max ∧ Usize.max + 1 = 2^System.Platform.numBits := Usize.cMax_bound

@[scalar_tac Isize.min]
theorem Isize.cMin_bound : Isize.min ≤ IScalar.cMin .Isize ∧ Isize.min = - 2^(System.Platform.numBits - 1) := by
  simp [Isize.min, IScalar.cMin, IScalar.rMin, I32.rMin, Isize.numBits]
  have := System.Platform.numBits_eq; cases this <;> simp [*]

abbrev Isize.minAbbrevPow :Int := -2^(System.Platform.numBits-1)
@[scalar_tac Isize.minAbbrevPow]
theorem Isize.cMin_bound' : Isize.min ≤ IScalar.cMin .Isize ∧ Isize.min = - 2^(System.Platform.numBits - 1) := Isize.cMin_bound

abbrev Isize.minAbbrevPow' :Int := -2^(Isize.numBits-1)
@[scalar_tac Isize.minAbbrevPow']
theorem Isize.cMin_bound'' : Isize.min ≤ IScalar.cMin .Isize ∧ Isize.min = - 2^(System.Platform.numBits - 1) := Isize.cMin_bound

@[scalar_tac Isize.max]
theorem Isize.cMax_bound : IScalar.cMax .Isize ≤ Isize.max ∧ Isize.max + 1 = 2^(System.Platform.numBits - 1) := by
  simp [Isize.numBits, Isize.max, IScalar.cMax, IScalar.rMax, I32.rMax]
  have := System.Platform.numBits_eq; cases this <;> simp [*]

@[scalar_tac Usize.size]
theorem Isize.size_scalarTac_eq : Isize.size = 2^System.Platform.numBits := by
  simp [Isize.numBits, Isize.size]

abbrev Isize.maxAbbrevPow : Int := 2^(System.Platform.numBits-1)
@[scalar_tac Isize.maxAbbrevPow]
theorem Isize.cMax_bound' : IScalar.cMax .Isize ≤ Isize.max ∧ Isize.max + 1 = 2^(System.Platform.numBits - 1) := Isize.cMax_bound

abbrev Isize.maxAbbrevPow' : Int := 2^(Isize.numBits-1)
@[scalar_tac Isize.maxAbbrevPow']
theorem Isize.cMax_bound'' : IScalar.cMax .Isize ≤ Isize.max ∧ Isize.max + 1 = 2^(System.Platform.numBits - 1) := Isize.cMax_bound

@[scalar_tac_simps] theorem U8.numBits_eq    : U8.numBits = 8 := by simp_scalar_consts
@[scalar_tac_simps] theorem U16.numBits_eq   : U16.numBits = 16 := by simp_scalar_consts
@[scalar_tac_simps] theorem U32.numBits_eq   : U32.numBits = 32 := by simp_scalar_consts
@[scalar_tac_simps] theorem U64.numBits_eq   : U64.numBits = 64 := by simp_scalar_consts
@[scalar_tac_simps] theorem U128.numBits_eq  : U128.numBits = 128 := by simp_scalar_consts
@[scalar_tac_simps] theorem Usize.numBits_eq : Usize.numBits = System.Platform.numBits := by simp_scalar_consts

@[scalar_tac_simps] theorem I8.numBits_eq    : I8.numBits = 8 := by simp_scalar_consts
@[scalar_tac_simps] theorem I16.numBits_eq   : I16.numBits = 16 := by simp_scalar_consts
@[scalar_tac_simps] theorem I32.numBits_eq   : I32.numBits = 32 := by simp_scalar_consts
@[scalar_tac_simps] theorem I64.numBits_eq   : I64.numBits = 64 := by simp_scalar_consts
@[scalar_tac_simps] theorem I128.numBits_eq  : I128.numBits = 128 := by simp_scalar_consts
@[scalar_tac_simps] theorem Isize.numBits_eq : Isize.numBits = System.Platform.numBits := by simp_scalar_consts

@[scalar_tac_simps] theorem U8.max_eq    : U8.max = 255 := by simp_scalar_consts
@[scalar_tac_simps] theorem U16.max_eq   : U16.max = 65535 := by simp_scalar_consts
@[scalar_tac_simps] theorem U32.max_eq   : U32.max = 4294967295 := by simp_scalar_consts
@[scalar_tac_simps] theorem U64.max_eq   : U64.max = 18446744073709551615 := by simp_scalar_consts
@[scalar_tac_simps] theorem U128.max_eq  : U128.max = 340282366920938463463374607431768211455 := by simp_scalar_consts

@[scalar_tac_simps] theorem UScalar.max_U8_eq    : UScalar.max .U8 = 255 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.max_U16_eq   : UScalar.max .U16 = 65535 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.max_U32_eq   : UScalar.max .U32 = 4294967295 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.max_U64_eq   : UScalar.max .U64 = 18446744073709551615 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.max_U128_eq  : UScalar.max .U128 = 340282366920938463463374607431768211455 := by simp_scalar_consts

@[scalar_tac_simps] theorem I8.min_eq    : I8.min = -128 := by simp_scalar_consts
@[scalar_tac_simps] theorem I8.max_eq    : I8.max = 127 := by simp_scalar_consts
@[scalar_tac_simps] theorem I16.min_eq   : I16.min = -32768 := by simp_scalar_consts
@[scalar_tac_simps] theorem I16.max_eq   : I16.max = 32767 := by simp_scalar_consts
@[scalar_tac_simps] theorem I32.min_eq   : I32.min = -2147483648 := by simp_scalar_consts
@[scalar_tac_simps] theorem I32.max_eq   : I32.max = 2147483647 := by simp_scalar_consts
@[scalar_tac_simps] theorem I64.min_eq   : I64.min = -9223372036854775808 := by simp_scalar_consts
@[scalar_tac_simps] theorem I64.max_eq   : I64.max = 9223372036854775807 := by simp_scalar_consts
@[scalar_tac_simps] theorem I128.min_eq  : I128.min = -170141183460469231731687303715884105728 := by simp_scalar_consts
@[scalar_tac_simps] theorem I128.max_eq  : I128.max = 170141183460469231731687303715884105727 := by simp_scalar_consts

@[scalar_tac_simps] theorem IScalar.min_I8_eq    : IScalar.min .I8 = -128 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.max_I8_eq    : IScalar.max .I8 = 127 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.min_I16_eq   : IScalar.min .I16 = -32768 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.max_I16_eq   : IScalar.max .I16 = 32767 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.min_I32_eq   : IScalar.min .I32 = -2147483648 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.max_I32_eq   : IScalar.max .I32 = 2147483647 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.min_I64_eq   : IScalar.min .I64 = -9223372036854775808 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.max_I64_eq   : IScalar.max .I64 = 9223372036854775807 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.min_I128_eq  : IScalar.min .I128 = -170141183460469231731687303715884105728 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.max_I128_eq  : IScalar.max .I128 = 170141183460469231731687303715884105727 := by simp_scalar_consts

@[scalar_tac_simps] theorem U8.size_eq    : U8.size = 256 := by simp_scalar_consts
@[scalar_tac_simps] theorem U16.size_eq   : U16.size = 65536 := by simp_scalar_consts
@[scalar_tac_simps] theorem U32.size_eq   : U32.size = 4294967296 := by simp_scalar_consts
@[scalar_tac_simps] theorem U64.size_eq   : U64.size = 18446744073709551616 := by simp_scalar_consts
@[scalar_tac_simps] theorem U128.size_eq  : U128.size = 340282366920938463463374607431768211456 := by simp_scalar_consts

@[scalar_tac_simps] theorem I8.size_eq    : I8.size = 256 := by simp_scalar_consts
@[scalar_tac_simps] theorem I16.size_eq   : I16.size = 65536 := by simp_scalar_consts
@[scalar_tac_simps] theorem I32.size_eq   : I32.size = 4294967296 := by simp_scalar_consts
@[scalar_tac_simps] theorem I64.size_eq   : I64.size = 18446744073709551616 := by simp_scalar_consts
@[scalar_tac_simps] theorem I128.size_eq  : I128.size = 340282366920938463463374607431768211456 := by simp_scalar_consts

@[scalar_tac_simps] theorem UScalar.size_U8_eq    : UScalar.size .U8 = 256 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.size_U16_eq   : U16.size = 65536 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.size_U32_eq   : UScalar.size .U32 = 4294967296 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.size_U64_eq   : UScalar.size .U64 = 18446744073709551616 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.size_U128_eq  : UScalar.size .U128 = 340282366920938463463374607431768211456 := by simp_scalar_consts

@[scalar_tac_simps] theorem IScalar.size_I8_eq    : IScalar.size .I8 = 256 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.size_I16_eq   : IScalar.size .I16 = 65536 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.size_I32_eq   : IScalar.size .I32 = 4294967296 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.size_I64_eq   : IScalar.size .I64 = 18446744073709551616 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.size_I128_eq  : IScalar.size .I128 = 340282366920938463463374607431768211456 := by simp_scalar_consts

@[scalar_tac_simps] theorem UScalar.cMax_U8_eq     : UScalar.cMax .U8 = 255 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.cMax_U16_eq    : UScalar.cMax .U16 = 65535 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.cMax_U32_eq    : UScalar.cMax .U32 = 4294967295 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.cMax_U64_eq    : UScalar.cMax .U64 = 18446744073709551615 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.cMax_U128_eq   : UScalar.cMax .U128 = 340282366920938463463374607431768211455 := by simp_scalar_consts
@[scalar_tac_simps] theorem UScalar.cMax_Usize_eq  : UScalar.cMax .Usize = 4294967295 := by simp_scalar_consts

@[scalar_tac_simps] theorem IScalar.cMin_I8_eq     : IScalar.cMin .I8 = -128 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMax_I8_eq     : IScalar.cMax .I8 = 127 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMin_I16_eq    : IScalar.cMin .I16 = -32768 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMax_I16_eq    : IScalar.cMax .I16 = 32767 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMin_I32_eq    : IScalar.cMin .I32 = -2147483648 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMax_I32_eq    : IScalar.cMax .I32 = 2147483647 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMin_I64_eq    : IScalar.cMin .I64 = -9223372036854775808 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMax_I64_eq    : IScalar.cMax .I64 = 9223372036854775807 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMin_I128_eq   : IScalar.cMin .I128 = -170141183460469231731687303715884105728 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMax_I128_eq   : IScalar.cMax .I128 = 170141183460469231731687303715884105727 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMin_Isize_eq  : IScalar.cMin .Isize = -2147483648 := by simp_scalar_consts
@[scalar_tac_simps] theorem IScalar.cMax_Isize_eq  : IScalar.cMax .Isize = 2147483647 := by simp_scalar_consts

@[scalar_tac_simps]
theorem UScalarTy.USize.numBits_eq : UScalarTy.Usize.numBits = System.Platform.numBits := by simp_scalar_consts

@[scalar_tac_simps]
theorem IScalarTy.ISize.numBits_eq : IScalarTy.Isize.numBits = System.Platform.numBits := by simp_scalar_consts

attribute [scalar_tac_simps] Bool.toNat_false Bool.toNat_true

end Std

namespace ScalarTac

open Std

attribute [scalar_tac_simps] Prod.mk.injEq gt_iff_lt

attribute [scalar_tac_simps]
  -- Int.subNatNat is very annoying - TODO: there is probably something more general thing to do
  Int.subNatNat_eq_coe

@[scalar_tac x.val]
theorem UScalar.bounds {ty : UScalarTy} (x : UScalar ty) :
  x.val ≤ UScalar.max ty := by
  simp [UScalar.max]
  have := x.hBounds
  omega

@[scalar_tac x.val]
theorem IScalar.bounds {ty : IScalarTy} (x : IScalar ty) :
  IScalar.min ty ≤ x.val ∧ x.val ≤ IScalar.max ty := by
  simp [IScalar.max, IScalar.min]
  have := x.hBounds
  omega

attribute [scalar_tac a.toNat] Int.toNat_eq_max

/-!
# Neq
-/

/- We use this because several scalar_tac patterns are triggered by a precondition of the shape `a < b`. -/
@[scalar_tac_simps]
theorem Nat_neq_zero_iff (x : ℕ) : x ≠ 0 ↔ 0 < x := by omega

attribute [scalar_tac_simps] Nat.not_eq Int.not_eq

/-!
# Casts
-/

attribute [scalar_tac_simps, simp_scalar_simps] Nat.cast_add Nat.cast_mul Nat.cast_ofNat
attribute [scalar_tac_simps, simp_lists_hyps_simps, simp_scalar_hyps_simps] Int.cast_subNatNat

/-!
# Min, Max
-/

@[scalar_tac_simps] theorem Nat.max_eq_Max_max (x y : Nat) : Nat.max x y = x ⊔ y := by simp
@[scalar_tac_simps] theorem Nat.min_eq_Min_min (x y : Nat) : Nat.min x y = x ⊓ y := by simp

example (x y : Nat) : x ≤ x ⊔ y := by scalar_tac
example (x y : Nat) : x ≤ Nat.max x y := by scalar_tac
example (x y : Nat) : x ⊓ y ≤ x := by scalar_tac
example (x y : Nat) : Nat.min x y ≤ x := by scalar_tac

example (x y : Int) : x ≤ x ⊔ y := by scalar_tac
example (x y : Int) : x ≤ max x y := by scalar_tac
example (x y : Int) : x ⊓ y ≤ x := by scalar_tac
example (x y : Int) : min x y ≤ x := by scalar_tac

/-!
# Abs
-/

@[scalar_tac_simps]
theorem Int.natAbs_eq_abs (x : Int) : |x| = ↑x.natAbs := by simp

example (x y z : Int) (h0 : x.natAbs ≤ y.natAbs) (h1 : y.natAbs ≤ z.natAbs) : x ≤ z.natAbs := by
  scalar_tac
example (x y : Int) (h : |x| ≤ |y|) : x ≤ |y| := by scalar_tac
example (x y : Int) (h : |x| ≤ |y|) : x ≤ |y| := by scalar_tac

/-!
# Forward Saturation
-/

section
/-!
The example below fails if the simp which happens *before* the saturation uses `scalar_tac_simps` instead
of `scalar_tac_before_sat_simps`.
-/

private def c : Nat := 100

@[local scalar_tac x * c]
private theorem mul_c (x : Nat) : x * c ≤ 100 * x := by simp [c]; omega

example (x : Nat) : x * c ≤ 100 * x := by scalar_tac_preprocess

end

/-!
# ZMod
-/
@[scalar_tac x.val]
theorem ZMod.val_lt_or {n} (x : ZMod n) : x.val < n ∨ n = 0 := by
  by_cases hn : n = 0
  . simp [*]
  . have := @ZMod.val_lt n (by constructor; omega) x
    omega

@[simp_scalar_simps]
theorem ZMod.val_lt_iff {n} (x : ZMod n) : x.val < n ↔ n ≠ 0 := by
 scalar_tac

attribute [simp_scalar_simps] ZMod.val_natCast ZMod.val_intCast

@[simp, simp_scalar_simps]
theorem ZMod.cast_intCast {n : ℕ} (a : ℤ) [NeZero n] : ((a : ZMod n).cast : ℤ) = a % ↑n := by
  simp only [ZMod.cast_eq_val, ZMod.val_intCast]

attribute [scalar_tac_simps, simp_scalar_simps] ReduceZMod.reduceZMod

/-!
# Sets
-/
attribute [scalar_tac_simps] Set.Mem

@[scalar_tac_simps] theorem Set.mem_insert_nat s x y :
  @insert ℕ (Set ℕ) Set.instInsert x s y ↔ y = x ∨ s y := by rfl

@[scalar_tac_simps] theorem Set.mem_singleton_nat x y :
  @singleton ℕ (Set ℕ) Set.instSingletonSet x y ↔ y = x := by rfl

@[scalar_tac_simps] theorem Set.mem_insert_int s x y :
  @insert ℤ (Set ℤ) Set.instInsert x s y ↔ y = x ∨ s y := by rfl

@[scalar_tac_simps] theorem Set.mem_singleton_int x y :
  @singleton ℤ (Set ℤ) Set.instSingletonSet x y ↔ y = x := by rfl

/-!
# Subtypes
-/
@[scalar_tac x.val]
theorem subtype_property {α : Sort u} (p : α → Prop) (x : Subtype p) : p x.val := by
  cases x; trivial

@[scalar_tac_simps]
theorem nat_subset_le_iff (p : ℕ → Prop) (x y : {n : ℕ // p n}) : x ≤ y ↔ x.val ≤ y.val := by rfl

@[scalar_tac_simps]
theorem nat_subset_lt_iff (p : ℕ → Prop) (x y : {n : ℕ // p n}) : x < y ↔ x.val < y.val := by rfl

@[scalar_tac_simps]
theorem nat_subset_eq_iff (p : ℕ → Prop) (x y : {n : ℕ // p n}) : x = y ↔ x.val = y.val := by
  cases x; cases y; simp

/-!
# Multiplication
-/
@[scalar_tac x * y]
theorem lt_mul_lt_le (x y a b : ℕ) (h0 : x < a) (h1 : y < b) :
  x * y ≤ (a - 1) * (b - 1) := by apply Nat.le_mul_le; omega

@[scalar_tac x * y]
theorem le_mul_lt_le (x y a b : ℕ) (h0 : x ≤ a) (h1 : y < b) :
  x * y ≤ a * (b - 1) := by apply Nat.le_mul_le; omega

@[scalar_tac x * y]
theorem lt_mul_le_le (x y a b : ℕ) (h0 : x < a) (h1 : y ≤ b) :
  x * y ≤ (a - 1) * b := by apply Nat.le_mul_le; omega

@[scalar_tac x * y]
theorem le_mul_le_le (x y a b : ℕ) (h0 : x ≤ a) (h1 : y ≤ b) :
  x * y ≤ a * b := by apply Nat.le_mul_le; omega

/-!
Not activating those lemmas for now, because there are a lot of them
and it leads to performance issues.
TODO: experiment with lemmas for non linear goals.
-/

--@[scalar_tac_nonlin a * b]
theorem lt_mul_lt_le' (x y a b : ℕ) (h0 : x < a) (h1 : y < b) :
  (x + 1) * (y + 1) ≤ a * b := by apply Nat.le_mul_le; omega

--@[scalar_tac_nonlin a * b]
theorem le_mul_lt_le' (x y a b : ℕ) (h0 : x ≤ a) (h1 : y < b) :
  x * (y + 1) ≤ a * b := by apply Nat.le_mul_le; omega

--@[scalar_tac_nonlin a * b]
theorem lt_mul_le_le' (x y a b : ℕ) (h0 : x < a) (h1 : y ≤ b) :
  (x + 1) * y ≤ a * b := by apply Nat.le_mul_le; omega

--@[scalar_tac_nonlin a * b]
theorem le_mul_le_le' (x y a b : ℕ) (h0 : x ≤ a) (h1 : y ≤ b) :
  x * y ≤ a * b := by apply Nat.le_mul_le; omega

--@[scalar_tac_nonlin x * y]
theorem lt_mul_le_left (x y a : ℕ) (h0 : x < a) :
  x * y ≤ (a - 1) * y := by apply Nat.le_mul_le; omega

--@[scalar_tac_nonlin x * b]
theorem lt_mul_lt_left (x a b : ℕ) (h0 : x < a) :
  x * b + b ≤ a * b := by
  calc
    x * b + b = (x + 1) * b := by ring_nf
    _ ≤ a * b := by apply Nat.le_mul_le; omega

--@[scalar_tac_nonlin x * y]
theorem lt_mul_le_right (x y a : ℕ) (h0 : y < a) :
  x * y ≤ x * (a - 1) := by apply Nat.le_mul_le; omega

--@[scalar_tac_nonlin a * y]
theorem lt_mul_lt_right (y a b : ℕ) (h0 : y < b) :
  a * y + a ≤ a * b := by
  calc
    a * y + a = a * (y + 1) := by ring_nf
    _ ≤ a * b := by apply Nat.le_mul_le; omega

--@[scalar_tac_nonlin x * y]
theorem le_mul_le_left (x y a : ℕ) (h0 : x ≤ a) :
  x * y ≤ a * y := by apply Nat.le_mul_le; omega

--@[scalar_tac_nonlin x * y]
theorem le_mul_le_right (x y a : ℕ) (h0 : y ≤ a) :
  x * y ≤ x * a := by apply Nat.le_mul_le; omega

/-
example (i j n1 n2 : ℕ)
  (hi : i < n1)
  (hj : j < n2) :
  i * n2 + j < n1 * n2
  := by
  scalar_tac +nonLin

example (i j n1 n2 : ℕ)
  (hi : i < n1)
  (hj : j < n2) :
  n1 * j + i < n1 * n2
  := by
  scalar_tac +nonLin
-/

/-!
# Modulo
-/
@[scalar_tac x % y]
theorem mod_lt (x y : ℕ) (h : 0 < y) : x % y < y := by exact Nat.mod_lt x h

/-!
# Size
-/

/- Remark: we're omitting a similar theorem for `IScalar` because the theorem is a bit cumbersome
   to use (it has to be expressed in terms of `x.bv.toNat`). -/
@[scalar_tac_simps]
theorem UScalar.sizeOf {ty} (x : UScalar ty) : sizeOf x = x.val + 3 := by
  cases x; simp only [UScalar.mk.sizeOf_spec, BitVec.sizeOf, Fin.sizeOf, BitVec.val_toFin]
  unfold UScalar.val
  simp only
  omega

end ScalarTac

end Aeneas
