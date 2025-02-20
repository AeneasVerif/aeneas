import Aeneas.ScalarTac.ScalarTac
import Aeneas.Std.ScalarCore

namespace Aeneas

namespace Std

set_option maxRecDepth 1024

@[scalar_tac_simp] theorem UScalar.max_USize_eq : UScalar.max .Usize = Usize.max := by rfl
@[scalar_tac_simp] theorem IScalar.min_ISize_eq : IScalar.min .Isize = Isize.min := by rfl
@[scalar_tac_simp] theorem IScalar.max_ISize_eq : IScalar.max .Isize = Isize.max := by rfl

theorem Usize.max_succ_eq_pow : Usize.max + 1 = 2^System.Platform.numBits := by
  simp [Usize.max, Usize.numBits]
  have : 0 < 2^System.Platform.numBits := by simp
  omega

@[scalar_tac Usize.max]
theorem Usize.cMax_bound : UScalar.cMax .Usize ≤ Usize.max ∧ Usize.max + 1 = 2^System.Platform.numBits := by
  simp [Usize.max, UScalar.cMax, UScalar.rMax, U32.rMax, Usize.numBits]
  have := System.Platform.numBits_eq; cases this <;> simp [*]

abbrev Usize.maxAbbrevPow := 2^System.Platform.numBits
@[scalar_tac Usize.maxAbbrevPow]
theorem Usize.cMax_bound' : UScalar.cMax .Usize ≤ Usize.max ∧ Usize.max + 1 = 2^System.Platform.numBits := Usize.cMax_bound

@[scalar_tac Isize.min]
theorem Isize.cMin_bound : Isize.min ≤ IScalar.cMin .Isize ∧ Isize.min = - 2^(System.Platform.numBits - 1) := by
  simp [Isize.min, IScalar.cMin, IScalar.rMin, I32.rMin, Isize.numBits,
        Isize.max, IScalar.cMax, IScalar.rMax, I32.rMax]
  have := System.Platform.numBits_eq; cases this <;> simp [*]

abbrev Isize.minAbbrevPow :Int := -2^(System.Platform.numBits-1)
@[scalar_tac Isize.minAbbrevPow]
theorem Isize.cMin_bound' : Isize.min ≤ IScalar.cMin .Isize ∧ Isize.min = - 2^(System.Platform.numBits - 1) := Isize.cMin_bound

@[scalar_tac Isize.max]
theorem Isize.cMax_bound : IScalar.cMax .Isize ≤ Isize.max ∧ Isize.max + 1 = 2^(System.Platform.numBits - 1) := by
  simp [Isize.min, IScalar.cMin, IScalar.rMin, I32.rMin, Isize.numBits,
        Isize.max, IScalar.cMax, IScalar.rMax, I32.rMax]
  have := System.Platform.numBits_eq; cases this <;> simp [*]

abbrev Isize.maxAbbrevPow : Int := 2^(System.Platform.numBits-1)
@[scalar_tac Isize.maxAbbrevPow]
theorem Isize.cMax_bound' : IScalar.cMax .Isize ≤ Isize.max ∧ Isize.max + 1 = 2^(System.Platform.numBits - 1) := Isize.cMax_bound

@[scalar_tac_simp] theorem U8.numBits_eq    : U8.numBits = 8 := by rfl
@[scalar_tac_simp] theorem U16.numBits_eq   : U16.numBits = 16 := by rfl
@[scalar_tac_simp] theorem U32.numBits_eq   : U32.numBits = 32 := by rfl
@[scalar_tac_simp] theorem U64.numBits_eq   : U64.numBits = 64 := by rfl
@[scalar_tac_simp] theorem U128.numBits_eq  : U128.numBits = 128 := by rfl
@[scalar_tac_simp] theorem Usize.numBits_eq : Usize.numBits = System.Platform.numBits := by rfl

@[scalar_tac_simp] theorem I8.numBits_eq    : I8.numBits = 8 := by rfl
@[scalar_tac_simp] theorem I16.numBits_eq   : I16.numBits = 16 := by rfl
@[scalar_tac_simp] theorem I32.numBits_eq   : I32.numBits = 32 := by rfl
@[scalar_tac_simp] theorem I64.numBits_eq   : I64.numBits = 64 := by rfl
@[scalar_tac_simp] theorem I128.numBits_eq  : I128.numBits = 128 := by rfl
@[scalar_tac_simp] theorem Isize.numBits_eq : Isize.numBits = System.Platform.numBits := by rfl

@[scalar_tac_simp] theorem U8.max_eq    : U8.max = 255 := by rfl
@[scalar_tac_simp] theorem U16.max_eq   : U16.max = 65535 := by rfl
@[scalar_tac_simp] theorem U32.max_eq   : U32.max = 4294967295 := by rfl
@[scalar_tac_simp] theorem U64.max_eq   : U64.max = 18446744073709551615 := by rfl
@[scalar_tac_simp] theorem U128.max_eq  : U128.max = 340282366920938463463374607431768211455 := by rfl

@[scalar_tac_simp] theorem UScalar.max_U8_eq    : UScalar.max .U8 = 255 := by rfl
@[scalar_tac_simp] theorem UScalar.max_U16_eq   : UScalar.max .U16 = 65535 := by rfl
@[scalar_tac_simp] theorem UScalar.max_U32_eq   : UScalar.max .U32 = 4294967295 := by rfl
@[scalar_tac_simp] theorem UScalar.max_U64_eq   : UScalar.max .U64 = 18446744073709551615 := by rfl
@[scalar_tac_simp] theorem UScalar.max_U128_eq  : UScalar.max .U128 = 340282366920938463463374607431768211455 := by rfl

@[scalar_tac_simp] theorem I8.min_eq    : I8.min = -128 := by rfl
@[scalar_tac_simp] theorem I8.max_eq    : I8.max = 127 := by rfl
@[scalar_tac_simp] theorem I16.min_eq   : I16.min = -32768 := by rfl
@[scalar_tac_simp] theorem I16.max_eq   : I16.max = 32767 := by rfl
@[scalar_tac_simp] theorem I32.min_eq   : I32.min = -2147483648 := by rfl
@[scalar_tac_simp] theorem I32.max_eq   : I32.max = 2147483647 := by rfl
@[scalar_tac_simp] theorem I64.min_eq   : I64.min = -9223372036854775808 := by rfl
@[scalar_tac_simp] theorem I64.max_eq   : I64.max = 9223372036854775807 := by rfl
@[scalar_tac_simp] theorem I128.min_eq  : I128.min = -170141183460469231731687303715884105728 := by rfl
@[scalar_tac_simp] theorem I128.max_eq  : I128.max = 170141183460469231731687303715884105727 := by rfl

@[scalar_tac_simp] theorem IScalar.min_I8_eq    : IScalar.min .I8 = -128 := by rfl
@[scalar_tac_simp] theorem IScalar.max_I8_eq    : IScalar.max .I8 = 127 := by rfl
@[scalar_tac_simp] theorem IScalar.min_I16_eq   : IScalar.min .I16 = -32768 := by rfl
@[scalar_tac_simp] theorem IScalar.max_I16_eq   : IScalar.max .I16 = 32767 := by rfl
@[scalar_tac_simp] theorem IScalar.min_I32_eq   : IScalar.min .I32 = -2147483648 := by rfl
@[scalar_tac_simp] theorem IScalar.max_I32_eq   : IScalar.max .I32 = 2147483647 := by rfl
@[scalar_tac_simp] theorem IScalar.min_I64_eq   : IScalar.min .I64 = -9223372036854775808 := by rfl
@[scalar_tac_simp] theorem IScalar.max_I64_eq   : IScalar.max .I64 = 9223372036854775807 := by rfl
@[scalar_tac_simp] theorem IScalar.min_I128_eq  : IScalar.min .I128 = -170141183460469231731687303715884105728 := by rfl
@[scalar_tac_simp] theorem IScalar.max_I128_eq  : IScalar.max .I128 = 170141183460469231731687303715884105727 := by rfl

@[scalar_tac_simp] theorem U8.size_eq    : U8.size = 256 := by rfl
@[scalar_tac_simp] theorem U16.size_eq   : U16.size = 65536 := by rfl
@[scalar_tac_simp] theorem U32.size_eq   : U32.size = 4294967296 := by rfl
@[scalar_tac_simp] theorem U64.size_eq   : U64.size = 18446744073709551616 := by rfl
@[scalar_tac_simp] theorem U128.size_eq  : U128.size = 340282366920938463463374607431768211456 := by rfl

@[scalar_tac_simp] theorem I8.size_eq    : I8.size = 256 := by rfl
@[scalar_tac_simp] theorem I16.size_eq   : I16.size = 65536 := by rfl
@[scalar_tac_simp] theorem I32.size_eq   : I32.size = 4294967296 := by rfl
@[scalar_tac_simp] theorem I64.size_eq   : I64.size = 18446744073709551616 := by rfl
@[scalar_tac_simp] theorem I128.size_eq  : I128.size = 340282366920938463463374607431768211456 := by rfl

@[scalar_tac_simp] theorem UScalar.size_U8_eq    : UScalar.size .U8 = 256 := by rfl
@[scalar_tac_simp] theorem UScalar.size_U16_eq   : U16.size = 65536 := by rfl
@[scalar_tac_simp] theorem UScalar.size_U32_eq   : UScalar.size .U32 = 4294967296 := by rfl
@[scalar_tac_simp] theorem UScalar.size_U64_eq   : UScalar.size .U64 = 18446744073709551616 := by rfl
@[scalar_tac_simp] theorem UScalar.size_U128_eq  : UScalar.size .U128 = 340282366920938463463374607431768211456 := by rfl

@[scalar_tac_simp] theorem IScalar.size_I8_eq    : IScalar.size .I8 = 256 := by rfl
@[scalar_tac_simp] theorem IScalar.size_I16_eq   : IScalar.size .I16 = 65536 := by rfl
@[scalar_tac_simp] theorem IScalar.size_I32_eq   : IScalar.size .I32 = 4294967296 := by rfl
@[scalar_tac_simp] theorem IScalar.size_I64_eq   : IScalar.size .I64 = 18446744073709551616 := by rfl
@[scalar_tac_simp] theorem IScalar.size_I128_eq  : IScalar.size .I128 = 340282366920938463463374607431768211456 := by rfl

@[scalar_tac_simp] theorem UScalar.cMax_U8_eq     : UScalar.cMax .U8 = 255 := by rfl
@[scalar_tac_simp] theorem UScalar.cMax_U16_eq    : UScalar.cMax .U16 = 65535 := by rfl
@[scalar_tac_simp] theorem UScalar.cMax_U32_eq    : UScalar.cMax .U32 = 4294967295 := by rfl
@[scalar_tac_simp] theorem UScalar.cMax_U64_eq    : UScalar.cMax .U64 = 18446744073709551615 := by rfl
@[scalar_tac_simp] theorem UScalar.cMax_U128_eq   : UScalar.cMax .U128 = 340282366920938463463374607431768211455 := by rfl
@[scalar_tac_simp] theorem UScalar.cMax_Usize_eq  : UScalar.cMax .Usize = 4294967295 := by rfl

@[scalar_tac_simp] theorem IScalar.cMin_I8_eq     : IScalar.cMin .I8 = -128 := by rfl
@[scalar_tac_simp] theorem IScalar.cMax_I8_eq     : IScalar.cMax .I8 = 127 := by rfl
@[scalar_tac_simp] theorem IScalar.cMin_I16_eq    : IScalar.cMin .I16 = -32768 := by rfl
@[scalar_tac_simp] theorem IScalar.cMax_I16_eq    : IScalar.cMax .I16 = 32767 := by rfl
@[scalar_tac_simp] theorem IScalar.cMin_I32_eq    : IScalar.cMin .I32 = -2147483648 := by rfl
@[scalar_tac_simp] theorem IScalar.cMax_I32_eq    : IScalar.cMax .I32 = 2147483647 := by rfl
@[scalar_tac_simp] theorem IScalar.cMin_I64_eq    : IScalar.cMin .I64 = -9223372036854775808 := by rfl
@[scalar_tac_simp] theorem IScalar.cMax_I64_eq    : IScalar.cMax .I64 = 9223372036854775807 := by rfl
@[scalar_tac_simp] theorem IScalar.cMin_I128_eq   : IScalar.cMin .I128 = -170141183460469231731687303715884105728 := by rfl
@[scalar_tac_simp] theorem IScalar.cMax_I128_eq   : IScalar.cMax .I128 = 170141183460469231731687303715884105727 := by rfl
@[scalar_tac_simp] theorem IScalar.cMin_Isize_eq  : IScalar.cMin .Isize = -2147483648 := by rfl
@[scalar_tac_simp] theorem IScalar.cMax_Isize_eq  : IScalar.cMax .Isize = 2147483647 := by rfl


@[scalar_tac_simp]
theorem UScalarTy.USize.numBits_eq : UScalarTy.Usize.numBits = System.Platform.numBits := by rfl

@[scalar_tac_simp]
theorem IScalarTy.ISize.numBits_eq : IScalarTy.Isize.numBits = System.Platform.numBits := by rfl

attribute [scalar_tac_simp] Bool.toNat_false Bool.toNat_true

end Std

namespace ScalarTac

open Std

@[scalar_tac x]
theorem UScalar.bounds {ty : UScalarTy} (x : UScalar ty) :
  x.val ≤ UScalar.max ty := by
  simp [UScalar.max]
  have := x.hBounds
  omega

@[scalar_tac x]
theorem IScalar.bounds {ty : IScalarTy} (x : IScalar ty) :
  IScalar.min ty ≤ x.val ∧ x.val ≤ IScalar.max ty := by
  simp [IScalar.max, IScalar.min]
  have := x.hBounds
  omega

/-!
# Tests and Additional Simp Theorems
-/

example (x _y : U32) : x.val ≤ UScalar.max .U32 := by
  scalar_tac_preprocess
  simp [*]

example (x _y : U32) : x.val ≤ UScalar.max .U32 := by
  scalar_tac

-- Checking that we explore the goal *and* projectors correctly
example (x : U32 × U32) : 0 ≤ x.fst.val := by
  scalar_tac

-- Checking that we properly handle [ofInt]
example : (U32.ofNat 1).val ≤ U32.max := by
  scalar_tac

example (x : Nat) (h1 : x ≤ U32.max) :
  (U32.ofNat x (by scalar_tac)).val ≤ U32.max := by
  scalar_tac_preprocess
  scalar_tac

-- Not equal
example (x : U32) (h0 : ¬ x = U32.ofNat 0) : 0 < x.val := by
  scalar_tac

/- See this: https://aeneas-verif.zulipchat.com/#narrow/stream/349819-general/topic/U64.20trouble/near/444049757

   We solved it by removing the instance `OfNat` for `Scalar`.
   Note however that we could also solve it with a simplification lemma.
   However, after testing, we noticed we could only apply such a lemma with
   the rewriting tactic (not the simplifier), probably because of the use
   of typeclasses. -/
example {u: U64} (h1: (u : Nat) < 2): (u : Nat) = 0 ∨ (u : Nat) = 1 := by
  scalar_tac

example (x : I32) : -100000000000 < x.val := by
  scalar_tac

example : (Usize.ofNat 2).val ≠ 0 := by
  scalar_tac

example (x : U32) : x.val ≤ Usize.max := by scalar_tac
example (x : I32) : x.val ≤ Isize.max := by scalar_tac
example (x : I32) : Isize.min ≤ x.val := by scalar_tac

example (x y : Nat) (z : Int) (h : Int.subNatNat x y + z = 0) : (x : Int) - (y : Int) + z = 0 := by
  scalar_tac_preprocess
  omega

example (x : U32) (h : 16 * x.val ≤ U32.max) :
  4 * (U32.ofNat (4 * x.val) (by scalar_tac)).val ≤ U32.max := by
  scalar_tac

example (b : Bool) (x y : Int) (h : if b then P ∧ x + y < 3 else x + y < 4) : x + y < 5 := by
  scalar_tac +split

open Utils

/- Some tests which introduce big constants (those sometimes cause issues when reducing expressions).

   See for instance: https://github.com/leanprover/lean4/issues/6955
 -/
example (x y : Nat) (h : x = y + 2^32) : 0 ≤ x := by
  scalar_tac

example (x y : Nat) (h : x = y - 2^32) : 0 ≤ x := by
  scalar_tac

example
  (xi yi : U32)
  (c0 : U8)
  (hCarryLe : c0.val ≤ 1)
  (c0u : U32)
  (_ : c0u.val = c0.val)
  (s1 : U32)
  (c1 : Bool)
  (hConv1 : if xi.val + c0u.val > U32.max then s1.val = ↑xi + ↑c0u - U32.max - 1 ∧ c1 = true else s1 = xi.val + c0u ∧ c1 = false)
  (s2 : U32)
  (c2 : Bool)
  (hConv2 : if s1.val + yi.val > U32.max then s2.val = ↑s1 + ↑yi - U32.max - 1 ∧ c2 = true else s2 = s1.val + yi ∧ c2 = false)
  (c1u : U8)
  (_ : c1u.val = if c1 = true then 1 else 0)
  (c2u : U8)
  (_ : c2u.val = if c2 = true then 1 else 0)
  (c3 : U8)
  (_ : c3.val = c1u.val + c2u.val):
  c3.val ≤ 1 := by
  scalar_tac +split

example (x y : Nat) (h : x = y - 2^32) : 0 ≤ x := by
  scalar_tac

example (v : { l : List α // l.length ≤ Usize.max }) :
  v.val.length < 2 ^ UScalarTy.Usize.numBits := by
  scalar_tac

example (i : I8) : - 2^(Isize.numBits - 1) ≤ i.val ∧ i.val ≤ 2^(Isize.numBits - 1) := by scalar_tac
example (x : I8) : -2 ^ (System.Platform.numBits - 1) ≤ x.val := by scalar_tac

example
  (α : Type u)
  (v : { l : List α // l.length ≤ Usize.max })
  (nlen : ℕ)
  (h : nlen ≤ U32.max ∨ nlen ≤ 2 ^ Usize.numBits - 1) :
  nlen ≤ 2 ^ Usize.numBits - 1
  := by
  scalar_tac

example
  (α : Type u)
  (v : { l : List α // l.length ≤ Usize.max })
  (nlen : ℕ)
  (h : (decide (nlen ≤ U32.max) || decide (nlen ≤ Usize.max)) = true) :
  nlen ≤ Usize.max
  := by
  scalar_tac

example (x : I8) : x.toNat = x.val.toNat := by scalar_tac

/-!
## Min, Max
-/

@[scalar_tac_simp] theorem Nat.max_eq_Max_max (x y : Nat) : Nat.max x y = x ⊔ y := by simp
@[scalar_tac_simp] theorem Nat.min_eq_Min_min (x y : Nat) : Nat.min x y = x ⊓ y := by simp

example (x y : Nat) : x ≤ x ⊔ y := by scalar_tac
example (x y : Nat) : x ≤ Nat.max x y := by scalar_tac
example (x y : Nat) : x ⊓ y ≤ x := by scalar_tac
example (x y : Nat) : Nat.min x y ≤ x := by scalar_tac

example (x y : Int) : x ≤ x ⊔ y := by scalar_tac
example (x y : Int) : x ≤ max x y := by scalar_tac
example (x y : Int) : x ⊓ y ≤ x := by scalar_tac
example (x y : Int) : min x y ≤ x := by scalar_tac

/-!
## Abs
-/

@[scalar_tac_simp]
theorem Int.natAbs_eq_abs (x : Int) : |x| = ↑x.natAbs := by simp

example (x y : Int) (h : x.natAbs ≤ y.natAbs) : x ≤ y.natAbs := by
  scalar_tac_preprocess

  scalar_tac
example (x y : Int) (h : |x| ≤ |y|) : x ≤ |y| := by scalar_tac
example (x y : Int) (h : |x| ≤ |y|) : x ≤ |y| := by scalar_tac

end ScalarTac

end Aeneas
