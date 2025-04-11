import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.ScalarTac
import Aeneas.Std.Core
import Mathlib.Data.BitVec
import Mathlib.Data.Int.Init

namespace Aeneas.Std

open Result Error Arith

/-!
# Multiplication: Definitions
-/

def UScalar.mul {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.val * y.val)

def IScalar.mul {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.val * y.val)

def UScalar.try_mul {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (mul x y)

def IScalar.try_mul {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (mul x y)

instance {ty} : HMul (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hMul x y := UScalar.mul x y

instance {ty} : HMul (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hMul x y := IScalar.mul x y

/-!
# Multiplication: Theorems
-/

/-!
Theorems with a specification which use integers and bit-vectors
-/

theorem UScalar.mul_equiv {ty} (x y : UScalar ty) :
  match mul x y with
  | ok z => x.val * y.val ≤ UScalar.max ty ∧ (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv
  | fail _ => UScalar.max ty < x.val * y.val
  | .div => False := by
  simp [mul]
  have := tryMk_eq ty (x.val * y.val)
  split <;> simp_all
  simp_all [tryMk, tryMkOpt]
  rename_i hEq; simp only [← hEq, ofNatCore, val]
  split_conjs
  . simp [max]; omega
  . zify at this; zify; simp only [bv_toNat, BitVec.toNat_ofFin, Nat.cast_mul, BitVec.toNat_mul,
    Int.ofNat_emod, Nat.cast_pow, Nat.cast_ofNat] at *
    rw [Int.emod_eq_of_lt]
    . apply Int.pos_mul_pos_is_pos <;> simp
    . simp [*]
  . have : 0 < 2^ty.numBits := by simp
    simp [max]
    omega

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.mul_bv_spec {ty} {x y : UScalar ty}
  (hmax : ↑x * ↑y ≤ UScalar.max ty) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv := by
  have : x * y = mul x y := by rfl
  have := mul_equiv x y
  split at this <;> simp_all
  omega

theorem IScalar.mul_equiv {ty} (x y : IScalar ty) :
  match mul x y with
  | ok z => IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | fail _ => ¬(IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty)
  | .div => False := by
  simp [mul]
  have := tryMk_eq ty (x.val * y.val)
  split <;> simp_all [min, max] <;>
  simp_all [tryMk, tryMkOpt] <;>
  rename_i hEq <;> simp only [← hEq, ofIntCore, val] <;>
  simp [← BitVec.toInt_inj]
  . split_conjs
    . omega
    . simp [BitVec.toInt, Int.bmod]
      have this : 2 * (x.val * y.val % 2 ^ ty.numBits).toNat < 2 ^ ty.numBits ↔
            x.val * y.val % 2 ^ ty.numBits < (2 ^ ty.numBits + 1) / 2 := by
        have hdiv : (2 : ℤ) ∣ 2 ^ ty.numBits := by
          have : ty.numBits = (ty.numBits - 1) + 1 := by
            have := ty.numBits_nonzero
            scalar_tac
          rw [this, Int.pow_succ]; simp
        have : (2^ty.numBits + 1 : Int) / 2 = 2^ty.numBits / 2 := by
          rw [Int.add_ediv_of_dvd_left]
          . simp
          . apply hdiv
        rw [this]; clear this
        have heq := @Int.div_lt_div_iff_of_dvd_of_pos (↑x * ↑y % 2 ^ ty.numBits) 1 (2 ^ ty.numBits) 2
          (by simp) (by simp) (by simp) hdiv
        simp at heq
        simp [heq]
        have : (x.val * y.val % 2 ^ ty.numBits).toNat = x.val * y.val % 2 ^ ty.numBits := by
          scalar_tac
        scalar_tac
      simp [this]
      split <;> simp_all <;> omega
  . omega

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.mul_bv_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ IScalar.max ty) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv := by
  have : x * y = mul x y := by rfl
  have := mul_equiv x y
  split at this <;> simp_all

theorem Usize.mul_bv_spec {x y : Usize} (hmax : x.val * y.val ≤ Usize.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  UScalar.mul_bv_spec (by scalar_tac)

theorem U8.mul_bv_spec {x y : U8} (hmax : x.val * y.val ≤ U8.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  UScalar.mul_bv_spec (by scalar_tac)

theorem U16.mul_bv_spec {x y : U16} (hmax : x.val * y.val ≤ U16.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  UScalar.mul_bv_spec (by scalar_tac)

theorem U32.mul_bv_spec {x y : U32} (hmax : x.val * y.val ≤ U32.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  UScalar.mul_bv_spec (by scalar_tac)

theorem U64.mul_bv_spec {x y : U64} (hmax : x.val * y.val ≤ U64.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  UScalar.mul_bv_spec (by scalar_tac)

theorem U128.mul_bv_spec {x y : U128} (hmax : x.val * y.val ≤ U128.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  UScalar.mul_bv_spec (by scalar_tac)

theorem Isize.mul_bv_spec {x y : Isize}
  (hmin : Isize.min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ Isize.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  IScalar.mul_bv_spec (by scalar_tac) (by scalar_tac)

theorem I8.mul_bv_spec {x y : I8}
  (hmin : I8.min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ I8.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  IScalar.mul_bv_spec (by scalar_tac) (by scalar_tac)

theorem I16.mul_bv_spec {x y : I16}
  (hmin : I16.min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ I16.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  IScalar.mul_bv_spec (by scalar_tac) (by scalar_tac)

theorem I32.mul_bv_spec {x y : I32}
  (hmin : I32.min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ I32.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  IScalar.mul_bv_spec (by scalar_tac) (by scalar_tac)

theorem I64.mul_bv_spec {x y : I64} (hmin : I64.min ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ I64.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  IScalar.mul_bv_spec (by scalar_tac) (by scalar_tac)

theorem I128.mul_bv_spec {x y : I128} (hmin : I128.min ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ I128.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv :=
  IScalar.mul_bv_spec (by scalar_tac) (by scalar_tac)


/-!
Theorems with a specification which only use integers
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.mul_spec {ty} {x y : UScalar ty}
  (hmax : ↑x * ↑y ≤ UScalar.max ty) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y := by
  have ⟨ z, h⟩ := mul_bv_spec hmax
  simp [h]

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.mul_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ IScalar.max ty) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y := by
  have ⟨ z, h⟩ := @mul_bv_spec ty x y (by scalar_tac) (by scalar_tac)
  simp only [ok.injEq, _root_.exists_eq_left', h]

@[progress] theorem Usize.mul_spec {x y : Usize} (hmax : x.val * y.val ≤ Usize.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y :=
  UScalar.mul_spec (by scalar_tac)

@[progress] theorem U8.mul_spec {x y : U8} (hmax : x.val * y.val ≤ U8.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y :=
  UScalar.mul_spec (by scalar_tac)

@[progress] theorem U16.mul_spec {x y : U16} (hmax : x.val * y.val ≤ U16.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y :=
  UScalar.mul_spec (by scalar_tac)

@[progress] theorem U32.mul_spec {x y : U32} (hmax : x.val * y.val ≤ U32.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y :=
  UScalar.mul_spec (by scalar_tac)

@[progress] theorem U64.mul_spec {x y : U64} (hmax : x.val * y.val ≤ U64.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y :=
  UScalar.mul_spec (by scalar_tac)

@[progress] theorem U128.mul_spec {x y : U128} (hmax : x.val * y.val ≤ U128.max) :
  ∃ z, x * y = ok z ∧ (↑z : Nat) = ↑x * ↑y :=
  UScalar.mul_spec (by scalar_tac)

@[progress] theorem Isize.mul_spec {x y : Isize}
  (hmin : Isize.min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ Isize.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  IScalar.mul_spec (by scalar_tac) (by scalar_tac)

@[progress] theorem I8.mul_spec {x y : I8}
  (hmin : I8.min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ I8.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  IScalar.mul_spec (by scalar_tac) (by scalar_tac)

@[progress] theorem I16.mul_spec {x y : I16}
  (hmin : I16.min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ I16.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  IScalar.mul_spec (by scalar_tac) (by scalar_tac)

@[progress] theorem I32.mul_spec {x y : I32}
  (hmin : I32.min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ I32.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  IScalar.mul_spec (by scalar_tac) (by scalar_tac)

@[progress] theorem I64.mul_spec {x y : I64} (hmin : I64.min ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ I64.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  IScalar.mul_spec (by scalar_tac) (by scalar_tac)

@[progress] theorem I128.mul_spec {x y : I128} (hmin : I128.min ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ I128.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  IScalar.mul_spec (by scalar_tac) (by scalar_tac)

end Aeneas.Std
