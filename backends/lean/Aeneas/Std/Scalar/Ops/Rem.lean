import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.ScalarTac
import Aeneas.Std.Core
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith

/-!
# Remainder: Definitions
-/
def UScalar.rem {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if y.val != 0 then ok ⟨ BitVec.umod x.bv y.bv ⟩ else fail divisionByZero

def IScalar.rem {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  if y.val != 0 then ok ⟨ BitVec.srem x.bv y.bv ⟩
  else fail divisionByZero

def UScalar.try_rem {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (rem x y)

def IScalar.try_rem {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (rem x y)

instance {ty} : HMod (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hMod x y := UScalar.rem x y

instance {ty} : HMod (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hMod x y := IScalar.rem x y

/-!
# Sanity Checks
-/

/-!
The scalar division/modulo on signed machine integers 't'runcates towards 0, meaning it is
implemented by the `Int.tdiv`, `Int.tmod`, etc. definitions.
-/

namespace Tests
  -- Checking that the remainder over signed integers agrees with Rust
  #assert Int.tmod 1 2 = 1
  #assert Int.tmod (-1) 2 = -1
  #assert Int.tmod 1 (-2) = 1
  #assert Int.tmod (-1) (-2) = -1
  #assert Int.tmod 7 3 = (1:Int)
  #assert Int.tmod (-7) 3 = -1
  #assert Int.tmod 7 (-3) = 1
  #assert Int.tmod (-7) (-3) = -1

  -- Checking that the signed operation over bit-vectors agrees with Rust
  private def bv_srem (x y : Int) : Int :=
    (BitVec.srem (BitVec.ofInt 32 x) (BitVec.ofInt 32 y)).toInt

  #assert bv_srem 1 2 = 1
  #assert bv_srem (-1) 2 = -1
  #assert bv_srem 1 (-2) = 1
  #assert bv_srem (-1) (-2) = -1
  #assert bv_srem 7 3 = (1:Int)
  #assert bv_srem (-7) 3 = -1
  #assert bv_srem 7 (-3) = 1
  #assert bv_srem (-7) (-3) = -1
end Tests

/-!
# Remainder: Theorems
-/

/-!
Theorems with a specification which uses integers and bit-vectors
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.rem_bv_spec {ty} (x : UScalar ty) {y : UScalar ty} (hzero : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv := by
  conv => congr; ext; lhs; simp [HMod.hMod]
  simp [hzero, rem, tryMk, tryMkOpt, ofOption, hmax, ofNatCore]
  simp only [val]
  simp

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.rem_bv_spec {ty} (x : IScalar ty) {y : IScalar ty} (hzero : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv := by
  conv => congr; ext; lhs; simp [HMod.hMod]
  simp [hzero, rem, tryMk, tryMkOpt, ofOption, hmax, ofIntCore]
  simp only [val]
  simp

  simp [BitVec.srem_eq]
  have pow2Ineq : (2^(ty.numBits - 1) : Int) < 2^ty.numBits := by
    have := ty.numBits_nonzero
    have : (0 : Int) < 2^(ty.numBits - 1) := by simp
    have : ty.numBits = ty.numBits - 1 + 1 := by omega
    conv => rhs; rw [this]
    rw [Int.pow_succ']
    omega
  have hxBounds := x.hBounds
  have hyBounds := y.hBounds
  have := ty.numBits_nonzero
  split

  . -- 0 ≤ x
    -- 0 ≤ y
    rename_i hxMsb hyMsb
    have hx := @BitVec.toInt_eq_msb_cond _ x.bv
    simp [hxMsb] at hx
    have hy := @BitVec.toInt_eq_msb_cond _ y.bv
    simp [hyMsb] at hy
    rw [Int.tmod_eq_emod] <;> try omega
    simp only [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_umod]
    have : ((x.bv.toNat % y.bv.toNat : Nat) : Int) < 2 ^ (ty.numBits - 1) := by
      have := @Nat.mod_lt x.bv.toNat y.bv.toNat (by omega)
      zify at this
      omega
    have : ((x.bv.toNat % y.bv.toNat : Nat) : Int).bmod (2 ^ ty.numBits) = x.bv.toNat % y.bv.toNat := by
      apply bmod_pow_numBits_eq_of_lt ty _ (by omega) (by omega)
    rw [this]; clear this
    simp only [hx, hy]

  . -- 0 ≤ x
    -- y < 0
    rename_i hxMsb hyMsb
    have hx := @BitVec.toInt_eq_msb_cond _ x.bv
    simp [hxMsb] at hx
    have hy := @BitVec.toInt_eq_msb_cond _ y.bv
    simp [hyMsb] at hy

    have hxNeg : 0 ≤ x.val := by
      have := @BitVec.msb_eq_toInt _ x.bv
      simp_all
    have hyNeg : y.val < 0 := by
      have := @BitVec.msb_eq_toInt _ y.bv
      simp_all

    have : x.val.tmod y.val = x.val.tmod (-y.val) := by simp
    rw [this]; clear this

    rw [Int.tmod_eq_emod] <;> try omega
    simp only [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_umod]

    have : ((x.bv.toNat % (-y.bv).toNat : Nat) : Int) < 2 ^ (ty.numBits - 1) := by
      have := @Nat.mod_le x.bv.toNat (-y.bv).toNat
      omega
    have : ((x.bv.toNat % (-y.bv).toNat : Nat) : Int).bmod (2 ^ ty.numBits) = x.bv.toNat % (-y.bv).toNat := by
      apply bmod_pow_numBits_eq_of_lt ty _ (by omega) (by omega)
    rw [this]; clear this
    simp only [hx]

    have := IScalar.neg_imp_toNat_neg_eq_neg_toInt y (by omega)
    simp only [this, val]

  . -- x < 0
    -- 0 ≤ y
    rename_i hxMsb hyMsb
    have hx := @BitVec.toInt_eq_msb_cond _ x.bv
    simp [hxMsb] at hx
    have hy := @BitVec.toInt_eq_msb_cond _ y.bv
    simp [hyMsb] at hy

    have hxNeg : x.val < 0 := by
      have := @BitVec.msb_eq_toInt _ x.bv
      simp_all
    have hyNeg : 0 ≤ y.val := by
      have := @BitVec.msb_eq_toInt _ y.bv
      simp_all

    have hModEq : ((-x.bv) % y.bv).toInt = ((-x.bv).toNat % y.bv.toNat : Nat) := by
      simp only [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_umod]

      have : ((-x.bv).toNat % y.bv.toNat : Nat) < (2 ^ (ty.numBits - 1) : Int) := by
        have := @Nat.mod_lt (-x.bv).toNat y.bv.toNat (by omega)
        simp only [val] at *
        -- TODO: this is annoying
        have : (2 ^ (ty.numBits - 1) : Nat) = (2 ^ (ty.numBits - 1) : Int) := by simp
        omega

      have := @bmod_pow_numBits_eq_of_lt ty ((-x.bv).toNat % y.bv.toNat : Nat)
        (by omega) (by omega)
      rw [this]

    have : 0 ≤ (-x.bv % y.bv).toInt := by omega

    have := BitVec.toInt_neg_of_pos_eq_neg (-x.bv % y.bv) (by omega) (by omega)
    rw [this]; clear this

    have : (-x.bv % y.bv).toInt = (-x.bv).toNat % y.bv.toNat := by
      rw [hModEq]; simp
    rw [this]; clear this

    have : x.val.tmod y.val = - (-x.val).tmod y.val := by simp
    rw [this]; clear this

    have hx := IScalar.neg_imp_toNat_neg_eq_neg_toInt x (by omega)
    simp only [hx, ← hy]

    rw [Int.tmod_eq_emod] <;> try omega

    simp only [val]

  . -- x < 0
    -- y < 0

    rename_i hxMsb hyMsb
    have hx := @BitVec.toInt_eq_msb_cond _ x.bv
    simp [hxMsb] at hx
    have hy := @BitVec.toInt_eq_msb_cond _ y.bv
    simp [hyMsb] at hy

    have hxNeg : x.val < 0 := by
      have := @BitVec.msb_eq_toInt _ x.bv
      simp_all
    have hyNeg : y.val < 0 := by
      have := @BitVec.msb_eq_toInt _ y.bv
      simp_all

    have : (x.val).tmod (y.val) = -(-x.val).tmod (-y.val) := by simp
    rw [this]; clear this

    rw [Int.tmod_eq_emod] <;> try omega

    have hx := IScalar.neg_imp_toNat_neg_eq_neg_toInt x (by omega)
    have hy := IScalar.neg_imp_toNat_neg_eq_neg_toInt y (by omega)

    have : 0 ≤ -x.bv.toInt % -y.bv.toInt := by
      scalar_tac +nonLin

    have : -2 ^ (ty.numBits - 1) ≤ -x.bv.toInt % -y.bv.toInt := by omega

    have hxmyToInt : (-x.bv % -y.bv).toInt = (-x.bv.toInt) % (-y.bv.toInt) := by
      conv => lhs; simp only [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_umod]
      push_cast
      simp only [hx, hy]
      apply bmod_pow_numBits_eq_of_lt
      . omega
      . simp only [val] at *
        have := @Int.emod_lt_of_pos (-x.bv.toInt) (-y.bv.toInt) (by omega)
        omega

    have : 0 ≤ (-x.bv % -y.bv).toInt := by
      simp only [hxmyToInt]
      omega

    have := BitVec.toInt_neg_of_pos_eq_neg (-x.bv % -y.bv) (by omega) (by omega)
    rw [this]; clear this

    simp only [hxmyToInt]
    simp

theorem U8.rem_bv_spec (x : U8) {y : U8} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv :=
  UScalar.rem_bv_spec x hnz

theorem U16.rem_bv_spec (x : U16) {y : U16} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv :=
  UScalar.rem_bv_spec x hnz

theorem U32.rem_bv_spec (x : U32) {y : U32} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv :=
  UScalar.rem_bv_spec x hnz

theorem U64.rem_bv_spec (x : U64) {y : U64} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv :=
  UScalar.rem_bv_spec x hnz

theorem U128.rem_bv_spec (x : U128) {y : U128} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv :=
  UScalar.rem_bv_spec x hnz

theorem Usize.rem_bv_spec (x : Usize) {y : Usize} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv :=
  UScalar.rem_bv_spec x hnz

theorem I8.rem_bv_spec (x : I8) {y : I8} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv :=
  IScalar.rem_bv_spec x hnz

theorem I16.rem_bv_spec (x : I16) {y : I16} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv :=
  IScalar.rem_bv_spec x hnz

theorem I32.rem_bv_spec (x : I32) {y : I32} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv :=
  IScalar.rem_bv_spec x hnz

theorem I64.rem_bv_spec (x : I64) {y : I64} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv :=
  IScalar.rem_bv_spec x hnz

theorem I128.rem_bv_spec (x : I128) {y : I128} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv :=
  IScalar.rem_bv_spec x hnz

theorem Isize.rem_bv_spec (x : I128) {y : I128} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv :=
  IScalar.rem_bv_spec x hnz

/-!
Theorems with a specification which only uses integers
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.rem_spec {ty} (x : UScalar ty) {y : UScalar ty} (hzero : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y := by
  have ⟨ z, hz ⟩ := rem_bv_spec x hzero
  simp [hz]

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.rem_spec {ty} (x : IScalar ty) {y : IScalar ty} (hzero : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y := by
  have ⟨ z, hz ⟩ := rem_bv_spec x hzero
  simp [hz]

@[progress] theorem U8.rem_spec (x : U8) {y : U8} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y :=
  UScalar.rem_spec x hnz

@[progress] theorem U16.rem_spec (x : U16) {y : U16} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y :=
  UScalar.rem_spec x hnz

@[progress] theorem U32.rem_spec (x : U32) {y : U32} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y :=
  UScalar.rem_spec x hnz

@[progress] theorem U64.rem_spec (x : U64) {y : U64} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y :=
  UScalar.rem_spec x hnz

@[progress] theorem U128.rem_spec (x : U128) {y : U128} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y :=
  UScalar.rem_spec x hnz

@[progress] theorem Usize.rem_spec (x : Usize) {y : Usize} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y :=
  UScalar.rem_spec x hnz

@[progress] theorem I8.rem_spec (x : I8) {y : I8} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y :=
  IScalar.rem_spec x hnz

@[progress] theorem I16.rem_spec (x : I16) {y : I16} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y :=
  IScalar.rem_spec x hnz

@[progress] theorem I32.rem_spec (x : I32) {y : I32} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y :=
  IScalar.rem_spec x hnz

@[progress] theorem I64.rem_spec (x : I64) {y : I64} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y :=
  IScalar.rem_spec x hnz

@[progress] theorem I128.rem_spec (x : I128) {y : I128} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y :=
  IScalar.rem_spec x hnz

@[progress] theorem Isize.rem_spec (x : I128) {y : I128} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y :=
  IScalar.rem_spec x hnz

end Aeneas.Std
