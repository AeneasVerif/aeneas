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
  simp only [rem, bne_iff_ne, ne_eq, hzero, not_false_eq_true, ↓reduceIte, ok.injEq,
    _root_.exists_eq_left', and_true]
  simp only [val]
  simp only [BitVec.toInt_srem, bv_toInt_eq]

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
