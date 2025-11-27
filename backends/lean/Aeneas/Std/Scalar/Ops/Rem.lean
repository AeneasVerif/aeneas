import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab

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
  simp [hzero, rem]
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

uscalar theorem «%S».rem_bv_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv :=
  UScalar.rem_bv_spec x hnz

iscalar theorem «%S».rem_bv_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
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

uscalar @[progress] theorem «%S».rem_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Nat) = ↑x % ↑y :=
  UScalar.rem_spec x hnz

iscalar @[progress] theorem «%S».rem_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = Int.tmod ↑x ↑y :=
  IScalar.rem_spec x hnz

end Aeneas.Std
