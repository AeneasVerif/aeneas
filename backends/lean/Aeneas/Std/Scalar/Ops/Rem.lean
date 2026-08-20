import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open RustM Error Arith ScalarElab WP

/-!
# Remainder: Definitions
-/
def UScalar.rem {ty : UScalarTy} (x y : UScalar ty) : RustM (UScalar ty) :=
  if y.val != 0 then ok ⟨ BitVec.umod x.bv y.bv ⟩ else fail panic

def IScalar.rem {ty : IScalarTy} (x y : IScalar ty) : RustM (IScalar ty) :=
  if y.val != 0 then
    -- There can be an overflow if `x` is equal to the lower bound and `y` to `-1`
    if ¬ (x.val = IScalar.min ty && y.val = -1) then ok ⟨ BitVec.srem x.bv y.bv ⟩
    else fail panic
  else fail panic

def UScalar.try_rem {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (rem x y)

def IScalar.try_rem {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofRustM (rem x y)

instance {ty} : HMod (UScalar ty) (UScalar ty) (RustM (UScalar ty)) where
  hMod x y := UScalar.rem x y

instance {ty} : HMod (IScalar ty) (IScalar ty) (RustM (IScalar ty)) where
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

  -- Checking that `MIN % -1` panics (like `MIN / -1`) while `MIN % 1` succeeds
  #assert (IScalar.rem (I8.ofInt (-2^7)) (I8.ofInt (-1)) == fail panic)
  #assert (IScalar.rem (I16.ofInt (-2^15)) (I16.ofInt (-1)) == fail panic)
  #assert (IScalar.rem (I32.ofInt (-2^31)) (I32.ofInt (-1)) == fail panic)
  #assert (IScalar.rem (I64.ofInt (-2^63)) (I64.ofInt (-1)) == fail panic)
  #assert (IScalar.rem (I128.ofInt (-2^127)) (I128.ofInt (-1)) == fail panic)
  #assert (IScalar.rem (I8.ofInt (-2^7)) (I8.ofInt 1) == ok (I8.ofInt 0))
  #assert (IScalar.rem (I16.ofInt (-2^15)) (I16.ofInt 1) == ok (I16.ofInt 0))
  #assert (IScalar.rem (I32.ofInt (-2^31)) (I32.ofInt 1) == ok (I32.ofInt 0))
  #assert (IScalar.rem (I64.ofInt (-2^63)) (I64.ofInt 1) == ok (I64.ofInt 0))
  #assert (IScalar.rem (I128.ofInt (-2^127)) (I128.ofInt 1) == ok (I128.ofInt 0))
  #assert (IScalar.rem (I32.ofInt (-7)) (I32.ofInt (-1)) == ok (I32.ofInt 0))
  #assert (IScalar.rem (I32.ofInt 7) (I32.ofInt 3) == ok (I32.ofInt 1))
  #assert (IScalar.rem (I32.ofInt 7) (I32.ofInt 0) == fail panic)
  #assert (UScalar.rem (U32.ofNat 7) (U32.ofNat 3) == ok (U32.ofNat 1))
  #assert (UScalar.rem (U32.ofNat 7) (U32.ofNat 0) == fail panic)
end Tests

/-!
# Remainder: Theorems
-/

/-!
Theorems with a specification which uses integers and bit-vectors
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.rem_bv_spec {ty} (x : UScalar ty) {y : UScalar ty} (hzero : y.val ≠ 0) :
  x % y ⦃ z => (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv ⦄ := by
  conv => arg 1; simp [HMod.hMod]
  simp [hzero, rem]
  simp only [val]
  simp

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.rem_bv_spec {ty} (x : IScalar ty) {y : IScalar ty} (hzero : y.val ≠ 0)
  (hNoOverflow : ¬ (x.val = IScalar.min ty ∧ y.val = -1)) :
  x % y ⦃ z => (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv ⦄ := by
  conv => arg 1; simp [HMod.hMod]
  simp only [spec_ok, rem, bne_iff_ne, ne_eq, hzero, not_false_eq_true, ↓reduceIte,
    Int.reduceNeg, Bool.and_eq_true, decide_eq_true_eq, hNoOverflow]
  simp only [val]
  simp only [BitVec.toInt_srem, bv_toInt_eq, and_true]


uscalar theorem «%S».rem_bv_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
  x % y ⦃ z => (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv ⦄ :=
  UScalar.rem_bv_spec x hnz

iscalar theorem «%S».rem_bv_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0)
  (hNoOverflow : ¬ (x.val = «%S».min ∧ y.val = -1)) :
  x % y ⦃ z => (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv ⦄ :=
  IScalar.rem_bv_spec x hnz (by scalar_tac)

/-!
Theorems with a specification which only uses integers
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.rem_spec {ty} (x : UScalar ty) {y : UScalar ty} (hzero : y.val ≠ 0) :
  x % y ⦃ z => (↑z : Nat) = ↑x % ↑y ⦄ := by
  apply spec_mono
  · apply rem_bv_spec x hzero
  · intros x' h
    exact h.1

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.rem_spec {ty} (x : IScalar ty) {y : IScalar ty} (hzero : y.val ≠ 0)
  (hNoOverflow : ¬ (x.val = IScalar.min ty ∧ y.val = -1)) :
  x % y ⦃ z => (↑z : Int) = Int.tmod ↑x ↑y ⦄ := by
  apply spec_mono
  · apply rem_bv_spec x hzero hNoOverflow
  · intros x' h
    exact h.1

uscalar @[step] theorem «%S».rem_spec (x : «%S») {y : «%S»} :
    partialSpec (x % y)
      (fun z => (↑z : Nat) = ↑x % ↑y)
      (fun | .panic => (↑y : Nat) = 0 | _ => False)
      False := by
  have hxy : (x % y : RustM _) = UScalar.rem x y := rfl
  rw [hxy]
  by_cases hy : y.val = 0
  · simp [partialSpec, UScalar.rem, hy]
  · have h := UScalar.rem_spec x hy
    rw [hxy] at h
    simp_all [partialSpec]
    split <;> simp_all

iscalar @[step] theorem «%S».rem_spec (x : «%S») {y : «%S»} :
    partialSpec (x % y)
      (fun z => (↑z : Int) = Int.tmod ↑x ↑y)
      (fun | .panic => ((↑y : Int) = 0) ∨ ((↑x : Int) = «%S».min ∧ (↑y : Int) = -1)
           | _ => False)
      False := by
  have hxy : (x % y : RustM _) = IScalar.rem x y := rfl
  rw [hxy]
  by_cases hy : y.val = 0
  · simp [partialSpec, IScalar.rem, hy]
  · by_cases ho : x.val = IScalar.min (IScalarTy.«%S») ∧ y.val = -1
    · simp [partialSpec, IScalar.rem, ho.1, ho.2]
      try scalar_tac
    · have h := IScalar.rem_spec x hy ho
      rw [hxy] at h
      simp_all [partialSpec]
      split <;> simp_all

end Aeneas.Std
