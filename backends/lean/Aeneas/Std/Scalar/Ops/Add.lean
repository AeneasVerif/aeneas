import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Addition: Definitions
-/
def UScalar.add {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.val + y.val)

def IScalar.add {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.val + y.val)

def UScalar.try_add {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (add x y)

def IScalar.try_add {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (add x y)

instance {ty} : HAdd (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hAdd x y := UScalar.add x y

instance {ty} : HAdd (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hAdd x y := IScalar.add x y


/-!
# Addition: Theorems
-/

theorem UScalar.add_equiv {ty} (x y : UScalar ty) :
  match x + y with
  | ok z => x.val + y.val < 2^ty.numBits ∧
    z.val = x.val + y.val ∧
    z.bv = x.bv + y.bv
  | fail .integerOverflow => ¬ (UScalar.inBounds ty (x.val + y.val))
  | _ => False := by
  have : x + y = add x y := by rfl
  rw [this]
  simp [add]
  have h := tryMk_eq ty (↑x + ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  zify; simp
  zify at h
  have := @Int.emod_eq_of_lt (x.val + y.val) (2^ty.numBits) (by omega) (by omega)
  simp [*]

theorem IScalar.add_equiv {ty} (x y : IScalar ty) :
  match x + y with
  | ok z =>
    IScalar.inBounds ty (x.val + y.val) ∧
    z.val = x.val + y.val ∧
    z.bv = x.bv + y.bv
  | fail .integerOverflow => ¬ (IScalar.inBounds ty (x.val + y.val))
  | _ => False := by
  have : x + y = add x y := by rfl
  rw [this]
  simp [add]
  have h := tryMk_eq ty (↑x + ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  apply BitVec.eq_of_toInt_eq
  simp
  have := bmod_pow_numBits_eq_of_lt ty (x.val + y.val) (by omega) (by omega)
  simp [*]

/-!
Theorems about the addition, with a specification which uses
integers and bit-vectors.
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.add_bv_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [max]
  have : 0 < 2^ty.numBits := by simp
  omega

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.add_bv_spec {ty}  {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar theorem «%S».add_bv_spec {x y : «%S»} (hmax : x.val + y.val ≤ «%S».max) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ :=
  UScalar.add_bv_spec (by scalar_tac)

iscalar theorem «%S».add_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ :=
  IScalar.add_bv_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems about the addition, with a specification which uses
only integers. Those are the most common to use, so we mark them with the
`step` and `spec` attribute.
-/

section mvcgen
open Std.Do
set_option mvcgen.warning false

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.add_mvcgen {ty} {x y : UScalar ty} {Q}
  (hmax : UScalar.max ty < ↑x + ↑y → (Q.2.1 .integerOverflow).down)
  (h : ∀ z : UScalar ty, (↑z : Nat) = ↑x + ↑y → (Q.1 z).down) :
  ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ Q ⦄ := by
  have h := @UScalar.add_equiv _ x y
  split at h <;> try simp_all only [max] <;> (mvcgen; grind)

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.add_mvcgen {ty} {x y : IScalar ty} {Q}
  (hmin : ↑x + ↑y < IScalar.min ty → (Q.2.1 .integerOverflow).down)
  (hmax : IScalar.max ty < ↑x + ↑y → (Q.2.1 .integerOverflow).down)
  (h : ∀ z : IScalar ty, (↑z : Int) = ↑x + ↑y → (Q.1 z).down) :
  ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ Q ⦄ := by
  have h := @IScalar.add_equiv _ x y
  split at h <;> try simp_all only [min, max] <;> (mvcgen; grind)

uscalar @[spec] theorem «%S».add_mvcgen {Q} {x y : «%S»}
  (hmax : «%S».max < x.val + y.val → (Q.2.1 .integerOverflow).down)
  (h : ∀ z : «%S», (↑z : Nat) = ↑x + ↑y → (Q.1 z).down) :
  ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ Q ⦄ :=
  UScalar.add_mvcgen (by scalar_tac) (fun _ _ => h _ (by scalar_tac))

iscalar @[spec] theorem «%S».add_mvcgen {Q} {x y : «%S»}
  (hmin : ↑x + ↑y < «%S».min → (Q.2.1 .integerOverflow).down)
  (hmax : «%S».max < ↑x + ↑y → (Q.2.1 .integerOverflow).down)
  (h : ∀ z : «%S», (↑z : Int) = ↑x + ↑y → (Q.1 z).down) :
  ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ Q ⦄ :=
  IScalar.add_mvcgen (by scalar_tac) (by scalar_tac) (fun _ _ => h _ (by scalar_tac))

end mvcgen

section step

/-- Generic theorem - shouldn't be used much -/
@[step]
theorem UScalar.add_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ :=
  Result.spec_of_mvcgen (add_mvcgen (by omega) (by simp))

/-- Generic theorem - shouldn't be used much -/
@[step]
theorem IScalar.add_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ⦄ :=
  Result.spec_of_mvcgen (add_mvcgen (by omega) (by omega) (by simp))

uscalar @[step] theorem «%S».add_spec {x y : «%S»} (hmax : x.val + y.val ≤ «%S».max) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ :=
  UScalar.add_spec (by scalar_tac)

iscalar @[step] theorem «%S».add_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ⦄ :=
  IScalar.add_spec (by scalar_tac) (by scalar_tac)

end step

end Aeneas.Std
