import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Negation: Definitions
-/
@[step_pure_def]
def IScalar.neg {ty : IScalarTy} (x : IScalar ty) : Result (IScalar ty) := IScalar.tryMk ty (- x.val)

/--
The notation typeclass for heterogeneous negation.

There is no heterogenous negation in the Lean prelude: we thus introduce one here.
-/
class HNeg (α : Type u) (β : outParam (Type v)) where
  /-- `- a` computes the negation of `a`.
  The meaning of this notation is type-dependent. -/
  hNeg : α → β

/- Notation for heterogeneous negation.

   We initially used the notation "-" but it conflicted with the homogeneous
   negation too much. In particular, it made terms like `-10` ambiguous,
   and seemingly caused to backtracking in elaboration, leading to definitions
   like arrays of constants to take an unreasonable time to get elaborated
   and type-checked.

   TODO: PR to introduce HNeg in Lean?
 -/
prefix:75  "-."   => HNeg.hNeg

/- We need this, otherwise we break pattern matching like in:

   ```
   def is_minus_one (x : Int) : Bool :=
     match x with
     | -1 => true
     | _ => false
   ```
-/
attribute [match_pattern] HNeg.hNeg

instance {ty} : HNeg (IScalar ty) (Result (IScalar ty)) where hNeg x := IScalar.neg x

/-!
# Negation: Theorems
-/

theorem IScalar.neg_equiv {ty} (x : IScalar ty) :
  match -. x with
  | ok z =>
    IScalar.inBounds ty (- x.val) ∧
    z.val = - x.val ∧
    z.bv = - x.bv
  | fail _ => ¬ (IScalar.inBounds ty (- x.val))
  | _ => ⊥ := by
  have : (-. x : Result (IScalar ty)) = neg x := by rfl
  rw [this]
  simp [neg]
  have h := tryMk_eq ty (- x.val)
  simp [inBounds] at h
  split at h <;> simp_all
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_neg]
  have hbmod := bmod_pow_numBits_eq_of_lt ty (- x.val) (by omega) (by omega)
  simp only [val] at hbmod h ⊢
  rw [hbmod, h.1]

/- Generic theorem - shouldn't be used much -/
theorem IScalar.neg_bv_spec {ty} {x : IScalar ty}
  (hmin : IScalar.min ty ≤ - x.val)
  (hmax : - x.val ≤ IScalar.max ty) :
  (-. x) ⦃ z => (↑z : Int) = - x.val ∧ z.bv = - x.bv ⦄ := by
  have h := @neg_equiv ty x
  split at h <;> simp_all [min, max]
  omega

/- Generic theorem - shouldn't be used much -/
@[step]
theorem IScalar.neg_spec {ty} {x : IScalar ty}
  (hmin : IScalar.min ty ≤ - x.val)
  (hmax : - x.val ≤ IScalar.max ty) :
  (-. x) ⦃ z => (↑z : Int) = - x.val ⦄ := by
  have h := @neg_equiv ty x
  split at h <;> simp_all [min, max]
  omega

iscalar @[step] theorem «%S».neg_spec {x : «%S»}
  (hmin : «%S».min ≤ - x.val) (hmax : - x.val ≤ «%S».max) :
  (-. x) ⦃ z => (↑z : Int) = - x.val ⦄ :=
  IScalar.neg_spec (by scalar_tac) (by scalar_tac)

end Aeneas.Std
