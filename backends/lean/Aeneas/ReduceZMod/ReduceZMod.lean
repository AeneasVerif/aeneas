import Aeneas.ReduceZMod.Init
import Mathlib.Algebra.Algebra.ZMod
import AeneasMeta.Utils

namespace Aeneas.ReduceZMod

open Utils
open Lean Meta

/- TODO: it might be possible to remove some of those simp procedures with simp lemmas,
   by using the notation `ofNat(x)`
   (https://github.com/leanprover-community/mathlib4/blob/ce412ec13b32cf08820842e2ec234161d6dbd5d2/Mathlib/Tactic/OfNat.lean#L8) -/

/-- A simproc to reduce ZMod expressions.

    For instance, it reduces `(12 : ZMod 8)` to `4`.
 -/
simproc reduceZMod (@OfNat.ofNat _ _
    (@instOfNatAtLeastTwo _ _
      (@AddMonoidWithOne.toNatCast _
        (@AddGroupWithOne.toAddMonoidWithOne _
          (@Ring.toAddGroupWithOne _ (@CommRing.toRing _ (ZMod.commRing _)))))
            _))  := fun e => do
  match e.consumeMData.getAppFnArgs with
  | (``OfNat.ofNat, #[fieldTy, value, _]) =>
    trace[ReduceZMod] "- fieldTy: {fieldTy}\n- value: {value}"
    -- Retrieve the value
    let value ← if let some value := exprToNat? value then pure value else return .continue
    trace[ReduceZMod] "Value: {value}"
    -- Retrieve the field
    let fieldTy ← whnf fieldTy
    trace[ReduceZMod] "reduced fieldTy: {fieldTy}"
    let field ← do
        match fieldTy.consumeMData.getAppFnArgs with
        | (``ZMod, #[field]) =>
          let field ← whnf field
          trace[ReduceZMod] "reduced field: {field}"
          if let some field := exprToNat? field then pure field else return .continue
        | _ => return .continue
    trace[ReduceZMod] "field: {field}"
    -- Compute the modulus
    let res := value % field
    -- Create the new expression - the proof is by reflection
    return .visit {expr := ← mkAppOptM ``OfNat.ofNat #[fieldTy, some (.lit (.natVal res)), none]}
  | _ => return .continue

/-- A simproc to reduce inverses in ZMod. -/
simproc reduceZModInv (@Inv.inv _ (ZMod.instInv _) _) := fun e => do
  match e.consumeMData.getAppFnArgs with
  | (``Inv.inv, #[fieldTy, inst, value0]) =>
    trace[ReduceZMod] "- fieldTy: {fieldTy}\n- inst: {inst}- value0: {value0}"
    -- Retrieve the field
    let field ←
      match inst.consumeMData.getAppFnArgs with
      | (``ZMod.instInv, #[field]) =>
        let field ← whnf field
        trace[ReduceZMod] "Field after reduction: {field}"
        if let some field := exprToNat? field then pure field else return .continue
      | _ => return .continue
    trace[ReduceZMod] "field: {field}"
    -- Retrieve the value
    let value ← if let some value := exprToNat? value0 then pure value else return .continue
    trace[ReduceZMod] "value: {value}"
    -- Compute the result
    let inv := (Nat.gcdA value field).toNat
    trace[ReduceZMod] "inverse: {inv}"
    /- Create the new expression.
       We can't do the proof by reflection because it is too expensive, so
       we use the property that if `value0 * inv = 1` then `inv = value0⁻¹` -/
    let inv ← mkAppOptM ``OfNat.ofNat #[fieldTy, some (.lit (.natVal inv)), none]
    trace[ReduceZMod] "inverse: {inv}"
    let mul_eq ← mkAppM ``Eq.refl #[← mkAppM ``HMul.hMul #[value0, inv]]
    trace[ReduceZMod] "mul_eq: {mul_eq}"
    let eq := mkAppN (.const ``ZMod.inv_eq_of_mul_eq_one []) #[.lit (.natVal field), value0, inv, mul_eq]
    trace[ReduceZMod] "eq: {eq}"
    return .visit {expr := inv, proof? := eq}
  | _ => return .continue

/-- A simproc to reduce powers in ZMod. -/
simproc reduceZModPow
  (@HPow.hPow _ Nat _
      (@instHPow _ Nat
        (@Monoid.toNatPow _
          (@MonoidWithZero.toMonoid _
            (@Semiring.toMonoidWithZero _
              (@CommSemiring.toSemiring _ (@CommRing.toCommSemiring _ (ZMod.commRing _)))))))
      _ _) := fun e => do
  trace[ReduceZMod] "Visiting: {e}"
  match e.consumeMData.getAppFnArgs with
  | (``HPow.hPow, #[fieldTy, _, _, inst, value, pow]) =>
    trace[ReduceZMod] "- fieldTy: {fieldTy},\n- inst: {inst},\n- value: {value}\n- pow: {pow}"
    let redFieldTy ← whnf fieldTy
    trace[ReduceZMod] "reduced field type: {redFieldTy}"
    let field ← match redFieldTy.consumeMData.getAppFnArgs with
      | (``ZMod, #[field]) => whnf field
      | _ => return .continue
    trace[ReduceZMod] "field: {field}"
    let field ← if let some field := exprToNat? field then pure field else return .continue
    trace[ReduceZMod] "field: {field}"
    let value ← if let some value := exprToNat? value then pure value else return .continue
    trace[ReduceZMod] "value: {value}"
    let pow ← if let some pow := exprToNat? pow then pure pow else return .continue
    trace[ReduceZMod] "pow: {pow}"
    -- Reduce
    let res := (value ^ pow) % field
    trace[ReduceZMod] "res: {res}"
    -- Create the new expression - the proof is by reflection
    let res ← mkAppOptM ``OfNat.ofNat #[fieldTy, some (.lit (.natVal res)), none]
    return .visit {expr := res}
  | _ => return .continue


namespace Test
  set_option linter.dupNamespace false

  /-!
  ReduceZMod
  -/
  example : (12 : ZMod 12) = 0 := by simp only [reduceZMod]
  example : (1 : ZMod 12) - (12 : ZMod 12) = 1 := by simp only [reduceZMod, sub_zero]

  private abbrev Q := 3329
  private abbrev Zq := ZMod Q

  example : (3329 : Zq) = (0 : Zq) := by simp only [reduceZMod]

  example : (@OfNat.ofNat Zq 3329
    (@instOfNatAtLeastTwo Zq 3329
      (@AddMonoidWithOne.toNatCast Zq
        (@AddGroupWithOne.toAddMonoidWithOne Zq
          (@Ring.toAddGroupWithOne Zq
            (@CommRing.toRing Zq (ZMod.commRing (@OfNat.ofNat Nat 3329 (instOfNatNat 3329)))))))
      _)) = 0 := by
      simp only [reduceZMod]

  /-!
  ReduceZModInv
  -/
  example : (12⁻¹ : ZMod 7) = 3 := by simp only [reduceZModInv]
  example : (65536⁻¹ : Zq) = (169 : Zq) := by simp only [reduceZModInv]

  /-!
  ReduceZModPow
  -/
  example : ((2 ^ 16)⁻¹ : Zq) = (169 : Zq) := by simp only [reduceZModPow, reduceZModInv]

end Test

end Aeneas.ReduceZMod
