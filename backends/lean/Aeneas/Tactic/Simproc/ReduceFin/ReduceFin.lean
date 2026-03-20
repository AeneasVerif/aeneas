import Aeneas.ReduceFin.Init
import AeneasMeta.Utils

namespace Aeneas.ReduceFin

open Utils
open Lean Meta

/-
TODO: the following lemma might be enough
theorem Fin.val_ofNat{n: Nat}[NeZero n]{x: Nat}
: (ofNat(x): Fin n).val = x % n
-/

/-- A simp proc to reduce expressions of the shape: `Fin.val (6 : Fin 7)` -/
simproc reduceFinOfNatVal
  -- TODO: for some reason we can't use a more precise pattern, otherwise it doesn't match
  (@Fin.val _ _)
        := fun e => do
  trace[ReduceFin] "- e: {e}\n"
  match e.consumeMData.getAppFnArgs with
  | (``Fin.val, #[finTy, value]) =>
    trace[ReduceFin] "- finTy: {finTy}\n- value: {value}\n"
    -- Small helper
    let extractOfNatValue (e : Expr) : Option Nat :=
      match e.consumeMData.getAppFnArgs with
      | (``OfNat.ofNat, #[_, value, _]) =>
        match exprToNat? value with
        | none => none
        | some value => some value
      | _ => none
    -- Retrieve the finite type
    let finTyN ← do
      let finTy ← whnf finTy
      match extractOfNatValue finTy with
      | some value => pure value
      | _ => return .continue
    trace[ReduceFin] "- finTyN: {finTyN}\n"
    let value ← do
      match extractOfNatValue value with
      | some value => pure value
      | _ => return .continue
    trace[ReduceFin] "- value: {value}\n"
    -- Compute the reduced value
    let reduced := value % finTyN
    trace[ReduceFin] "- reduced: {reduced}\n"
    -- Create the new expression - the proof is by reflection
    return .visit {expr := (.lit (.natVal reduced))}
  | _ => return .continue

example : (12 : Fin 7).val = 5 := by
  simp only [Fin.isValue] -- This simp procedure comes from Lean
  simp

end Aeneas.ReduceFin
