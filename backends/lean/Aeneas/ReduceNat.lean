import AeneasMeta.Utils
import Aeneas.ScalarTac.Init

namespace Aeneas.ReduceNat

open Lean Meta

theorem Eq.comm' {α} (x y : α) : (x = y) = (y = x) := by
  simp only [eq_iff_iff]; constructor <;> simp +contextual

/-- If often happens that we have an equality of the shape: `32 = e` (i.e., a constant number
   on the LHS of an equality). When this happens, we swap the equality so that the constant goes
   to the right, or the variable goes to the left.

   This leads to more natural rewritings, and also prevents looping issues when using `simp_all`.

   Rem.: we tried to have a more precise pattern, but we couldn't
-/
simproc reduceNatEq (@Eq Nat _ _) :=
  fun e => do
  match e.consumeMData.getAppFnArgs with
  | (``Eq, #[_, lhs, rhs]) =>
    trace[Utils] "- lhs: {lhs}\n- rhs: {rhs}"
    -- Check that the lhs is a constant
    if (Utils.exprToNat? lhs).isNone then return .continue
    -- Check that the rhs is not a constant
    if (Utils.exprToNat? rhs).isSome then return .continue
    -- Create the new expression
    let expr ← mkAppM ``Eq #[rhs, lhs]
    let proof? ← mkAppM ``Eq.comm' #[lhs, rhs]
    trace[Utils] "- expr: {expr}\n- proof?: {proof?}"
    return .visit {expr, proof?}
  | _ => return .continue

attribute [scalar_tac_simps] reduceNatEq

example {x y : Nat} (h : 32 = x + y) : x + y = 32 := by
  simp only [reduceNatEq] at h
  apply h

end Aeneas.ReduceNat
