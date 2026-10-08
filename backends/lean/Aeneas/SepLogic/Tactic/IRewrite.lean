module
public import Aeneas.SepLogic.Tactic.IFrame
public meta import Lean
public meta import AeneasMeta.Simp
public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Normalize Common

namespace IRewrite

def rewriteAssertion (assertion : Expr) (rule : Expr) : TacticM (Expr × Expr) := do
  let ruleType ← instantiateMVars (← inferType rule)
  let (lhs, rhs, entailment) ←
    if ruleType.consumeMData.isAppOfArity ``Entails 2 then
      let args := ruleType.consumeMData.getAppArgs
      pure (args[0]!, args[1]!, rule)
    else if let some (_, lhs, rhs) := ruleType.consumeMData.eq? then
      pure (lhs, rhs, ← mkAppM ``entails_of_eq #[rule])
    else
      throwError "irewrite expects an entailment `A ⊢ B` or an equality \
        `A = B`, got {ruleType}"
  let assertion ← reducePostApplication assertion
  let atoms ← flatten assertion
  let some restAtoms ← removeMatches atoms (← flatten lhs)
    | throwError "irewrite: {lhs}\nis not part of\n{assertion}"
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if restAtoms.isEmpty then
    let reorder ← mkAppM ``entails_of_eq #[← proveEqAC assertion lhs]
    return (rhs, ← mkAppM ``entails_trans #[reorder, entailment])
  let rest := mkStar restAtoms
  let reordered := mkApp2 (mkConst ``sep) lhs rest
  let reorder ← mkAppM ``entails_of_eq #[← proveEqAC assertion reordered]
  let rewritten := mkApp2 (mkConst ``sep) rhs rest
  let change ← mkAppM ``sep_mono #[entailment, ← mkAppM ``entails_refl #[rest]]
  return (rewritten, ← mkAppM ``entails_trans #[reorder, change])

end IRewrite

/-- Rewrite an atom `A` of the precondition with `M : A ⊢ B` (or `M : A = B`; `← M` rewrites
with `M : B = A`). Explicit arguments of `M` are found by matching, or become new goals. -/
elab "irewrite " symm:("← ")? rule:term : tactic => Tactic.focus do withMainContext do
  let rule ← Tactic.elabTerm rule none
  let (premises, _, _) ← forallMetaTelescope (← inferType rule)
  let rule := mkAppN rule premises
  let rule ← if symm.isNone then pure rule else
    unless (← instantiateMVars (← inferType rule)).consumeMData.isAppOfArity ``Eq 3 do
      throwError "irewrite ← expects an equality `A = B`, got {← inferType rule}"
    mkEqSymm rule
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← exposeEntailment? target
    | throwError "irewrite expects an entailment, got\n{target}"
  let args := entailment.getAppArgs
  let (rewritten, proof) ← IRewrite.rewriteAssertion args[0]! rule
  let nextType ← mkEntailmentLike target args[0]! args[1]! rewritten
  let next ← mkFreshExprSyntheticOpaqueMVar nextType
  goal.assign (← mkAppM ``entails_trans #[proof, next])
  let premises ← premises.filterM fun premise => return !(← premise.mvarId!.isAssigned)
  replaceMainGoal (next.mvarId! :: premises.toList.map Expr.mvarId!)

end Aeneas.SepLogic
