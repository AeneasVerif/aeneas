module
public import Aeneas.SepLogic.Tactic.IFrame
public meta import Lean
public meta import AeneasMeta.Simp
public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Normalize Matchers

namespace IRewrite

def rewriteAssertion (assertion : Expr) (rule : Expr) : TacticM (Expr × Expr) := do
  let ruleType ← instantiateMVars (← inferType rule)
  let (lhs, rhs, entailment) ←
    if ruleType.consumeMData.isAppOfArity ``Entails 2 then
      let args := ruleType.consumeMData.getAppArgs
      pure (args[0]!, args[1]!, rule)
    else if let some (_, lhs, rhs) := ruleType.consumeMData.eq? then
      pure (lhs, rhs, mkApp3 (mkConst ``entails_of_eq) lhs rhs rule)
    else
      throwError "irewrite expects an entailment `A ⊢ B` or an equality \
        `A = B`, got {ruleType}"
  let assertion ← reducePostApplication assertion
  let some (pairs, restAtoms) ← matchAll (← flatten assertion) (← flatten lhs)
    | throwError "irewrite: {lhs}\nis not part of\n{assertion}"
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  let entailment ← instantiateMVars entailment
  let trans (a b c pab pbc : Expr) := mkApp5 (mkConst ``entails_trans) a b c pab pbc
  if restAtoms.isEmpty then
    let reorder := mkApp3 (mkConst ``entails_of_eq) assertion lhs
      (← proveEqAC assertion lhs pairs)
    return (rhs, trans assertion lhs rhs reorder entailment)
  let rest := mkStar restAtoms
  let reordered := mkApp2 (mkConst ``sep) lhs rest
  let reorder := mkApp3 (mkConst ``entails_of_eq) assertion reordered
    (← proveEqAC assertion reordered pairs)
  let rewritten := mkApp2 (mkConst ``sep) rhs rest
  let change := mkApp6 (mkConst ``sep_mono) lhs rhs rest rest entailment
    (mkApp (mkConst ``entails_refl) rest)
  return (rewritten, trans assertion reordered rewritten reorder change)

end IRewrite

/-- Rewrite an atom `A` of the precondition with `M : A ⊢ B` (or `M : A = B`; `← M` rewrites
with `M : B = A`). Explicit arguments of `M` are found by matching, or become new goals. -/
elab "irewrite " symm:("← ")? rule:term : tactic => Tactic.focus do withMainContext do
  let rule ← Tactic.elabTerm rule none
  -- not `forallMetaTelescopeReducing`: it would unfold `Entails` itself
  let (premises, binderInfos, _) ← forallMetaTelescope (← inferType rule)
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
  goal.assign (mkApp5 (mkConst ``entails_trans) args[0]! rewritten args[1]! proof next)
  postprocessAppMVars `irewrite goal premises binderInfos
  let premises ← premises.filterM fun premise => return !(← premise.mvarId!.isAssigned)
  replaceMainGoal (next.mvarId! :: premises.toList.map Expr.mvarId!)

end Aeneas.SepLogic
