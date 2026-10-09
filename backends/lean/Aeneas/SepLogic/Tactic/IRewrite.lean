module
public import Aeneas.SepLogic.Tactic.IFrame
public meta import Lean
public meta import AeneasMeta.Simp

/-! `irewrite M` replaces atoms `A` of the precondition by `B`, given `M : A ⊢ B` or `M : A = B`.
It finds `A` with `iframe`'s frame inference on `pre ⊢ A ∗ ?F`, then concludes with `sep_mono`;
the premises of `M` are found by unification or become goals. Same design as CFML `xchange` (which
reuses `xsimpl`), Bedrock2 `seprewrite_in` and VST `sep_apply`; Iris selects hypotheses by name
instead, which this logic, without modalities or persistence, does not need. -/

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
  -- find `lhs` in `assertion` by frame inference: `assertion ⊢ lhs ∗ ?frame`
  let frame ← mkFreshExprMVar (mkConst ``IProp)
  let lhsFrame := mkApp2 (mkConst ``sep) lhs frame
  let framing ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Entails) assertion lhsFrame)
  try IFrame.solveGoal none framing.mvarId!
  catch e => throwError "irewrite: {lhs}\nis not part of\n{assertion}\n(open its existentials \
    with `iintro` first)\n{e.toMessageData}"
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  let entailment ← instantiateMVars entailment
  let frame ← instantiateMVars frame
  let lhsFrame := mkApp2 (mkConst ``sep) lhs frame
  let trans (a b c pab pbc : Expr) := mkApp5 (mkConst ``entails_trans) a b c pab pbc
  let rewritten := mkApp2 (mkConst ``sep) rhs frame
  let change := mkApp6 (mkConst ``sep_mono) lhs rhs frame frame entailment
    (mkApp (mkConst ``entails_refl) frame)
  let proof := trans assertion lhsFrame rewritten (← instantiateMVars framing) change
  unless frame.consumeMData.isConstOf `Aeneas.SepLogic.emp do return (rewritten, proof)
  return (rhs, trans assertion rewritten rhs proof
    (mkApp3 (mkConst ``entails_of_eq) rewritten rhs (mkApp (mkConst ``sep_emp_r_eq) rhs)))

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
