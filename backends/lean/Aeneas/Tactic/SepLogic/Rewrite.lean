import Aeneas.Tactic.SepLogic.Frame

/-!
# `irewrite`

Rewriting one of the `∗`-separated atoms of the current resources with an
entailment or an equality, which is how a representation predicate is opened or
closed when plain cancellation cannot see through it.
-/

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

/-- The rule behind `irewrite`: rewrite a part of the left-hand side of an
entailment with an entailment of its own. -/
theorem entails_rewrite {H₁ H₂ H₃ H₄ : IProp} (hPart : H₁ ⊢ H₂)
    (hRest : H₂ ∗ H₃ ⊢ H₄) : H₁ ∗ H₃ ⊢ H₄ :=
  entails_trans (sep_mono hPart (entails_refl H₃)) hRest

namespace IFrame

/-- Rewrite the assertion `H` (the left-hand side of an entailment, or the
precondition of a triple) using `lemma : A ⊢ B` or `lemma : A = B`, replacing the
atom `A` of `H` by `B`.  Returns the rewritten assertion and a proof of
`H ⊢ rewritten`. -/
def rewriteAssertion (assertion : Expr) (rule : Expr) : TacticM (Expr × Expr) := do
  let ruleType ← instantiateMVars (← inferType rule)
  /- Accept both an entailment and an equality, in either direction for the
     latter. -/
  let (lhs, rhs, entailment) ←
    if ruleType.consumeMData.isAppOfArity ``Entails 2 then
      let args := ruleType.consumeMData.getAppArgs
      pure (args[0]!, args[1]!, rule)
    else if let some (_, lhs, rhs) := ruleType.consumeMData.eq? then
      pure (lhs, rhs, ← mkAppM ``entails_of_eq #[rule])
    else
      throwError "irewrite expects an entailment `A ⊢ B` or an equality \
        `A = B`, got {ruleType}"
  let atoms ← flatten assertion
  /- The rewritten part may be a separating conjunction of several atoms, which
     do not have to be adjacent in `assertion`. -/
  let some restAtoms ← removeMatches atoms (← flatten lhs)
    | throwError "irewrite: {lhs}\nis not part of\n{assertion}"
  let rest := mkStar restAtoms
  let reordered := mkApp2 (mkConst ``sep) (← instantiateMVars lhs) rest
  let reorder ← mkAppM ``entails_of_eq #[← proveEqAC assertion reordered]
  let rewritten := mkApp2 (mkConst ``sep) (← instantiateMVars rhs) rest
  let change ← mkAppM ``sep_mono #[entailment, ← mkAppM ``entails_refl #[rest]]
  return (rewritten, ← mkAppM ``entails_trans #[reorder, change])

end IFrame

/-- Rewrite part of the current resources with an entailment.

`irewrite M`, for `M : A ⊢ B` (or `M : A = B`), replaces the assertion `A` by
`B` in the left-hand side of the entailment, or in the precondition of the
triple, that the goal states.  This is how a representation predicate is opened
or closed when plain cancellation cannot see through it.

Unlike `rw`, `M` need not be an equality and `A` need not occur syntactically:
it only has to be one of the `∗`-separated atoms, up to unification. -/
elab "irewrite" rule:term : tactic => Tactic.focus do withMainContext do
  let rule ← Tactic.elabTerm rule none
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``Entails && args.size = 2 then
    let (rewritten, proof) ← IFrame.rewriteAssertion args[0]! rule
    let next ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Entails #[rewritten, args[1]!])
    goal.assign (← mkAppM ``entails_trans #[proof, next])
    replaceMainGoal [next.mvarId!]
  else if fn.isConstOf `Aeneas.SepLogic.triple && args.size = 4 then
    let (rewritten, proof) ← IFrame.rewriteAssertion args[1]! rule
    let next ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppOptM `Aeneas.SepLogic.triple #[args[0]!, rewritten, args[2]!, args[3]!])
    let qrefl ← withLocalDeclD `value args[0]! fun value => do
      mkLambdaFVars #[value] (← mkAppM ``entails_refl #[mkApp args[3]! value])
    goal.assign (← mkAppM `Aeneas.SepLogic.triple_conseq #[next, proof, qrefl])
    replaceMainGoal [next.mvarId!]
  else
    throwError "irewrite expects an entailment or a triple, got\n{target}"

end Aeneas.SepLogic
