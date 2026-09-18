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

/-- Rewrite the assertion `H` using `lemma : A ⊢ B` or `lemma : A = B`,
replacing the atom `A` of `H` by `B`. Returns the rewritten assertion and a
proof of `H ⊢ rewritten`. -/
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
`B` in the left-hand side of the entailment that the goal states. Reducible
wrappers around an entailment are preserved. This is how a representation
predicate is opened or closed when plain cancellation cannot see through it.

Unlike `rw`, `M` need not be an equality and `A` need not occur syntactically:
it only has to be one of the `∗`-separated atoms, up to unification. -/
elab "irewrite" rule:term : tactic => Tactic.focus do withMainContext do
  let rule ← Tactic.elabTerm rule none
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← IFrame.exposeEntailment? target
    | throwError "irewrite expects an entailment, got\n{target}"
  let args := entailment.getAppArgs
  let (rewritten, proof) ← IFrame.rewriteAssertion args[0]! rule
  let nextType ← IFrame.mkEntailmentLike target args[0]! args[1]! rewritten
  let next ← mkFreshExprSyntheticOpaqueMVar nextType
  goal.assign (← mkAppM ``entails_trans #[proof, next])
  replaceMainGoal [next.mvarId!]

end Aeneas.SepLogic
