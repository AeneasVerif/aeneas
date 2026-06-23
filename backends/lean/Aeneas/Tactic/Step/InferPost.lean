import Lean
import AeneasMeta.Utils
import Aeneas.Tactic.Solver.Grind.Init
import Aeneas.Tactic.Step.Init

namespace Aeneas

namespace Step

open Lean Elab Meta Tactic TacticM

/-- Infer a postcondition for a goal of the form `?post args...` of the form
    `fun x₁ ... xₙ => ∃ vars..., x₁ = a₁ ∧ ... ∧ xₙ = aₙ` and assign it to the postcondition metavariable.

    `eliminate` controls which free variables to try clearing from the context before collecting
    escaping variables -/
def inferPost (goal : MVarId) (eliminate : LocalDecl → Bool := fun _ => true) :
    TacticM MVarId := withTraceNode `Step (fun _ => do pure m!"inferPost") <| goal.withContext do
  traceGoalWithNode "metavariable context"
  let goalTy ← instantiateMVars (← goal.getType)

  -- The goal should be of the form `?post args...`
  let (mvarFn, args) := goalTy.withApp fun f a => (f, a)
  unless mvarFn.isMVar do
    throwError "inferPost: goal should be of the form `?post args...`, got {goalTy}"
  let postMVarId := mvarFn.mvarId!
  let args ← args.mapM instantiateMVars

  -- Get local contexts and decls
  let lctx ← getLCtx
  let lclDecls ← lctx.getDecls
  let mvarLCtx := (← postMVarId.getDecl).lctx

  -- Collect free vars not in the mvar's context or marked for elimination.
  let escapingLocalDecls := lclDecls.filter fun decl =>
    !(mvarLCtx.contains decl.fvarId || eliminate decl)

  -- Build postcondition: fun x₁ ... xₙ => ∃ vars..., x₁ = a₁ ∧ ... ∧ xₙ = aₙ ∧ props
  let lambdaArgs : Array (Name × Expr) ←
    args.mapM fun arg => do
      let argTy ← inferType arg
      let name ←
        if let some fvarId := arg.fvarId? then
          fvarId.getUserName
        else
          mkFreshUserName `x
      pure (name, argTy)
  let postExpr ← withLocalDeclsDND lambdaArgs fun boundVars => do
    -- Build conjuncts: equalities x₁ = a₁, ..., xₙ = aₙ, then relevant props
    let conjuncts ← boundVars.zip args |>.mapM fun (bvar, arg) => mkEq bvar arg

    let body ← match conjuncts.toList.reverse with
      | [] => pure (Lean.mkConst ``True)
      | last :: rest => rest.foldlM (fun acc c => mkAppM ``And #[c, acc]) last

    -- Wrap with existentials over all escaping vars
    let existsBody ← escapingLocalDecls.foldrM (fun decl acc => do
        mkAppM ``Exists #[← mkLambdaFVars #[.fvar decl.fvarId] acc]) body
    mkLambdaFVars boundVars existsBody
  trace[Step] m!"inferred postcondition: {←ppExpr postExpr}"
  postMVarId.assign postExpr
  pure goal

/-- Tactic that infers the postcondition and attempts to prove it with `grind` -/
elab "infer_post" : tactic => do
  let goal ← getMainGoal
  let _ ← inferPost goal
  evalTactic (←`(tactic|agrind))

end Step

end Aeneas
