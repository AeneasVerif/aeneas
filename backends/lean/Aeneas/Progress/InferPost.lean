import Lean
import AeneasMeta.Utils
import Aeneas.Grind.Init

namespace Aeneas

namespace Progress

open Lean Elab Term Meta Tactic

/-- Infer a postcondition for a goal of the form `?post args...` of the form
    `fun x₁ ... xₙ => ∃ vars..., x₁ = a₁ ∧ ... ∧ xₙ = aₙ ∧ props` and assign it to the postcondition metavariable.

    `eliminate` controls which free variables to try clearing from the context before collecting
    escaping variables -/
def inferPost (goal : MVarId) (eliminate : LocalDecl → Bool := fun _ => true) :
    MetaM MVarId := do
  goal.withContext do
  let goalTy ← instantiateMVars (← goal.getType)

  -- The goal should be of the form `?post args...`
  let (mvarFn, args) := goalTy.withApp fun f a => (f, a)
  unless mvarFn.isMVar do
    throwError "inferPost: goal should be of the form `?post args...`, got {goalTy}"
  let postMVarId := mvarFn.mvarId!
  let args ← args.mapM instantiateMVars

  -- Try to clear eliminable variables (e.g., display-only vars from progress)
  let mvarLCtx := (← postMVarId.getDecl).lctx
  let toClear ← (← (← getLCtx).getDecls).filterMapM fun decl => do
    if mvarLCtx.contains decl.fvarId then return none
    if ← isProp decl.type then return none  -- keep props: they carry postcondition info
    if eliminate decl then return some decl.fvarId else return none
  let goal ← goal.tryClearMany toClear.toArray

  goal.withContext do
    let lctx ← getLCtx

    -- Collect non-prop free vars not in the mvar's context
    let nonPropEscaping ← (← lctx.getDecls).filterMapM fun decl => do
      if mvarLCtx.contains decl.fvarId then return none
      if ← isProp decl.type then return none
      return some decl.fvarId

    -- Collect relevant props (those mentioning any escaping non-prop variable)
    let relevantFVars := nonPropEscaping
    let relevantProps := (← lctx.getAssumptions).filter fun decl =>
      relevantFVars.any fun fv => decl.type.find? (·.isFVarOf fv) |>.isSome

    -- Build postcondition: fun x₁ ... xₙ => ∃ vars..., x₁ = a₁ ∧ ... ∧ xₙ = aₙ ∧ props
    let argTys ← args.mapM inferType
    let declInfos : Array (Name × Expr) :=
      argTys.mapIdx fun (i : Nat) ty => (Name.mkSimple s!"x{i + 1}", ty)
    let postExpr ← withLocalDeclsDND declInfos fun resExprs => do
      -- Build conjuncts: equalities x₁ = a₁, ..., xₙ = aₙ, then relevant props
      let mut conjuncts : Array Expr := #[]
      for i in [:args.size] do
        conjuncts := conjuncts.push (← mkEq resExprs[i]! args[i]!)
      for p in relevantProps do
        conjuncts := conjuncts.push p.type
      let body ← match conjuncts.toList.reverse with
        | [] => pure (Lean.mkConst ``True)
        | last :: rest => rest.foldlM (fun acc c => mkAppM ``And #[c, acc]) last

      -- Determine which fvars to existentially quantify
      let bodyFVarSet := (collectFVars {} body).fvarSet
      let allEscaping ← (← lctx.getDecls).filterMapM fun decl => do
        if mvarLCtx.contains decl.fvarId then return none
        if nonPropEscaping.contains decl.fvarId then return some decl.fvarId
        if bodyFVarSet.contains decl.fvarId then return some decl.fvarId
        return none

      -- Wrap with existentials over all escaping vars
      let existsBody ← allEscaping.foldrM (fun fVar acc => do
          let pred ← mkLambdaFVars #[.fvar fVar] acc
          mkAppOptM ``Exists #[none, some pred]
        ) body
      mkLambdaFVars resExprs existsBody
    postMVarId.assign postExpr
  return goal

/-- Tactic that infers the postcondition and attempts to prove it with `grind` -/
elab "infer_post" : tactic => do
  let goal ← getMainGoal
  let goal ← inferPost goal
  replaceMainGoal [goal]
  evalTactic (←`(tactic|agrind))

end Progress

end Aeneas
