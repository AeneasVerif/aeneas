module
public import Aeneas.Tactic.Step.PrepareIntroOutputs
public section

namespace Aeneas.Step

open Lean Elab Term Meta Tactic

/-- Read the pattern with which the program destructures the output of the call from the
premise the mono or bind rule of `ispec`/`dispec` leaves behind.

- bind: the premise is `∀ v, ispec (Qm v ∗ F) (k v) Q`, and we read the pattern from the
  input of the continuation `k`.
- mono: the premise is `P ⊢ Pm ∗ (Qm -∗+ Q)`, and we read the pattern from the input of
  the caller's postcondition `Q`. -/
meta def getIspecOutputTree (goalTy : Expr) : MetaM NameTree := do
  let goalTy := (← instantiateMVars goalTy).consumeMData
  if goalTy.isForall then
    forallBoundedTelescope goalTy (some 1) fun xs body => do
      let body := body.consumeMData
      if body.isAppOfArity ``Std.WP.ispec 4 || body.isAppOfArity ``Std.WP.dispec 4 then
        getContInput (← mkLambdaFVars xs body.getAppArgs[2]!).eta
      else
        return .leaf none
  else
    match goalTy.find? (·.isAppOfArity ``SepLogic.postWand 3) with
    | some wand => getContInput wand.getAppArgs[2]!
    | none => return .leaf none

/-- Destructure an introduced output according to the pattern `tree`, returning the leaves. -/
meta partial def destructureOutput {α} (goal : MVarId) (fv : FVarId) (tree : BTree α) :
    MetaM (Array FVarId × MVarId) := do
  match tree with
  | .leaf _ => return (#[fv], goal)
  | .pair l r =>
    let #[subgoal] ← goal.cases fv
      | throwError "destructureOutput: expected a single constructor"
    let #[left, right] := subgoal.fields
      | throwError "destructureOutput: expected a pair"
    let (lFVs, goal) ← destructureOutput subgoal.mvarId left.fvarId! l
    let (rFVs, goal) ← destructureOutput goal right.fvarId! r
    return (lFVs ++ rFVs, goal)

/-- Goal preparation shared by `ispec` and `dispec`.

`Std.WP.introIspec` extracts the pure facts and existentials of the premise into the
context. We revert them, then replace the output which is now the leading binder of
the goal with one binder per component of the pattern the program destructures it with. -/
meta def prepareIntroIspec : PrepareIntroOutputs := do
  withTraceNode `Step (fun _ => pure m!"prepareIntroIspec") do
  withMainContext do
  let tree ← getIspecOutputTree (← getMainTarget)
  let last? := (← getLCtx).lastDecl.map LocalDecl.fvarId
  Std.WP.introIspec
  let goal ← match ← getUnsolvedGoals with
    | [] => return 0
    | [goal] => pure goal
    | _ => throwError "prepareIntroIspec: expected a single goal"
  let goal ← match last? with
    | some last => Prod.snd <$> goal.revertAfter last
    | none => Prod.snd <$> goal.revert (← goal.withContext do pure (← getLCtx).getFVarIds)
  setGoals [goal]
  let goalTy ← instantiateMVars (← goal.getType)
  let .forallE name domain body info := goalTy.consumeMData | return 0
  if ← isProp domain then return 0
  if (← withReducible <| whnf domain).isConstOf ``PUnit then
    let newGoal ← mkFreshExprSyntheticOpaqueMVar (body.instantiate1 (mkConst ``Unit.unit))
    goal.assign (← mkAppM ``Iff.mpr
      #[← mkAppM ``forall_punit #[.lam name domain body info], newGoal])
    setGoals [newGoal.mvarId!]
    return 0
  let (fv, goal) ← goal.intro1
  let (leaves, goal) ← destructureOutput goal fv tree
  setGoals [goal]
  if leaves.size > 1 then
    Simp.dsimpAt true { implicitDefEqProofs := true, failIfUnchanged := false, iota := false }
      {} (.targets #[] true)
  let goal ← getMainGoal
  let (_, goal) ← goal.revert leaves (preserveOrder := true)
  setGoals [goal]
  return leaves.size

end Aeneas.Step
