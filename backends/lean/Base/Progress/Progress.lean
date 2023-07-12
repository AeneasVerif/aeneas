import Lean
import Base.Arith
import Base.Progress.Base

namespace Progress

open Lean Elab Term Meta Tactic
open Utils

namespace Test
  open Primitives

  set_option trace.Progress true

  @[pspec]
  theorem vec_index_test (α : Type u) (v: Vec α) (i: Usize) (h: i.val < v.val.length) :
    ∃ x, v.index α i = .ret x := by
      apply
      sorry

  #eval pspecAttr.find? ``Primitives.Vec.index
end Test

def progressLookupTheorem (asmTac : TacticM Unit) : TacticM Unit := do
  withMainContext do
  -- Retrieve the goal
  let mgoal ← Tactic.getMainGoal
  let goalTy ← mgoal.getType
  -- Dive into the goal to lookup the theorem
  let (fName, fLevels, args) ← do
    withPSpec goalTy fun desc =>
    -- TODO: check that no universally quantified variables in the arguments
    pure (desc.fName, desc.fLevels, desc.args)
  -- TODO: also try the assumptions
  trace[Progress] "Function: {fName}"
  -- TODO: use a list of theorems, and try them one by one?
  let thName ← do
    match ← pspecAttr.find? fName with
    | none => throwError "Could not find a pspec theorem for {fName}"
    | some thName => pure thName
  trace[Progress] "Lookuped up: {thName}"
  /- Apply the theorem
     We try to match the theorem with the goal
     In order to do so, we introduce meta-variables for all the parameters
     (i.e., quantified variables and assumpions), and unify those with the goal.
     Remark: we do not introduce meta-variables for the quantified variables
     which don't appear in the function arguments (we want to let them
     quantified).
     We also make sure that all the meta variables which appear in the
     function arguments have been instantiated
   -/  
  let env ← getEnv
  let thDecl := env.constants.find! thName
  let thTy := thDecl.type
  -- TODO: the tactic fails if we uncomment withNewMCtxDepth
  -- withNewMCtxDepth do
  let (mvars, binders, thExBody) ← forallMetaTelescope thTy
  -- Introduce the existentially quantified variables and the post-condition
  -- in the context
  let thBody ←
    existsTelescope thExBody fun _evars thBody => do
    let (thBody, _) ← destEq thBody
    -- There shouldn't be any existential variables in thBody
    pure thBody
  -- Match the body with the target
  let target := mkAppN (.const fName fLevels) args
  trace[Progress] "mvars:\n{mvars.map Expr.mvarId!}"
  trace[Progress] "thBody: {thBody}"
  trace[Progress] "target: {target}"
  let ok ← isDefEq thBody target
  if ¬ ok then throwError "Could not unify the theorem with the target:\n- theorem: {thBody}\n- target: {target}"
  postprocessAppMVars `progress mgoal mvars binders true true
  Term.synthesizeSyntheticMVarsNoPostponing
  let thBody ← instantiateMVars thBody
  trace[Progress] "thBody (after instantiation): {thBody}"
  -- Add the instantiated theorem to the assumptions (we apply it on the metavariables).
  let th ← mkAppOptM thName (mvars.map some)
  let asmName ← mkFreshUserName `h
  let thTy ← inferType th
  let thAsm ← Utils.addDeclTac asmName th thTy (asLet := false)
  withMainContext do -- The context changed - TODO: remove once addDeclTac is updated
  let ngoal ← getMainGoal
  trace[Progress] "current goal: {ngoal}"
  trace[Progress] "current goal: {← ngoal.isAssigned}"
  -- The assumption should be of the shape:
  -- `∃ x1 ... xn, f args = ... ∧ ...`
  -- We introduce the existentially quantified variables and split the top-most
  -- conjunction if there is one
  splitAllExistsTac thAsm fun h => do
    -- Split the conjunction
    let splitConj (k : Expr → TacticM Unit) : TacticM Unit := do
      if ← isConj (← inferType h) then
        splitConjTac h (fun h _ => k h)
      else k h
    -- Simplify the target by using the equality
    splitConj fun h => do
    simpAt [] [] [h.fvarId!] (.targets #[] true)
    -- Clear the equality
    let mgoal ← getMainGoal
    let mgoal ← mgoal.tryClearMany #[h.fvarId!]
    setGoals (mgoal :: (← getUnsolvedGoals))
  -- Update the set of goals
  let curGoals ← getUnsolvedGoals
  let newGoals := mvars.map Expr.mvarId!
  let newGoals ← newGoals.filterM fun mvar => not <$> mvar.isAssigned
  trace[Progress] "new goals: {newGoals}"
  setGoals newGoals.toList
  allGoals asmTac
  let newGoals ← getUnsolvedGoals
  setGoals (newGoals ++ curGoals)
  -- 
  pure ()

elab "progress" : tactic => do
  progressLookupTheorem (firstTac [assumptionTac, Arith.scalarTac])

namespace Test
  open Primitives

  set_option trace.Progress true

  @[pspec]
  theorem vec_index_test2 (α : Type u) (v: Vec α) (i: Usize) (h: i.val < v.val.length) :
    ∃ (x: α), v.index α i = .ret x := by
      progress
      simp

  set_option trace.Progress false

end Test

end Progress
