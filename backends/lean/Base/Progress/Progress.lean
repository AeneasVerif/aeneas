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

inductive TheoremOrLocal where
| Theorem (thName : Name)
| Local (asm : LocalDecl)

/- Type to propagate the errors of `progressWith`.
   We need this because we use the exceptions to backtrack, when trying to
   use the assumptions for instance. When there is actually an error we want
   to propagate to the user, we return it. -/
inductive ProgressError
| Ok
| Error (msg : MessageData)
deriving Inhabited

def progressWith (fnExpr : Expr) (th : TheoremOrLocal) (ids : Array Name)
  (asmTac : TacticM Unit) : TacticM ProgressError := do
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
  let thTy ← do
    match th with
    | .Theorem thName =>
      let thDecl := env.constants.find! thName
      pure thDecl.type
    | .Local asmDecl => pure asmDecl.type
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
  trace[Progress] "Maching `{thBody}` with `{fnExpr}`"
  let ok ← isDefEq thBody fnExpr
  if ¬ ok then throwError "Could not unify the theorem with the target:\n- theorem: {thBody}\n- target: {fnExpr}"
  let mgoal ← Tactic.getMainGoal
  postprocessAppMVars `progress mgoal mvars binders true true
  Term.synthesizeSyntheticMVarsNoPostponing
  let thBody ← instantiateMVars thBody
  trace[Progress] "thBody (after instantiation): {thBody}"
  -- Add the instantiated theorem to the assumptions (we apply it on the metavariables).
  let th ← do
    match th with
    | .Theorem thName => mkAppOptM thName (mvars.map some)
    |  .Local decl => mkAppOptM' (mkFVar decl.fvarId) (mvars.map some)
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
  -- conjunction if there is one. We use the provided `ids` list to name the
  -- introduced variables.
  let res ← splitAllExistsTac thAsm ids.toList fun h ids => do
    -- Split the conjunctions.
    -- For the conjunctions, we split according once to separate the equality `f ... = .ret ...`
    -- from the postcondition, if there is, then continue to split the postcondition if there
    -- are remaining ids.
    let splitEqAndPost (k : Expr → Option Expr → List Name → TacticM ProgressError) : TacticM ProgressError := do
      if ← isConj (← inferType h) then do
        let hName := (← h.fvarId!.getDecl).userName
        let (optId, ids) := listTryPopHead ids
        let optIds := match optId with | none => none | some id => some (hName, id)
        splitConjTac h optIds (fun hEq hPost => k hEq (some hPost) ids)
      else k h none ids
    -- Simplify the target by using the equality and some monad simplifications,
    -- then continue splitting the post-condition
    splitEqAndPost fun hEq hPost ids => do
    trace[Progress] "eq and post:\n{hEq} : {← inferType hEq}\n{hPost}"
    simpAt [] [``Primitives.bind_tc_ret, ``Primitives.bind_tc_fail, ``Primitives.bind_tc_div]
           [hEq.fvarId!] (.targets #[] true)
    -- Clear the equality
    let mgoal ← getMainGoal
    let mgoal ← mgoal.tryClearMany #[hEq.fvarId!]
    setGoals (mgoal :: (← getUnsolvedGoals))
    trace[Progress] "Goal after splitting eq and post and simplifying the target: {mgoal}"
    -- Continue splitting following the ids provided by the user
    if ¬ ids.isEmpty then
      let hPost ←
        match hPost with
        | none => do return (.Error m!"Too many ids provided ({ids}): there is no postcondition to split")
        | some hPost => pure hPost
      let curPostId := (← hPost.fvarId!.getDecl).userName
      let rec splitPost (hPost : Expr) (ids : List Name) : TacticM ProgressError := do
        match ids with
        | [] => pure .Ok -- Stop
        | nid :: ids => do
          -- Split
          if ← isConj hPost then
            splitConjTac hPost (some (nid, curPostId)) (λ _ nhPost => splitPost nhPost ids)
          else return (.Error m!"Too many ids provided ({nid :: ids}) not enough conjuncts to split in the postcondition")
      splitPost hPost ids
    else return .Ok
  match res with
  | .Error _ => return res -- Can we get there? We're using "return"
  | .Ok =>
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
    pure .Ok

-- The array of ids are identifiers to use when introducing fresh variables
def progressAsmsOrLookupTheorem (ids : Array Name) (asmTac : TacticM Unit) : TacticM Unit := do
  withMainContext do
  -- Retrieve the goal
  let mgoal ← Tactic.getMainGoal
  let goalTy ← mgoal.getType
  -- Dive into the goal to lookup the theorem
  let (fName, fLevels, args) ← do
    withPSpec goalTy fun desc =>
    -- TODO: check that no universally quantified variables in the arguments
    pure (desc.fName, desc.fLevels, desc.args)
  -- TODO: this should be in the pspec desc
  let fnExpr := mkAppN (.const fName fLevels) args
  trace[Progress] "Function: {fName}"
  -- Try all the assumptions one by one and if it fails try to lookup a theorem
  let ctx ← Lean.MonadLCtx.getLCtx
  let decls ← ctx.getDecls
  for decl in decls.reverse do
    trace[Progress] "Trying assumption: {decl.userName} : {decl.type}"
    try
      match ← progressWith fnExpr (.Local decl) ids asmTac with
      | .Ok => return ()
      | .Error msg => throwError msg
    catch _ => continue
  -- It failed: try to lookup a theorem
  -- TODO: use a list of theorems, and try them one by one?
  trace[Progress] "No assumption succeeded: trying to lookup a theorem"
  let thName ← do
    match ← pspecAttr.find? fName with
    | none => throwError "Could not find a pspec theorem for {fName}"
    | some thName => pure thName
  trace[Progress] "Lookuped up: {thName}"
  -- Apply the theorem
  match ← progressWith fnExpr (.Theorem thName) ids asmTac with
  | .Ok => return ()
  | .Error msg => throwError msg

syntax progressArgs := ("as" " ⟨ " (ident)+ " ⟩")?

def evalProgress (args : TSyntax `Progress.progressArgs) : TacticM Unit := do
  let args := args.raw
  -- Process the arguments to retrieve the identifiers to use
  trace[Progress] "Progressing arguments: {args}"
  let args := args.getArgs
  let ids :=
    if args.size > 0 then
      let args := (args.get! 0).getArgs
      let args := (args.get! 2).getArgs
      args.map Syntax.getId
    else #[]
  trace[Progress] "Ids: {ids}"
  --if args[0] ≠ some "as" then throwError "Invalid syntax: should be: `progress as ⟨ ... ⟩`"
  progressAsmsOrLookupTheorem ids (firstTac [assumptionTac, Arith.scalarTac])

elab "progress" args:progressArgs : tactic =>
  evalProgress args

namespace Test
  open Primitives

  set_option trace.Progress true
  set_option pp.rawOnError true

  @[pspec]
  theorem vec_index_test2 (α : Type u) (v: Vec α) (i: Usize) (h: i.val < v.val.length) :
    ∃ (x: α), v.index α i = .ret x := by
      progress as ⟨ x ⟩
      simp

  set_option trace.Progress false

end Test

end Progress
