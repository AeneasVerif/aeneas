import Aeneas.Tactic.Step.Step
import AeneasMeta.Split
open Lean Meta Elab Tactic

namespace Aeneas

/-- Given a goal of the shape `spec (match ... with ...) post`, perform a case split
and introduce an equality. -/
def esplitMatchAtSpec (h : Name) (names : Option (List (List (Option Name)))) :
  TacticM (List (Array FVarId × FVarId × MVarId)) := do
  withTraceNode `Utils (fun _ => do pure m!"esplitMatchAtSpec") do
  focus do withMainContext do
  let tgt ← getMainTarget
  tgt.consumeMData.withApp fun spec? args => do
  if ¬ (spec?.isConstOf ``Std.WP.spec) ∨ args.size ≠ 3 then throwError "Not a valid spec goal"
  let prog := args[1]!
  -- Check that we have a matcher
  let some ma ← Meta.matchMatcherApp? prog (alsoCasesOn := true)
    | throwError "not a matcher: {prog}"
  if ma.discrs.size ≠ 1 then throwError "Don't know what to do with > 1 scrutinees: discrs"
  let matcherName := ma.matcherName
  let scrut := ma.discrs[0]!
  -- Compute the names to use by looking at the branches
  let names ← do
    match names with
    | none =>
      ma.alts.toList.mapM fun alt => do
      lambdaTelescope alt.consumeMData fun args _ => do
      args.toList.mapM fun arg => do
      pure (some (← arg.fvarId!.getDecl).userName)
    | some names => pure names
  -- Split
  let goals ← Split.esplitCasesOn true scrut matcherName h names
  trace[Utils] "after esplitCasesOn:\n{goals.map fun (_, _, g) => g}"
  -- Simplify the goal with the equality we just introduced
  let goals ← goals.filterMapM fun (vars, h, goal) => do
    goal.withContext do
    setGoals [goal]
    trace[Goal] "About to simplify the goal (with h: {← h.getType}):\n{goal}"
    match ← Simp.simpAt true {} {hypsToUse := #[h]} (.targets #[] true) with
    | none => pure none
    | some _ => pure (some (vars, h, ← getMainGoal))
  --
  pure goals

def esplitMatchAtSpecTac (h : Name) (names : Option (List (List (Option Name)))) :
  TacticM (List (MVarId)) := do
  (← esplitMatchAtSpec h names).mapM fun (_, _, g) => pure g

elab "spec_split": tactic => do setGoals (← esplitMatchAtSpecTac (← mkFreshUserName `h) (some []))
elab "spec_split" "as" h:ident : tactic => do setGoals (← esplitMatchAtSpecTac h.getId (some []))

example {α} (x : Option α) :
  Std.WP.spec (match x with | none => .ok 0 | some _ => .ok 1) (fun _ => True) := by
  spec_split <;> simp

theorem dite_true: (dite True t e) = t (by simp) := by simp
theorem dite_false : (dite False t e) = e (by simp) := by simp

/-- Split an `if then else` in a spec predicate:
`⊢ spec (if ... then ... else ...) post`
-/
def esplitIteAtSpec (h : Name) : TacticM (List (FVarId × MVarId)) := do
  focus do withMainContext do
  let tgt ← getMainTarget
  tgt.consumeMData.withApp fun spec? args => do
  if ¬ (spec?.isConstOf ``Std.WP.spec) ∨ args.size ≠ 3 then throwError "Not a valid spec goal"
  let prog := args[1]!
  -- Check that we have an if then else
  prog.withApp fun ite? args => do
  trace[Utils] "ite?: {ite?}, args: {args}"
  if ¬ ite?.isConstOf ``ite ∧ ¬ ite?.isConstOf ``dite then throwError "Not an if then else"
  if args.size ≠ 5 then throwError "Incorrect number of arguments"
  -- `if then else` expressions receive a decidable `Prop` as input
  let prop := args[1]!
  let decInst := args[2]!
  let thm ← mkAppOptM ``Decidable.byCases #[prop, tgt, decInst]
  let thmTy ← inferType thm
  -- Apply the theorem
  let (goals, _, _) ← forallMetaTelescope thmTy
  let thm := mkAppN thm goals
  let goal ← getMainGoal
  goal.assign thm
  let goals := goals.toList.map Expr.mvarId!
  -- Introduce the equality and simplify
  let goals ← goals.filterMapM fun goal => do
    let (h, goal) ← goal.intro h
    setGoals [goal]
    let args : Simp.SimpArgs := {
      hypsToUse := #[h],
      addSimpThms := #[``Bool.false_eq_true, ``ite_false, ``ite_true, ``dite_true, ``dite_false] }
    match ← Simp.simpAt true {} args (.targets #[] true) with
    | none => pure none
    | some _ => pure (some (h, ← getMainGoal))
  --
  setGoals (goals.map Prod.snd)
  pure goals

def esplitIteAtSpecTac (h : Name) : TacticM (List MVarId) := do
  pure ((← esplitIteAtSpec h).map Prod.snd)

elab "spec_split_if": tactic => do setGoals (← esplitIteAtSpecTac (← mkFreshUserName `h))
elab "spec_split_if" "as" h:ident : tactic => do setGoals (← esplitIteAtSpecTac h.getId)

/--
error: unsolved goals
case h1
b : Bool
h : b = true
⊢ Std.Result.ok 0 ⦃ x✝ => True ⦄

case h2
b : Bool
h : ¬b = true
⊢ Std.Result.ok 1 ⦃ x✝ => True ⦄
-/
#guard_msgs in
example (b : Bool) : Std.WP.spec (if b then .ok 0 else .ok 1) (fun _ => True) := by
  spec_split_if as h

/--
error: unsolved goals
case h1
b : Bool
h : b = true
⊢ Std.Result.ok 0 ⦃ x✝ => True ⦄

case h2
b : Bool
h : ¬b = true
⊢ Std.Result.ok 1 ⦃ x✝ => True ⦄
-/
#guard_msgs in
example (b : Bool) : Std.WP.spec (if h: b then .ok 0 else .ok 1) (fun _ => True) := by
  spec_split_if as h

/-- Given a goal of the shape `spec (match ... with ...) post` or `spec (if ... then ... else ...)`,
perform a case split. -/
def esplitAtSpec (h : Name) (names : Option (List (List (Option Name)))) : TacticM (List (Array FVarId × FVarId × MVarId)) := do
  withTraceNode `Utils (fun _ => do pure m!"esplitAtSpec") do
  focus do withMainContext do
  let tgt ← getMainTarget
  tgt.consumeMData.withApp fun spec? args => do
  if ¬ (spec?.isConstOf ``Std.WP.spec) ∨ args.size ≠ 3 then throwError "Not a valid spec goal"
  let prog := args[1]!
  -- Check whether we have a matcher
  let ma ← Meta.matchMatcherApp? prog (alsoCasesOn := true)
  if ma.isSome
  then
    trace[Utils] "splitting a match"
    esplitMatchAtSpec h names
  else
    trace[Utils] "splitting an if then else"
    pure ((← esplitIteAtSpec h).map fun (h, g) => (#[], h, g))

def esplitAtSpecTac (h : Name) : TacticM (List MVarId) := do
  pure ((← esplitAtSpec h (some [])).map fun (_, _, g) => g)

elab "spec_split": tactic => do setGoals (← esplitAtSpecTac (← mkFreshUserName `h))
elab "spec_split" "as" h:ident : tactic => do setGoals (← esplitAtSpecTac h.getId)

namespace Bifurcation

/-- Expression on which a branch depends -/
structure Discr where
  toExpr: Expr
  /-- Name under which to bind the discriminant equation, if provided -/
  name?: Option Name := none
  deriving Repr

instance: ToMessageData Discr where
  toMessageData discr :=
    let nameMD := if let some name := discr.name? then m!"(name {name }) " else ""
    m!"(discr {nameMD}{discr.toExpr})"

/-- One possible branch in a bifurcation -/
structure Branch where
  /-- The branch as a function -/
  toExpr: Expr

  /-- The number of arguments the bifurcation is
      expected to provide. -/
  numArgs: Nat

  deriving Repr

instance: ToMessageData Branch where
  toMessageData br := m!"(branch (numArgs {br.numArgs}){br.toExpr}) "

/-- The kind of bifurcation -/
inductive Kind where
  /-- An `if-then-else` bifurcation -/
  | ite
  /-- A dependent `if-then-else` bifurcation -/
  | dite
  /-- A matcher or cases bifurcation, of name `name` -/
  | matcher (name: Name)
  deriving Repr

instance: ToString Kind where
  toString
  | .ite => "ite"
  | .dite => "dite"
  | .matcher name => s!"matcher {name}"

instance: ToMessageData Kind where toMessageData k := toString k

/-- Rough equivalent of `Lean.Meta.MatcherApp`, but which also includes if-then-else -/
structure Info where
  /-- The kind of bifurcation -/
  kind: Kind

  /-- The information on discriminants of the bifurcation -/
  discrs: Array Discr

  /-- The information on the branches of the bifurcation -/
  branches: Array Branch

  /-- The name of the function which implements the matcher -/
  matcher: Name

  /-- The scrutinee -/
  scrut : Expr

  /-- The motive of the bifurcation -/
  motive: Expr

  /-- The universe levels of the bifurcation -/
  uLevels: List Lean.Level

  params: Array Expr
  deriving Repr

instance: ToMessageData Info where
  toMessageData
  | {kind, discrs, branches, ..} =>
    let discr := MessageData.ofArray <| discrs.map (ToMessageData.toMessageData)
    let branches := MessageData.ofArray <| branches.map (ToMessageData.toMessageData)
    m!"(info {kind} {discr} {branches})"

def Info.ofExpr(e: Expr): MetaM (Option Info) := do
  let e := e.consumeMData
  if e.isIte || e.isDIte then
    let kind := if e.isIte then .ite else .dite
    let e ← deltaExpand e (fun n => n == ``ite || n == ``dite)
    let .const ``Decidable.casesOn uLevels := e.getAppFn
      | throwError "Expected ``Decidable.casesOn, found {←ppExpr e.getAppFn}"
    let #[prop, motive, dec, brFalse, brTrue] := e.getAppArgs
      | throwError "Wrong number of parameters for {e.getAppFn}: {e.getAppArgs.size} [{e.getAppArgs}]"
    let name? ← if e.isDIte
      then some <$> Utils.lambdaOne brFalse fun x _ => x.fvarId!.getUserName
      else pure none
    return some {
      kind,
      discrs := #[{ toExpr := dec, name?}]
      branches  := #[
        { toExpr := brTrue,  numArgs := 1, },
        { toExpr := brFalse, numArgs := 1, }
      ]
      matcher := ``Decidable.casesOn,
      uLevels,
      params  := #[prop]
      motive,
      scrut := dec,
    }
  else if let some ma ← Meta.matchMatcherApp? e (alsoCasesOn := true) then
    if h: ma.discrs.size = 1 then
      return some {
        kind := .matcher ma.matcherName
        discrs := ma.discrs.zip ma.discrInfos
          |>.map fun (toExpr, discrInfo) => {toExpr, name? := discrInfo.hName?}
        branches := ma.alts.zip ma.altNumParams
          |>.map fun (toExpr, numArgs) => {toExpr, numArgs}
        matcher := ma.matcherName,
        motive := ma.motive,
        uLevels := ma.matcherLevels.toList,
        params := ma.params,
        scrut := ma.discrs[0]
      }
    else return none
  else return none

def Info.toExpr(info: Info): Expr :=
  let fn := Expr.const info.matcher info.uLevels
  let args := info.params ++
    #[info.motive] ++
    info.discrs.map (·.toExpr) ++
    info.branches.map (·.toExpr)
  mkAppN fn args

end Bifurcation

namespace StepStar

abbrev traceGoalWithNode := Step.traceGoalWithNode

structure Config where
  stepConfig : Step.Config
  /-- We need the original configuration syntax to generate the proof script -/
  configSyntax : Option (TSyntax `Lean.Parser.Tactic.optConfig)
  preconditionTac: Option Syntax.Tactic := none
  /-- Should we use the special syntax `let* ⟨ ...⟩ ← ...` or the more standard syntax `step with ... as ⟨ ... ⟩`? -/
  prettyPrintedStep : Bool := true
  useCase : Bool := false
  useRename : Bool := true

inductive TaskOrDone α where
| task (x : Task α)
| done (x : α)

def TaskOrDone.get (x : TaskOrDone α) : α :=
  match x with
  | .task x => x.get
  | .done x => x

def TaskOrDone.mk (x : α) : TaskOrDone α := .done x

inductive BranchArg where
| case (stx : TSyntax `Lean.Parser.Tactic.caseArg)
| rename (names : Array Name)
| empty

inductive Script where
| split (splitStx : Syntax.Tactic) (branches : Array (BranchArg × Script))
| tacs (tacs : Array (TaskOrDone (Option Syntax.Tactic)))
| seq (s0 s1 : Script)

structure Info where
  script: Script := (.tacs #[])
  -- The unassigned meta-variables that are not propositions
  unassignedVars : Array MVarId := #[]
  -- TODO: this type is overly complex
  subgoals: Array (MVarId × Option (TaskOrDone (Option Expr))) := #[]

structure Result where
  script: Script
  unassignedVars : Array MVarId
  subgoals: Array MVarId

instance: Append Info where
  append inf1 inf2 := {
    script := .seq inf1.script inf2.script,
    subgoals := inf1.subgoals ++ inf2.subgoals,
    unassignedVars := inf1.unassignedVars ++ inf2.unassignedVars,
  }

def nameToBinderIdent (n : Name) : TSyntax `Lean.binderIdent :=
  if n.isInternalDetail
  then mkNode ``Lean.binderIdent #[mkHole mkNullNode]
  else mkNode ``Lean.binderIdent #[mkIdent n]

/-- Convert the script into syntax.
    This is a blocking operation: it waits for all the sub-components of the script to be generated.
-/
partial def Script.toSyntax (script : Script) : MetaM (Array Syntax.Tactic) := do
  match script with
  | .split splitStx branches =>
    let branches ← branches.mapM fun (caseArgs, branch) => do
      let branch ← branch.toSyntax
      match caseArgs with
      | .case caseArgs => `(tactic| case $caseArgs => $branch*) -- Remark: we can also use `case'`
      | .rename names =>
        let branch ← do
          if names.all Name.isInternalDetail then pure branch
          else
            let names := names.map nameToBinderIdent
            let rename ← `(tactic|rename_i $(names)*)
            pure (#[rename] ++ branch)
        `(tactic| · $branch*) -- Remark: we can also use `case'`
      | .empty => `(tactic|· $branch*)
    pure (#[splitStx] ++ branches)
  | .tacs tactics => pure (tactics.filterMap TaskOrDone.get)
  | .seq s0 s1 =>
    let s0 ← toSyntax s0
    let s1 ← toSyntax s1
    pure (s0 ++ s1)

attribute [step_simps] Aeneas.Std.bind_assoc_eq
attribute [step_simps] Function.uncurry_apply_pair

inductive TargetKind where
| bind (fn : Name)
| switch (info : Bifurcation.Info)
| result
| unknown

/- Smaller helper which we use to check in which situation we are -/
def analyzeTarget : TacticM TargetKind := do
  withTraceNode `Step (fun _ => do pure m!"analyzeTarget") do
  try
    let goalTy ← (← getMainGoal).getType
    -- Dive into the `spec program post`
    goalTy.consumeMData.withApp fun spec? args => do
    if h: spec?.isConstOf ``Std.WP.spec ∧ args.size = 3 then
      trace[Step] "application of `spec` with arity 3"
      let program := args[1]
      -- Check if this is a bind
      let e ← Utils.normalizeLetBindings program
      if let .const ``Bind.bind .. := e.getAppFn then
        let #[_m, _self, _α, _β, _value, cont] := e.getAppArgs
          | throwError "Expected bind to have 4 arguments, found {← e.getAppArgs.mapM (liftM ∘ ppExpr)}"
        Utils.lambdaOne cont fun x _ => do
          let name ← x.fvarId!.getUserName
          pure (.bind name)
      else if let .some bfInfo ← Bifurcation.Info.ofExpr e then
        pure (.switch bfInfo)
      else
        pure .result
    else
      trace[Step] "not an application of `spec` with arity 3"
      pure .result
  catch _ =>
    trace[Step] "exception caught"
    pure .unknown

partial def evalStepStar (cfg: Config) (fuel : Option Nat) : TacticM Result :=
  withMainContext do focus do
  withTraceNode `Step (fun _ => do pure m!"evalStepStar") do
  -- Initialize the step state (grind threading)
  let initState : Step.StepState ←
    if cfg.stepConfig.threadGrindState then
      let mvarId ← getMainGoal
      let gs ← Step.initStepGrindState cfg.stepConfig mvarId
      /- Check if grind detected a contradiction during initialization.
         If so, close the main goal immediately. -/
      if let some falseProof := gs.contradictionProof? then
        trace[Step] "grind detected contradiction during initialization — closing goal"
        Step.closeGoalWithFalse mvarId falseProof
        setGoals []
        let agrindStx ← `(tactic| agrind)
        return { script := .tacs #[.done (some agrindStx)], unassignedVars := #[], subgoals := #[] }
      pure { grindState? := some gs }
    else pure {}
  -- Simplify the target
  let (info, mvarId) ← simplifyTarget
  -- Continue
  match mvarId with
  | some _ =>
    let info' ← traverseProgram cfg fuel initState
    let info := info ++ info'
    -- Wait for the asynchronous execution to finish
    withTraceNode `Step (fun _ => do pure m!"filtering subgoals") do
    let mut sgs := #[]
    for (mvarId, proof) in info.subgoals do
      match proof with
      | none => sgs := sgs.push mvarId
      | some proof =>
        match proof.get with
        | none => sgs := sgs.push mvarId
        | some proof =>
          -- Introduce an auxiliary theorem (TODO: is this really a good idea?)
          let declName? ← Term.getDeclName?
          mvarId.withContext do
          let e ← mkAuxTheorem (← mvarId.getType) proof (zetaDelta := true)
          mvarId.assign proof
    setGoals (info.unassignedVars.toList ++ sgs.toList)
    pure { script := info.script, unassignedVars := info.unassignedVars, subgoals := sgs }
  | none => pure { script := info.script, unassignedVars := #[], subgoals := #[] }

where
  simplifyTarget : TacticM (Info × Option MVarId) := do
    withTraceNode `Step (fun _ => do pure m!"simplifyTarget") do
    traceGoalWithNode "about to simplify goal"
    let mvarId0 ← getMainGoal
    let r ← Simp.simpAt (simpOnly := true)
      { maxDischargeDepth := 1, failIfUnchanged := false}
      {simpThms := #[← Step.stepSimpExt.getTheorems]}
      (.targets #[] true)
    /- We may have proven the goal already -/
    let tac : Array Syntax.Tactic ← do
      let genSimp : Bool ← do
        if r.isNone then pure true
        else do
          pure ((← getMainGoal) != mvarId0)
      if genSimp then
        let step_simps ← `(Parser.Tactic.simpLemma| $(mkIdent `step_simps):term)
        let tac ← `(tactic|simp only [$step_simps])
        pure #[TaskOrDone.mk (some tac)]
      else pure #[]
    let info : Info := ⟨ .tacs tac, #[], #[] ⟩
    if r.isSome then traceGoalWithNode "after simplification"
    else trace[Step] "goal proved"
    let goal ← do if r.isSome then pure (some (← getMainGoal)) else pure none
    pure (info, goal)

  traverseProgram (cfg : Config) (fuel : Option Nat) (ss : Step.StepState) : TacticM Info := do
    withMainContext do
    withTraceNode `Step (fun _ => do pure m!"traverseProgram") do
    traceGoalWithNode "current goal"
    -- Check if there remains fuel
    let fuel ←
      match fuel with
      | none => pure none
      | some fuel =>
        if fuel = 0 then return { script := .tacs #[], unassignedVars := #[], subgoals := #[(← getMainGoal, none)] }
        else pure (some (fuel - 1))
    let targetKind ← analyzeTarget
    match targetKind with
    | .bind varName => do
      let names := if varName.hasMacroScopes then #[] else #[some varName]
      let (info, mainGoalAndState) ← onBind cfg names ss
      /- Continue, if necessary -/
      match mainGoalAndState with
      | none =>
        -- Stop
        trace[Step] "stop"
        return info
      | some (mainGoal, ss) =>
        /- Check if grind detected a contradiction during the step state update.
           This can happen when the new hypotheses introduced by the step contradict
           existing ones. Close the goal ourselves with the saved proof. -/
        if let some falseProof := ss.contradictionProof? then
          trace[Step] "grind detected contradiction after let-binding step — closing goal"
          Step.closeGoalWithFalse mainGoal falseProof
          let agrindStx ← `(tactic| agrind)
          return (info ++ { script := .tacs #[.done (some agrindStx)], unassignedVars := #[], subgoals := #[] })
        setGoals [mainGoal]
        /- Check if there are unassigned meta-variables which are not `Prop`:
           if it is the case it means there are meta-variables we could not infer, so we stop -/
        if info.unassignedVars.isEmpty then
          let restInfo ← traverseProgram cfg fuel ss
          return (info ++ restInfo)
        else
          trace[Step] "Found unassigned meta-variables of type ≠ Prop: stopping"
          let info' : Info ← pure
            { script := .tacs #[.done (← `(tactic| sorry))],
              unassignedVars := #[],
              subgoals := #[(mainGoal, none)] }
          pure (info ++ info')
    | .switch bfInfo => do
      let contsTaggedVals ←
        bfInfo.branches.mapM fun br => do
          Utils.lambdaTelescopeN br.toExpr br.numArgs fun xs _ => do
            let names ← xs.mapM (·.fvarId!.getUserName)
            return names
      trace[Step] "Match over scrutinee: {bfInfo.scrut}"
      let (branchGoals, mkStx) ← onMatch cfg bfInfo contsTaggedVals
      withTraceNode `Step (fun _ => do pure m!"exploring branches") do
      /- Continue exploring from the subgoals.
         Each branch starts from the same state (branches are independent).
         We update the grind state for each branch to internalize the hypotheses
         introduced by `esplitAtSpec` (case variables, discriminant equality). -/
      let branchInfos ← branchGoals.mapM fun mainGoal => do
        setGoals [mainGoal]
        let ss ← ss.update cfg.stepConfig mainGoal
        /- Check if grind detected a contradiction during hypothesis internalization.
           This happens when a branch's hypotheses contradict the pre-split context
           (e.g., `h : a = b` from before the split and `h' : ¬a = b` from the branch). -/
        if let some falseProof := ss.contradictionProof? then
          trace[Step] "grind detected contradiction in branch — closing goal"
          Step.closeGoalWithFalse mainGoal falseProof
          let agrindStx ← `(tactic| agrind)
          pure { script := .tacs #[.done (some agrindStx)], unassignedVars := #[], subgoals := #[] }
        else
          traverseProgram cfg fuel ss
      /- Put everything together — after branches, state is discarded (we can't merge
         divergent e-graphs). Use the pre-branch state going forward. -/
      mkStx branchInfos
    | .result => do
      let (info, mainGoal) ← onResult cfg ss
      let mainGoal ← match mainGoal with
        | none => pure #[]
        | some mainGoal => pure #[(mainGoal, none)]
      pure { info with subgoals := info.subgoals ++ mainGoal }
    | .unknown => do
      trace[Step] "don't know what to do: it may be a terminal goal, attempting to solve it with grind"
      let (info, mainGoal) ← onResult cfg ss
      let mainGoal ← match mainGoal with
        | none => pure #[]
        | some mainGoal => pure #[(mainGoal, none)]
      pure { info with subgoals := info.subgoals ++ mainGoal }

  onResult (cfg : Config) (ss : Step.StepState) : TacticM (Info × Option MVarId) := do
    withTraceNode `Step (fun _ => pure m!"onResult") do
    /- If we encounter `(do f a)` we process it as if it were `(do let res ← f a; return res)`
       since (id = (· >>= pure)) and when we desugar the do block we have that

                            (do f a) == f a
                                     == (f a) >>= pure
                                     == (do let res ← f a; return res)

       We known in advance the result of processing `return res`, which is to do nothing.
       This allows us to prevent code duplication with the `onBind` function. -/
    let names ← Step.getPostNamesFromGoal
    let (info, mainGoalAndState) ← onBind cfg names ss
    match mainGoalAndState with
    | none =>
      trace[Step] "done"
      pure (info, none)
    | some (mvarId, _) =>
      let (info', mvarId) ← onFinish cfg mvarId
      pure (info ++ info', mvarId)

  onFinish (cfg : Config) (mvarId : MVarId) : TacticM (Info × Option MVarId) := do
    withTraceNode `Step (fun _ => pure m!"onFinish") do
    setGoals [mvarId]
    traceGoalWithNode "goal"
    /- Simplify a bit -/
    let (info, mvarId) ← simplifyTarget
    match mvarId with
    | none => pure (info, mvarId)
    | some mvarId =>
      setGoals [mvarId]
      /- Attempt to finish with a tactic -/
      -- TODO: don't use syntax
      -- TODO: use global options
      let grindTac : TacticM Unit :=
        Step.evalAGrindWithPreprocess cfg.stepConfig.withGroundSimprocs cfg.stepConfig.toGrindConfig cfg.stepConfig.nla
      -- TODO: add the tactic given by the user
      let tacStx : IO.Promise Syntax.Tactic ← IO.Promise.new
      let rec tryFinish (tacl : List (String × Syntax.Tactic × TacticM Unit)) : TacticM Unit := do
        match tacl with
        | [] =>
          trace[Step] "could not prove the goal: inserting a sorry"
          tacStx.resolve (← `(tactic| sorry))
        | (name, stx, tac) :: tacl =>
          let stx : Option Syntax.Tactic ←
            withTraceNode `Step (fun _ => do pure m!"Attempting to solve finish goal with `{name}`:\n{← getMainGoal}") do
            try
              tac
              -- Check that there are no remaining goals
              let gl ← Tactic.getUnsolvedGoals
              if ¬ gl.isEmpty then throwError "tactic failed"
              else pure stx
            catch _ => pure none
          match stx with
          | some stx =>
            trace[Step] "goal solved"
            tacStx.resolve stx
          | none => tryFinish tacl
      let info' ← do
        if cfg.stepConfig.async then
          let proof ← Async.asyncRunTactic (tryFinish [("grind", ← `(tactic| agrind), grindTac)])
          let proof := proof.result?.map (fun x => match x with | none | some none => none | some (some x) => some x)
          let info' : Info ← pure
            { script := .tacs #[.task tacStx.result?],
              unassignedVars := #[],
              subgoals := #[(mvarId, some (TaskOrDone.task proof))] }
          pure info'
        else
          tryFinish [("grind", ← `(tactic| agrind), grindTac)]
          let info' : Info ← pure
            { script := .tacs #[.task tacStx.result?],
              unassignedVars := #[],
              subgoals := #[(mvarId, none)] }
          pure info'
      pure (info ++ info', none)

  onBind (cfg : Config) (names : Array (Option Name)) (ss : Step.StepState) : TacticM (Info × Option (MVarId × Step.StepState)) := do
    withTraceNode `Step (fun _ => pure m!"onBind ({names})") do
    let postsBasename := names[0]?.join
    if let some res ← tryStep cfg names postsBasename ss then
      let {usedTheorem, unassignedVars, preconditions, mainGoal } := res
      withTraceNode `Step (fun _ => pure m!"step succeeded") do
      match mainGoal with
      | none => trace[Step] "Main goal solved"
      | some goal =>
        withTraceNode `Step (fun _ => pure m!"New main goal:") do
        trace[Step] "{goal.goal}"
      withTraceNode `Step (fun _ => pure m!"all preconditions") do trace[Step] "All preconditions:\n{preconditions.map Prod.fst}"
      /- Compute ids for the tactic script from the introduced variables -/
      let ids : Array (TSyntax ``Lean.binderIdent) :=
        match mainGoal with
        | none => #[]
        | some mainGoal =>
          mainGoal.outputs.map fun o =>
            match o.name? with
            | some n => mkNode ``Lean.binderIdent #[mkIdent n]
            | none => mkNode ``Lean.binderIdent #[mkIdent `_]
      trace[Step] "ids from introduced vars: {ids}"
      let mainGoal := mainGoal.map fun mainGoal => (mainGoal.goal, mainGoal.stepState)
      /- Generate the tactic scripts for the preconditions -/
      let currTac ←
        if cfg.prettyPrintedStep then
          -- TODO: how to factor this out?
          let config ←
            match cfg.configSyntax with
            | none => `(Lean.Parser.Tactic.optConfig|)
            | some cfg => pure cfg
          match cfg.preconditionTac with
          | none =>
            if let some cfg := cfg.configSyntax then
              `(tactic| let* ⟨$ids,*⟩ ←[$cfg] $(←usedTheorem.toSyntax))
            else
              `(tactic| let* ⟨$ids,*⟩ ← $(←usedTheorem.toSyntax))
          | some tac =>
            if let some cfg := cfg.configSyntax then
              `(tactic| let* ⟨$ids,*⟩ ←[$cfg] $(←usedTheorem.toSyntax) by $(#[tac])*)
            else
              `(tactic| let* ⟨$ids,*⟩ ← $(←usedTheorem.toSyntax) by $(#[tac])*)
        else
          let config ←
            match cfg.configSyntax with
            | none => `(Lean.Parser.Tactic.optConfig|)
            | some cfg => pure cfg
          if ids.isEmpty
          then
            match cfg.preconditionTac with
            | none => `(tactic| step $config with $(←usedTheorem.toSyntax))
            | some tac => `(tactic| step $config with $(←usedTheorem.toSyntax) by $(#[tac])*)
          else
            match cfg.preconditionTac with
            | none => `(tactic| step $config with $(←usedTheorem.toSyntax) as ⟨$ids,*⟩)
            | some tac => `(tactic| step $config with $(←usedTheorem.toSyntax) as ⟨$ids,*⟩ by $(#[tac])*)
      /- If inferPost is enabled, try to recursively process unsolved preconditions
         that are `spec` goals.

         For each recursively processed precondition, we wrap its script in
         `case <tag> => [intro ...;] <recursive script>` so the generated proof
         navigates to the correct goal. -/
      let sorryStx ← `(tactic|· sorry)
      let (preconditions, extraInfo, preconditionsScript) ←
        if cfg.stepConfig.inferPost then
          let mut remaining : Array (MVarId × Step.OptTask (Option Expr)) := #[]
          let mut extra : Info := {}
          let mut scriptEntries : Array (TaskOrDone (Option Syntax.Tactic)) := #[]
          for (mvarId, proof) in preconditions do
            match proof with
            | .task y =>
              -- Async proof in progress, keep as-is
              remaining := remaining.push (mvarId, proof)
              scriptEntries := scriptEntries.push
                (TaskOrDone.task (y.map fun (e : Option _) => if e.isNone then some sorryStx else none))
            | .none =>
              if ← mvarId.isAssigned then
                continue
              -- Check if this precondition contains a spec goal
              -- (possibly under ∀ binders, e.g., ∀ y, mid y → f y ⦃ post ⦄)
              let precTy ← instantiateMVars (← mvarId.getType)
              let rec stripForall (e : Expr) : Expr :=
                match e.consumeMData with
                | .forallE _ _ body _ => stripForall body
                | e => e
              let innerTy := stripForall precTy
              let isSpec := innerTy.consumeMData.withApp fun f args =>
                f.isConstOf ``Std.WP.spec && args.size == 3
              if isSpec then
                let tag ← mvarId.getTag
                -- Recursively process this spec precondition
                let (subInfo, introNames) ← commitIfNoEx do
                  setGoals [mvarId]
                  let size ← getIntrosSize <$> mvarId.getType
                  let (introFVars, mvarId) ← mvarId.introNP size
                  -- Collect the user names while the fvars are still in scope
                  let introNames ← mvarId.withContext do
                    introFVars.mapM fun fvar => fvar.getUserName
                  setGoals [mvarId]
                  let info ← traverseProgram cfg fuel ss
                  pure (info, introNames)
                -- Build the script: case <tag> => [intros;] <recursive script>
                let subStx ← subInfo.script.toSyntax
                let introStx : Array Syntax.Tactic ←
                  if !introNames.isEmpty then
                    let idents := introNames.map mkIdent
                    pure #[← `(tactic| intros $idents*)]
                  else pure #[]
                let allTacs := introStx ++ subStx
                let caseArgs := makeCaseArgs tag #[]
                let caseTac ← `(tactic| case $caseArgs => $allTacs*)
                scriptEntries := scriptEntries.push (TaskOrDone.mk (some caseTac))
                extra := extra ++ { subInfo with script := .tacs #[] }
              else
                remaining := remaining.push (mvarId, proof)
                scriptEntries := scriptEntries.push (TaskOrDone.mk (some sorryStx))
          pure (remaining, extra, scriptEntries)
        else
          let scriptEntries : Array (TaskOrDone (Option Syntax.Tactic)) := preconditions.map fun (_, p) =>
            match p with
            | .none => TaskOrDone.mk (some sorryStx)
            | .task y => TaskOrDone.task (y.map fun (e : Option _) => if e.isNone then some sorryStx else none)
          pure (preconditions, {}, scriptEntries)

      /- After recursive processing, filter out unassigned vars that got assigned
         (e.g., `?post` assigned by `inferPost` during recursive spec processing) -/
      let unassignedVars ←
        if cfg.stepConfig.inferPost then
          unassignedVars.filterM fun mvarId => do
            pure !(← mvarId.isAssigned)
        else
          pure unassignedVars

      let unassignedVarsScript : Array (TaskOrDone (Option Syntax.Tactic)) :=
        unassignedVars.map fun _ => TaskOrDone.mk (some sorryStx)

      let preconditions ← preconditions.mapM fun (x, y) => do
        let y := match y with | .none => TaskOrDone.done .none | .task y => TaskOrDone.task y
        pure (x, some y)

      let info : Info := {
          script := .tacs (#[TaskOrDone.mk (some currTac)] ++ unassignedVarsScript ++ preconditionsScript),
          unassignedVars,
          subgoals := preconditions ++ extraInfo.subgoals,
        }
      let info := { info with unassignedVars := info.unassignedVars ++ extraInfo.unassignedVars }
      pure (info, mainGoal)
    else
      let (info, mvarId) ← onFinish cfg (← getMainGoal)
      pure (info, mvarId.map (·, ss))

  onMatch (cfg : Config) (bfInfo : Bifurcation.Info) (toBeProcessed : Array (Array Name)): TacticM (List MVarId × (List Info → TacticM Info)) := do
    withTraceNode `Step (fun _ => pure m!"onMatch") do
    trace[Step] "onMatch: encountered {bfInfo.kind}"
    if (←getGoals).isEmpty then
      trace[Step] "onMatch: no goals to be solved!"
      -- Tactic.focus fails if there are no goals to be solved.
      return ({}, fun infos => assert! (infos.length == 0); pure {})
    Tactic.focus do
      let h ← mkFreshUserName `h
      let splitStx ← `(tactic| spec_split)
      let subgoals ← esplitAtSpec h none
      --
      trace[Step] "onMatch: Bifurcation generated {subgoals.length} subgoals"
      unless subgoals.length == toBeProcessed.size do
        throwError "onMatch: Expected {toBeProcessed.size} cases, found {subgoals.length}"

      let infos_mkBranchesStx ← subgoals.mapM fun (vars, h, sg) => do
        setGoals [sg]
        sg.withContext do
        let names ← vars.mapM fun v => v.getUserName
        let h ← h.getUserName
        let names := names ++ [h]
        let mkStx (branchScript : Script) : TacticM (BranchArg × Script) := do
          let caseArgs : BranchArg ← do
            if cfg.useRename then
              pure (BranchArg.rename names)
            else if cfg.useCase then
              pure (BranchArg.case (makeCaseArgs (← sg.getTag) names))
            else pure .empty
          pure (caseArgs, branchScript)
        pure (sg,  mkStx)
      let (infos, mkBranchesStx) := infos_mkBranchesStx.unzip

      let mkStx (infos : List Info) : TacticM Info := do
        unless infos.length == mkBranchesStx.length do
          throwError "onMatch: Expected {mkBranchesStx.length} infos, found {infos.length}"
        let branchesStx ← (infos.zip mkBranchesStx).mapM fun (info, mkBranchStx) => mkBranchStx info.script
        let unassignedVars := (List.flatten (infos.map (fun info => info.unassignedVars.toList))).toArray
        let subgoals := (List.flatten (infos.map (fun info => info.subgoals.toList))).toArray
        let script := Script.split splitStx branchesStx.toArray
        pure ({ script, unassignedVars, subgoals } : Info)

      return (infos, mkStx)

  tryStep (cfg : Config) (ids : Array (Option Name) := #[]) (postsBasename : Option Name := none) (ss : Step.StepState) := do
    try some <$> Step.evalStepCore cfg.stepConfig (some (.str .anonymous "_")) none ids false postsBasename cfg.preconditionTac ss
    catch _ => pure none

  makeIds (base: Name) (numElem numPost : Nat) (defaultId := "x"): Array (TSyntax ``Lean.binderIdent) :=
    let (root, base?) := match base with
      | .str root base => (root, some base)
      | .num root _ => (root, none)
      | .anonymous => (.anonymous, none)
    let base := base?.getD defaultId
    let optionallyEnumerated base num := match num with
      | 0 => #[]
      | 1 => #[Name.str root base]
      | num => Array.ofFn fun (i: Fin num) => Name.str root s!"{base}_{i.val+1}"
    let elemNames := optionallyEnumerated base numElem
    let postNames := optionallyEnumerated s!"{base}_post" numPost
    elemNames ++ postNames |>.map (mkNode ``Lean.binderIdent #[mkIdent ·])

  makeCaseArgs tag names :=
    let tag := Lean.mkNode ``Lean.binderIdent #[mkIdent tag]
    let binderIdents := names.map nameToBinderIdent
    Lean.mkNode ``Lean.Parser.Tactic.caseArg #[tag, mkNullNode (args := binderIdents)]

syntax «step*_args» := (num)? Lean.Parser.Tactic.optConfig ("by" tacticSeq)?
def parseArgs: TSyntax `Aeneas.StepStar.«step*_args» → TermElabM (Config × Option Nat)
| `(«step*_args»| $(fuel)? $config $[by $preconditionTac:tacticSeq]?) => do
  withTraceNode `Step (fun _ => pure m!"parseArgs") do
  let fuel ← do match fuel with
    | none => pure none
    | some fuel =>
      match fuel.raw.isNatLit? with
      | some fuel => pure fuel
      | none => throwUnsupportedSyntax
  let stepConfig ← Step.elabPartialConfig config
  -- TODO: find a simpler way of checking whether the syntax is empty
  let configSyntax := if (Aeneas.Meta.OptionConfig.decomposeOptConfig config).isEmpty then none else some config
  let preconditionTac ← do
    match preconditionTac with
    | none => pure { stepConfig, configSyntax, preconditionTac := none }
    | some preconditionTac => do
      let preconditionTac : Syntax.Tactic := ⟨preconditionTac.raw⟩
      trace[Step] "preconditionTac: {preconditionTac}"
      pure { stepConfig, configSyntax, preconditionTac }
  pure (preconditionTac, fuel)
| _ => throwUnsupportedSyntax

/-- The `step*` tactic repeatedly applies `step` and `split` on the goal.

Its variant `step*?` allows automatically generating the equivalent proof script.
-/
syntax (name := stepStar) "step" noWs ("*" <|> "*?") «step*_args»: tactic

@[tactic stepStar, inherit_doc Step.step]
def evalStepStarTac : Tactic := fun stx => do
  match stx with
  | `(tactic| step* $args:«step*_args») =>
    let (cfg, fuel) ← parseArgs args
    evalStepStar cfg fuel *> pure ()
  | `(tactic| step*? $args:«step*_args») =>
    let (cfg, fuel) ← parseArgs args
    let info ← evalStepStar cfg fuel
    let suggestion ← info.script.toSyntax
    let suggestion ← `(tacticSeq|$(suggestion)*)
    Aeneas.Utils.addTryThisTacticSeqSuggestion stx suggestion (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end StepStar

section Examples

open Std.WP

/--
info: Try this:

  [apply]   simp only [step_simps]
-/
#guard_msgs in
example : True := by step*?

open Std Result

def add1 (x0 x1 : U32) : Std.Result U32 := do
  let x2 ← x0 + x1
  let x3 ← x2 + x2
  x3 + 4#u32

/--
info: Try this:

  [apply]     let* ⟨ x2, x2_post ⟩ ← U32.add_spec
    let* ⟨ x3, x3_post ⟩ ← U32.add_spec
    let* ⟨ ⟩ ← U32.add_spec
-/
#guard_msgs in
example (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
  add1 x y ⦃ _ => True ⦄ := by
  unfold add1
  step*?

/--
info: Try this:

  [apply]     let* ⟨ x2, x2_post ⟩ ← [ +scalarTac -grind ] U32.add_spec
    let* ⟨ x3, x3_post ⟩ ← [ +scalarTac -grind ] U32.add_spec
    let* ⟨ ⟩ ← [ +scalarTac -grind ] U32.add_spec
-/
#guard_msgs in
example (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
  add1 x y ⦃ _ => True ⦄ := by
  unfold add1
  step*? +scalarTac -grind

/--
error: unsolved goals
x y : U32
h : 2 * ↑x + 2 * ↑y + 4 ≤ U32.max
x2 : U32
_✝ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_ : [> let x3 ← x2 + x2 <]
x3_post : ↑x3 = ↑x2 + ↑x2
⊢ x3 + 4#u32 ⦃ z => True ⦄
-/
#guard_msgs in
example (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
  add1 x y ⦃ z => True ⦄ := by
  unfold add1
  step* 2

/--
info: Try this:

  [apply]     let* ⟨ x2, x2_post ⟩ ← U32.add_spec
    let* ⟨ x3, x3_post ⟩ ← U32.add_spec
---
error: unsolved goals
x y : U32
h : 2 * ↑x + 2 * ↑y + 4 ≤ U32.max
x2 : U32
_✝ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_ : [> let x3 ← x2 + x2 <]
x3_post : ↑x3 = ↑x2 + ↑x2
⊢ x3 + 4#u32 ⦃ z => True ⦄
-/
#guard_msgs in
example (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
  add1 x y ⦃ z => True ⦄ := by
  unfold add1
  step*? 2

/--
info: Try this:

  [apply]     simp only [step_simps]
    let* ⟨ x2, x2_post ⟩ ← U32.add_spec
    let* ⟨ x3, x3_post ⟩ ← U32.add_spec
    let* ⟨ z, z_post ⟩ ← U32.add_spec
    agrind
-/
#guard_msgs in
example (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
  let v := 2 * x.val + 2 * y.val + 4
  add1 x y ⦃ z => z.val = v ⦄ := by
  unfold add1
  step*?

def add2 (b : Bool) (x0 x1 : U32) : Std.Result U32 := do
  if b then
    let x2 ← x0 + x1
    let x3 ← x2 + x2
    x3 + 4#u32
  else
    let y ← x0 + x1
    y + 2#u32

/--
info: Try this:

  [apply]     spec_split
    · let* ⟨ x2, x2_post ⟩ ← U32.add_spec
      let* ⟨ x3, x3_post ⟩ ← U32.add_spec
      let* ⟨ ⟩ ← U32.add_spec
    · let* ⟨ y, y_post ⟩ ← U32.add_spec
      let* ⟨ ⟩ ← U32.add_spec
-/
#guard_msgs in
example b (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
      add2 b x y ⦃ _ => True ⦄ := by
  unfold add2
  step*?

/--
info: Try this:

  [apply]     spec_split
    · let* ⟨ x2, x2_post ⟩ ← U32.add_spec
      let* ⟨ x3, x3_post ⟩ ← U32.add_spec
    · let* ⟨ y, y_post ⟩ ← U32.add_spec
      let* ⟨ ⟩ ← U32.add_spec
---
error: unsolved goals
b : Bool
x y : U32
h : 2 * ↑x + 2 * ↑y + 4 ≤ U32.max
h✝ : b = true
x2 : U32
_✝ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_ : [> let x3 ← x2 + x2 <]
x3_post : ↑x3 = ↑x2 + ↑x2
⊢ x3 + 4#u32 ⦃ z => True ⦄
-/
#guard_msgs in
example b (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
  add2 b x y ⦃ z => True ⦄ := by
  unfold add2
  step*? 3

/--
info: Try this:

  [apply]     spec_split
    · let* ⟨ x2, x2_post ⟩ ← U32.add_spec
      · sorry
      let* ⟨ x3, x3_post ⟩ ← U32.add_spec
      · sorry
      let* ⟨ ⟩ ← U32.add_spec
      · sorry
    · let* ⟨ y, y_post ⟩ ← U32.add_spec
      · sorry
      let* ⟨ ⟩ ← U32.add_spec
      · sorry
---
error: unsolved goals
case hmax
b : Bool
x y : U32
h✝ : b = true
⊢ ↑x + ↑y ≤ U32.max

case hmax
b : Bool
x y : U32
h✝ : b = true
x2 : U32
_ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
⊢ ↑x2 + ↑x2 ≤ U32.max

case hmax
b : Bool
x y : U32
h✝ : b = true
x2 : U32
_✝ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_ : [> let x3 ← x2 + x2 <]
x3_post : ↑x3 = ↑x2 + ↑x2
⊢ ↑x3 + ↑4#u32 ≤ U32.max

case hmax
b : Bool
x y : U32
h✝ : ¬b = true
⊢ ↑x + ↑y ≤ U32.max

case hmax
b : Bool
x y✝ : U32
h✝ : ¬b = true
y : U32
_ : [> let y ← x + y✝ <]
y_post : ↑y = ↑x + ↑y✝
⊢ ↑y + ↑2#u32 ≤ U32.max
-/
#guard_msgs in
example b (x y : U32) :
      add2 b x y ⦃ _ => True ⦄ := by
  unfold add2
  step*?

/- Checking that if we can't prove the final goal, we do introduce names for the outputs of the last
   monadic call -/
/--
info: Try this:

  [apply]     let* ⟨ x2, x2_post ⟩ ← U32.add_spec
    let* ⟨ x3, x3_post ⟩ ← U32.add_spec
    let* ⟨ _, _ ⟩ ← U32.add_spec
    sorry
---
error: unsolved goals
x y : U32
h : 2 * ↑x + 2 * ↑y + 4 ≤ U32.max
x2 : U32
_✝² : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_✝¹ : [> let x3 ← x2 + x2 <]
x3_post : ↑x3 = ↑x2 + ↑x2
x✝ : U32
_ : [> let x✝ ← x3 + 4#u32 <]
_✝ : ↑x✝ = ↑x3 + 4
⊢ ↑x < 32
-/
#guard_msgs in
example (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
      add1 x y ⦃ _ => x.val < 32 ⦄ := by
  unfold add1
  step*?

example (x y : U32) (h : x.val * y.val ≤ U32.max):
  (do
    let z0 ← x * y
    let z1 ← y * x
    massert (z1 == z0)) ⦃ _ => True ⦄ := by
    step*

/--
info: Try this:

  [apply]     spec_split
    · simp only [step_simps]
    · rename_i x _
      simp only [step_simps]
-/
#guard_msgs in
example (x : Option Nat) :
  (match x with | none => .ok 0 | some x => .ok x) ⦃ _ => True ⦄ := by
  step*?

/--
info: Try this:

  [apply]     spec_split
    · simp only [step_simps]
    · simp only [step_simps]
-/
#guard_msgs in
example (x : Option α) :
  (match x with | none => .ok 0 | some _ => .ok 1) ⦃ _ => True ⦄ := by
  step*?

/--
info: Try this:

  [apply]     spec_split
    · simp only [step_simps]
    · simp only [step_simps]
    · rename_i a b _ _
      simp only [step_simps]
-/
#guard_msgs in
example (l : List Nat) :
  (match l with
   | [] | [_] => .ok 0
   | a :: b :: _ => .ok (a + b)) ⦃ _ => True ⦄ := by
  step*?

/--
info: Try this:

  [apply]     simp only [step_simps]
    let* ⟨ ⟩ ← core.num.U32.overflowing_add_eq.step_spec
-/
#guard_msgs in
example (x y : U32) :
  (lift (core.num.U32.overflowing_add x y)) ⦃ (_, _) => True ⦄ := by
  step*?

/--
error: unsolved goals
x y x✝¹ : U32
x✝ : Bool
_ : [> let(x✝¹, x✝) ← lift (core.num.U32.overflowing_add x y) <]
_✝ : if ↑x + ↑y > UScalar.max UScalarTy.U32 then ↑x✝¹ + U32.size = ↑x + ↑y ∧ x✝ = true else ↑x✝¹ = ↑x + ↑y ∧ x✝ = false
⊢ False
-/
#guard_msgs in
example (x y : U32) :
  (lift (core.num.U32.overflowing_add x y)) ⦃ (_, _) => False ⦄ := by
  simp only [step_simps]
  step*

/--
error: unsolved goals
case inst
α : Type
x : α
f : α → Result Unit
f_spec : ∀ (x : α) [Inhabited α], f x ⦃ x✝ => True ⦄
⊢ Inhabited α

α : Type
x : α
f : α → Result Unit
f_spec : ∀ (x : α) [Inhabited α], f x ⦃ x✝ => True ⦄
_ : [> let PUnit.unit ← f x <]
⊢ (do
      f x
      ok ()) ⦃
    x✝ => True ⦄
-/
#guard_msgs in
example {α : Type}
  (x : α)
  (f : α → Result Unit) (f_spec : ∀ x, [Inhabited α] → f x ⦃ _ => True ⦄) : --(a : Std.Array α 16#usize) :
  (do
    let () ← f x
    let () ← f x
    pure ()
    ) ⦃ _ => True ⦄ := by
    step*

/--
error: unsolved goals
f : Result (Bool × Bool)
f_spec : f ⦃ x✝ x✝¹ => True ⦄
x✝¹ x✝ : Bool
_ : [> let(x✝¹, x✝) ← f <]
_✝ : True
⊢ False
-/
#guard_msgs in
example
  (f : Result (Bool × Bool))
  (f_spec : f ⦃ _ _ => True ⦄) :
  (do
    let (x, _) ← f
    pure x
    ) ⦃ _ => False ⦄ := by
    step*

/-- Test with functions outputting nothing -/
example (x : U32) (h : x.val < 32) :
  (do
    massert (x < 32#u32)
    massert (x < 32#u32)
    massert (x < 32#u32)) ⦃ _ => True ⦄ := by
  step*

/-- Regression test: step* with if-then-else + fail + contradicting hypothesis.
    Previously crashed with "No goals to be solved" because grind's
    hypothesis internalization would assign the else-branch mvar when it
    detected contradicting hypotheses (h : a = b from context + ¬a = b from
    the else branch). The fix uses a fresh mvar during internalization and
    closes the goal explicitly when a contradiction is found. -/
private def grindContradictionFn (a b : U32) : Result U32 := do
  if a = b then a + b
  else fail .panic

/- Test that step* works (previously crashed with "No goals to be solved") -/
set_option maxHeartbeats 800000 in
example (a b : U32) (h : a = b) (hbnd : a.val + b.val ≤ U32.max) :
    grindContradictionFn a b ⦃ c => c.val = a.val + b.val ⦄ := by
  unfold grindContradictionFn
  step*

/- Test that step*? generates `agrind` for the contradiction branch -/
/--
info: Try this:

  [apply]     spec_split
    · let* ⟨ c, c_post ⟩ ← U32.add_spec
      agrind
    · agrind
-/
#guard_msgs in
set_option maxHeartbeats 800000 in
example (a b : U32) (h : a = b) (hbnd : a.val + b.val ≤ U32.max) :
    grindContradictionFn a b ⦃ c => c.val = a.val + b.val ⦄ := by
  unfold grindContradictionFn
  step*?

/- Test that the script generated by step*? is valid -/
set_option maxHeartbeats 800000 in
example (a b : U32) (h : a = b) (hbnd : a.val + b.val ≤ U32.max) :
    grindContradictionFn a b ⦃ c => c.val = a.val + b.val ⦄ := by
  unfold grindContradictionFn
  spec_split
  · let* ⟨ c, c_post ⟩ ← U32.add_spec
    agrind
  · agrind

/-- Test: contradiction after a match (explicit match on an inductive type).
    The `none` branch leads to `fail`, which contradicts the postcondition.
    With `h : x = some v` in context, the `none` branch is contradictory. -/
private def matchContradictionFn (x : Option U32) : Result U32 :=
  match x with
  | some v => .ok v
  | none => fail .panic

set_option maxHeartbeats 800000 in
example (v : U32) (h : x = some v) :
    matchContradictionFn x ⦃ r => r = v ⦄ := by
  unfold matchContradictionFn
  step*

/-- Test: contradiction after a let-binding.
    After the `add` step, the postcondition introduces `c.val = a.val + b.val`.
    The if-then-else checks `a = b`. In the `else` branch, we have `¬(a = b)` from
    the branch plus any accumulated facts. With `h : a = b` in scope, this contradicts.
    The contradiction is detected after the let-binding step introduces `c` and its
    postcondition, and then the if-split creates the contradicting branch. -/
private def letBindContradictionFn (a b : U32) : Result U32 := do
  let c ← a + b
  if a = b then
    .ok c
  else
    fail .panic

set_option maxHeartbeats 800000 in
example (a b : U32) (h : a = b) (hbnd : a.val + b.val ≤ U32.max) :
    letBindContradictionFn a b ⦃ r => r.val = a.val + b.val ⦄ := by
  unfold letBindContradictionFn
  step*

end Examples

end Aeneas
