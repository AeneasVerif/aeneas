import Aeneas.Tactic.Step.Step
import AeneasMeta.Split
open Lean Meta Elab Tactic
open Lean.Meta.Sym (SymM)

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

inductive TargetKind where
| bind (fn : Name)
| switch (info : Bifurcation.Info)
| result
| unknown

/- Smaller helper which we use to check in which situation we are -/
def analyzeTarget (mvarId : MVarId) : MetaM TargetKind := do
  withTraceNode `Step (fun _ => do pure m!"analyzeTarget") do
  try
    let goalTy ← mvarId.getType
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
  let mvarId ← getMainGoal
  -- Initialize the step state (grind threading + persistent SymM session + cached simp contexts)
  let symSession ← Step.SymSession.create
  let simpCaches ← Step.SimpCaches.create
  let initState : Step.StepState ←
    if cfg.stepConfig.threadGrindState then
      let gs ← Step.initStepGrindState cfg.stepConfig mvarId
      pure { grindState? := some gs, symSession? := some symSession, simpCaches? := some simpCaches }
    else pure { symSession? := some symSession, simpCaches? := some simpCaches }
  /- Run the entire step* pipeline inside one SymM session.
     This eliminates per-step session creation overhead and allows caches
     to accumulate across all steps in the step* traversal. -/
  let (result, finalGoals) ← symSession.run do
    -- Simplify the target
    let (info, mvarId?) ← simplifyTargetM initState.simpCaches? mvarId
    -- Continue
    match mvarId? with
    | some mvarId =>
      let info' ← traverseProgramM cfg fuel initState mvarId
      let info := info ++ info'
      -- Wait for the asynchronous execution to finish
      let sgs ← withTraceNode `Step (fun _ => do pure m!"filtering subgoals") do
        let mut sgs := #[]
        for (sgMvarId, proof) in info.subgoals do
          match proof with
          | none => sgs := sgs.push sgMvarId
          | some proof =>
            match proof.get with
            | none => sgs := sgs.push sgMvarId
            | some proof =>
              sgMvarId.withContext do
              let _e ← mkAuxTheorem (← sgMvarId.getType) proof (zetaDelta := true)
              sgMvarId.assign proof
        pure sgs
      pure ({ script := info.script, unassignedVars := info.unassignedVars, subgoals := sgs },
            info.unassignedVars.toList ++ sgs.toList)
    | none =>
      pure ({ script := info.script, unassignedVars := #[], subgoals := #[] }, [])
  setGoals finalGoals
  pure result

where
  /-- Simplify the target using step_simps. SymM-native: uses `simpAtTargetM` directly. -/
  simplifyTargetM (simpCaches? : Option Step.SimpCaches) (mvarId : MVarId) : SymM (Info × Option MVarId) := do
    withTraceNode `Step (fun _ => do pure m!"simplifyTarget") do
    Step.traceGoalWithNode "about to simplify goal" mvarId
    let mvarId? ← match simpCaches? with
      | some c => Step.simpAtTargetMCached mvarId c.stepSimps.1 c.stepSimps.2
      | none =>
        Step.simpAtTargetM mvarId true
          { maxDischargeDepth := 1, failIfUnchanged := false}
          {simpThms := #[← Step.stepSimpExt.getTheorems]}
    /- Generate script and check if we proved/changed the goal -/
    let tac : Array Syntax.Tactic ← do
      let genSimp : Bool := match mvarId? with
        | none => true
        | some mvarId' => mvarId' != mvarId
      if genSimp then
        -- Use scope-free identifier so generated script is user-pasteable
        let stepSimpsIdent : Lean.Ident := ⟨.ident .none "step_simps".toRawSubstring `step_simps []⟩
        let step_simps ← `(Parser.Tactic.simpLemma| $(stepSimpsIdent):term)
        let tac ← `(tactic|simp only [$step_simps])
        pure #[TaskOrDone.mk (some tac)]
      else pure #[]
    let info : Info := ⟨ .tacs tac, #[], #[] ⟩
    match mvarId? with
    | some mvarId' => Step.traceGoalWithNode "after simplification" mvarId'
    | none => trace[Step] "goal proved"
    pure (info, mvarId?)

  /-- Main traversal loop. SymM-native: threads MVarId explicitly. -/
  traverseProgramM (cfg : Config) (fuel : Option Nat) (ss : Step.StepState) (mvarId : MVarId) : SymM Info := do
    mvarId.withContext do
    withTraceNode `Step (fun _ => do pure m!"traverseProgram") do
    traceGoalWithNode "current goal" mvarId
    -- Check if there remains fuel
    let fuel ←
      match fuel with
      | none => pure none
      | some fuel =>
        if fuel = 0 then return { script := .tacs #[], unassignedVars := #[], subgoals := #[(mvarId, none)] }
        else pure (some (fuel - 1))
    let targetKind ← analyzeTarget mvarId
    match targetKind with
    | .bind varName => do
      let names := if varName.hasMacroScopes then #[] else #[some varName]
      let (info, mainGoalAndState) ← onBindM cfg names ss mvarId
      /- Continue, if necessary -/
      match mainGoalAndState with
      | none =>
        -- Stop
        trace[Step] "stop"
        return info
      | some (mainGoal, ss) =>
        /- Check if there are unassigned meta-variables which are not `Prop`:
           if it is the case it means there are meta-variables we could not infer, so we stop -/
        if info.unassignedVars.isEmpty then
          let restInfo ← traverseProgramM cfg fuel ss mainGoal
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
      /- Bridge to TacticM for esplitAtSpec (needs focus/setGoals).
         We get back the branch goals and a syntax-generation closure. -/
      let (splitResult, _) ← Step.runTacticMOnGoal mvarId do
        onMatchSplit cfg bfInfo contsTaggedVals
      let (branchGoals, branchNames, splitStx) := splitResult
      withTraceNode `Step (fun _ => do pure m!"exploring branches") do
      /- Continue exploring from the subgoals.
         Each branch starts from the same state (branches are independent).
         We update the grind state for each branch to internalize the hypotheses
         introduced by `esplitAtSpec` (case variables, discriminant equality). -/
      let branchInfos ← branchGoals.mapM fun mainGoal => do
        let ss ← ss.update cfg.stepConfig mainGoal
        traverseProgramM cfg fuel ss mainGoal
      /- Put everything together — after branches, state is discarded (we can't merge
         divergent e-graphs). Use the pre-branch state going forward. -/
      mkMatchInfo splitStx branchNames branchInfos
    | .result => do
      let (info, mainGoal) ← onResultM cfg ss mvarId
      let mainGoal ← match mainGoal with
        | none => pure #[]
        | some mainGoal => pure #[(mainGoal, none)]
      pure { info with subgoals := info.subgoals ++ mainGoal }
    | .unknown => do
      trace[Step] "don't know what to do: it may be a terminal goal, attempting to solve it with grind"
      let (info, mainGoal) ← onResultM cfg ss mvarId
      let mainGoal ← match mainGoal with
        | none => pure #[]
        | some mainGoal => pure #[(mainGoal, none)]
      pure { info with subgoals := info.subgoals ++ mainGoal }

  /-- Process a result (terminal call). SymM-native. -/
  onResultM (cfg : Config) (ss : Step.StepState) (mvarId : MVarId) : SymM (Info × Option MVarId) := do
    withTraceNode `Step (fun _ => pure m!"onResult") do
    let names ← Step.getPostNamesFromGoal mvarId
    let (info, mainGoalAndState) ← onBindM cfg names ss mvarId
    match mainGoalAndState with
    | none =>
      trace[Step] "done"
      pure (info, none)
    | some (mvarId, _) =>
      let (info', mvarId) ← onFinishM cfg ss mvarId
      pure (info ++ info', mvarId)

  /-- Try to finish a goal (simplify + grind). SymM-native for simp, direct MetaM for grind
      when in sync mode, bridges to TacticM only for async. -/
  onFinishM (cfg : Config) (ss : Step.StepState) (mvarId : MVarId) : SymM (Info × Option MVarId) := do
    withTraceNode `Step (fun _ => pure m!"onFinish") do
    traceGoalWithNode "goal" mvarId
    /- Simplify a bit (SymM-native) -/
    let (info, mvarId?) ← simplifyTargetM ss.simpCaches? mvarId
    match mvarId? with
    | none => pure (info, none)
    | some mvarId =>
      if !cfg.stepConfig.async then
        /- Synchronous path: try fully in MetaM (no TacticM bridge).
           Save the mctx so that if simp-preprocessing assigns mvarId, we can
           restore it and report the goal as unsolved with the original mvarId. -/
        let saved ← getMCtx
        let solved ← try
          Step.dischargeWithThreadedGrindM_onFinish cfg.stepConfig ss.grindState? mvarId
        catch _ => pure false
        let tacStx ←
          if solved then `(tactic| agrind)
          else
            /- Restore mctx: preprocessing simp inside dischargeWithThreadedGrindM_onFinish
               may have assigned mvarId. Restoring ensures the mvarId stays unassigned
               so it appears correctly as an unsolved goal. -/
            setMCtx saved
            `(tactic| sorry)
        let finishInfo : Info := {
          script := .tacs #[.done (some tacStx)],
          unassignedVars := #[],
          subgoals := if solved then #[] else #[(mvarId, none)] }
        pure (info ++ finishInfo, none)
      else
        /- Async path: must use TacticM bridge for Async.asyncRunTactic -/
        let (finishInfo, _) ← Step.runTacticMOnGoal mvarId do
            let grindTac : TacticM Unit :=
              Step.evalAGrindWithPreprocess cfg.stepConfig.withGroundSimprocs cfg.stepConfig.toGrindConfig cfg.stepConfig.nla
            let tacStx : IO.Promise Syntax.Tactic ← IO.Promise.new
            let rec tryFinish (tacl : List (String × Syntax.Tactic × TacticM Unit)) : TacticM Unit := do
              match tacl with
              | [] =>
                trace[Step] "could not prove the goal: inserting a sorry"
                tacStx.resolve (← `(tactic| sorry))
              | (name, stx, tac) :: tacl =>
                let stx : Option Syntax.Tactic ←
                  withTraceNode `Step (fun _ => do pure m!"Attempting to solve finish goal with `{name}`:\n{← Tactic.getMainGoal}") do
                  try
                    tac
                    let gl ← Tactic.getUnsolvedGoals
                    if ¬ gl.isEmpty then throwError "tactic failed"
                    else pure stx
                  catch _ => pure none
                match stx with
                | some stx =>
                  trace[Step] "goal solved"
                  tacStx.resolve stx
                | none => tryFinish tacl
            let proof ← Async.asyncRunTactic (tryFinish [("grind", ← `(tactic| agrind), grindTac)])
            let proof := proof.result?.map (fun x => match x with | none | some none => none | some (some x) => some x)
            pure ({ script := .tacs #[.task tacStx.result?],
                    unassignedVars := #[],
                    subgoals := #[(mvarId, some (TaskOrDone.task proof))] } : Info)
        pure (info ++ finishInfo, none)

  /-- Process a bind (one step). SymM-native: calls evalStepCore directly. -/
  onBindM (cfg : Config) (names : Array (Option Name)) (ss : Step.StepState) (mvarId : MVarId) : SymM (Info × Option (MVarId × Step.StepState)) := do
    withTraceNode `Step (fun _ => pure m!"onBind ({names})") do
    let postsBasename := names[0]?.join
    if let some res ← tryStepM cfg names postsBasename ss mvarId then
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
      let sorryStx ← `(tactic|· sorry)
      let unassignedVarsScript : Array (TaskOrDone (Option Syntax.Tactic)) :=
        unassignedVars.map fun _ => TaskOrDone.mk (some sorryStx)
      let preconditionsScript : Array (TaskOrDone (Option Syntax.Tactic)) := preconditions.map fun (_, p) =>
        match p with
        | .none => TaskOrDone.mk (some sorryStx)
        | .task y => TaskOrDone.task (y.map fun (e : Option _) => if e.isNone then some sorryStx else none)
      let preconditions ← preconditions.mapM fun (x, y) => do
        let y := match y with | .none => TaskOrDone.done .none | .task y => TaskOrDone.task y
        pure (x, some y)

      let info : Info := {
          script := .tacs (#[TaskOrDone.mk (some currTac)] ++ unassignedVarsScript ++ preconditionsScript),
          unassignedVars,
          subgoals := preconditions,
        }
      pure (info, mainGoal)
    else
      -- Check if simp inside tryStep already solved the goal as a side effect
      if ← mvarId.isAssigned then
        -- Goal was solved by initial simplification — generate script entry and return success
        let stepSimpsIdent : Lean.Ident := ⟨.ident .none "step_simps".toRawSubstring `step_simps []⟩
        let stepSimpsSimpLemma ← `(Parser.Tactic.simpLemma| $(stepSimpsIdent):term)
        let simpStx ← `(tactic| simp only [$stepSimpsSimpLemma])
        let info : Info := {
          script := .tacs #[.done (some simpStx)],
          unassignedVars := #[],
          subgoals := #[],
        }
        pure (info, none)
      else
        let (info, mvarId) ← onFinishM cfg ss mvarId
        pure (info, mvarId.map (·, ss))

  /-- Split a match/ite using MetaM-native esplitAtSpecM (avoids outer TacticM bridge).
      Returns branch goals, names, and tactic syntax. -/
  onMatchSplitM (toBeProcessed : Array (Array Name)) (mvarId : MVarId)
      : SymM (List MVarId × List (Array Name) × Syntax.Tactic) := do
    withTraceNode `Step (fun _ => pure m!"onMatchSplitM") do
    let h ← mkFreshUserName `h
    let splitStx ← `(tactic| spec_split)
    let subgoals ← Step.esplitAtSpecM h none mvarId
    trace[Step] "onMatch: Bifurcation generated {subgoals.length} subgoals"
    unless subgoals.length == toBeProcessed.size do
      throwError "onMatch: Expected {toBeProcessed.size} cases, found {subgoals.length}"
    let branchData ← subgoals.mapM fun (vars, hFvar, sg) => do
      sg.withContext do
      let names ← vars.mapM fun v => v.getUserName
      let hName ← hFvar.getUserName
      let allNames := (names.toList ++ [hName]).toArray
      pure (sg, allNames)
    let (branchGoals, branchNames) := branchData.unzip
    pure (branchGoals, branchNames, splitStx)

  /-- Split a match/ite in TacticM (needs focus/setGoals), returning branch goals and names.
      Called via bridge from traverseProgramM. -/
  onMatchSplit (_cfg : Config) (_bfInfo : Bifurcation.Info) (toBeProcessed : Array (Array Name))
      : TacticM (List MVarId × List (Array Name) × Syntax.Tactic) := do
    withTraceNode `Step (fun _ => pure m!"onMatch") do
    trace[Step] "onMatch: encountered {_bfInfo.kind}"
    let h ← mkFreshUserName `h
    let splitStx ← `(tactic| spec_split)
    let subgoals ← esplitAtSpec h none
    trace[Step] "onMatch: Bifurcation generated {subgoals.length} subgoals"
    unless subgoals.length == toBeProcessed.size do
      throwError "onMatch: Expected {toBeProcessed.size} cases, found {subgoals.length}"
    -- Collect branch goals and names for later SymM processing
    let branchData ← subgoals.mapM fun (vars, hFvar, sg) => do
      sg.withContext do
      let names ← vars.mapM fun v => v.getUserName
      let hName ← hFvar.getUserName
      let allNames := (names.toList ++ [hName]).toArray
      pure (sg, allNames)
    let (branchGoals, branchNames) := branchData.unzip
    pure (branchGoals, branchNames, splitStx)

  /-- Generate the combined Info for a match/ite from branch results. SymM-native. -/
  mkMatchInfo (splitStx : Syntax.Tactic) (branchNames : List (Array Name)) (branchInfos : List Info)
      : SymM Info := do
    unless branchInfos.length == branchNames.length do
      throwError "mkMatchInfo: Expected {branchNames.length} infos, found {branchInfos.length}"
    let branchesStx ← (branchInfos.zip branchNames).mapM fun (info, names) => do
      let caseArgs : BranchArg ←
        if cfg.useRename then
          pure (BranchArg.rename names)
        else pure .empty
      pure (caseArgs, info.script)
    let unassignedVars := (List.flatten (branchInfos.map (fun info => info.unassignedVars.toList))).toArray
    let subgoals := (List.flatten (branchInfos.map (fun info => info.subgoals.toList))).toArray
    let script := Script.split splitStx branchesStx.toArray
    pure ({ script, unassignedVars, subgoals } : Info)

  /-- Try one step. SymM-native: calls evalStepCore directly (no per-step session overhead). -/
  tryStepM (_cfg : Config) (ids : Array (Option Name) := #[]) (postsBasename : Option Name := none) (ss : Step.StepState) (mvarId : MVarId) : SymM (Option Step.Stats) := do
    try some <$> Step.evalStepCore _cfg.stepConfig (some (.str .anonymous "_")) none ids false postsBasename _cfg.preconditionTac ss mvarId
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

  makeCaseArgs (tag : Name) (names : Array Name) :=
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
    /- TODO: do not use the Aesop helper but our own (it mentions Aesop in the message)
       See https://github.com/AeneasVerif/aeneas/issues/476 -/
    Aesop.addTryThisTacticSeqSuggestion stx suggestion (origSpan? := ← getRef)
    --TODO: if we use this the indentation is not correct
    --Meta.Tactic.TryThis.addSuggestion stx suggestion (origSpan? := ← getRef)
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
case a
x y : U32
h : 2 * ↑x + 2 * ↑y + 4 ≤ U32.max
x2 : U32
_✝¹ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_✝ : [> let x3 ← x2 + x2 <]
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
case a
x y : U32
h : 2 * ↑x + 2 * ↑y + 4 ≤ U32.max
x2 : U32
_✝¹ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_✝ : [> let x3 ← x2 + x2 <]
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
case a
b : Bool
x y : U32
h : 2 * ↑x + 2 * ↑y + 4 ≤ U32.max
h✝ : b = true
x2 : U32
_✝¹ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_✝ : [> let x3 ← x2 + x2 <]
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
_✝ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
⊢ ↑x2 + ↑x2 ≤ U32.max

case hmax
b : Bool
x y : U32
h✝ : b = true
x2 : U32
_✝¹ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_✝ : [> let x3 ← x2 + x2 <]
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
_✝ : [> let y ← x + y✝ <]
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
case a
x y : U32
h : 2 * ↑x + 2 * ↑y + 4 ≤ U32.max
x2 : U32
_✝³ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_✝² : [> let x3 ← x2 + x2 <]
x3_post : ↑x3 = ↑x2 + ↑x2
x✝ : U32
_✝¹ : [> let x✝ ← x3 + 4#u32 <]
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
case a
x y x✝¹ : U32
x✝ : Bool
_✝¹ : [> let(x✝¹, x✝) ← lift (core.num.U32.overflowing_add x y) <]
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

case a
α : Type
x : α
f : α → Result Unit
f_spec : ∀ (x : α) [Inhabited α], f x ⦃ x✝ => True ⦄
_✝ : [> let PUnit.unit ← f x <]
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
case a
f : Result (Bool × Bool)
f_spec : f ⦃ x✝ x✝¹ => True ⦄
x✝¹ x✝ : Bool
_✝¹ : [> let(x✝¹, x✝) ← f <]
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

end Examples

end Aeneas
