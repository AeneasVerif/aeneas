import Aeneas.Progress.Progress
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

namespace ProgressStar

abbrev traceGoalWithNode := Progress.traceGoalWithNode

structure Config where
  async : Bool := false
  preconditionTac: Option Syntax.Tactic := none
  /-- Should we use the special syntax `let* ⟨ ...⟩ ← ...` or the more standard syntax `progress with ... as ⟨ ... ⟩`? -/
  prettyPrintedProgress : Bool := true
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
  -- TODO: this type is overly complex
  subgoals: Array (MVarId × Option (TaskOrDone (Option Expr))) := #[]

structure Result where
  script: Script
  subgoals: Array MVarId

instance: Append Info where
  append inf1 inf2 := {
    script := .seq inf1.script inf2.script,
    subgoals := inf1.subgoals ++ inf2.subgoals,
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

attribute [progress_simps] Aeneas.Std.bind_assoc_eq

inductive TargetKind where
| bind (fn : Name)
| switch (info : Bifurcation.Info)
| result
| unknown

/- Smaller helper which we use to check in which situation we are -/
def analyzeTarget : TacticM TargetKind := do
  withTraceNode `Progress (fun _ => do pure m!"analyzeTarget") do
  try
    let goalTy ← (← getMainGoal).getType
    -- Dive into the `spec program post`
    goalTy.consumeMData.withApp fun spec? args => do
    if h: spec?.isConstOf ``Std.WP.spec ∧ args.size = 3 then
      trace[Progress] "application of `spec` with arity 3"
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
      trace[Progress] "not an application of `spec` with arity 3"
      pure .result
  catch _ =>
    trace[Progress] "exception caught"
    pure .unknown

partial def evalProgressStar (cfg: Config) (fuel : Option Nat) : TacticM Result :=
  withMainContext do focus do
  withTraceNode `Progress (fun _ => do pure m!"evalProgressStar") do
  -- Simplify the target
  let (info, mvarId) ← simplifyTarget
  -- Continue
  match mvarId with
  | some _ =>
    let info' ← traverseProgram cfg fuel
    let info := info ++ info'
    -- Wait for the asynchronous execution to finish
    withTraceNode `Progress (fun _ => do pure m!"filtering subgoals") do
    let mut sgs := #[]
    for (mvarId, proof) in info.subgoals do
      match proof with
      | none => sgs := sgs.push mvarId
      | some proof =>
        match proof.get with
        | none => sgs := sgs.push mvarId
        | some proof =>
          -- Introduce an auxiliary theorem
          let declName? ← Term.getDeclName?
          mvarId.withContext do
          let e ← mkAuxTheorem (← mvarId.getType) proof (zetaDelta := true)
          mvarId.assign proof
    setGoals sgs.toList
    pure { script := info.script, subgoals := sgs }
  | none => pure { script := info.script, subgoals := #[] }

where
  simplifyTarget : TacticM (Info × Option MVarId) := do
    withTraceNode `Progress (fun _ => do pure m!"simplifyTarget") do
    traceGoalWithNode "about to simplify goal"
    let mvarId0 ← getMainGoal
    let r ← Simp.simpAt (simpOnly := true)
      { maxDischargeDepth := 1, failIfUnchanged := false}
      {simpThms := #[← Progress.progressSimpExt.getTheorems]}
      (.targets #[] true)
    /- We may have proven the goal already -/
    let tac : Array Syntax.Tactic ← do
      let genSimp : Bool ← do
        if r.isNone then pure true
        else do
          pure ((← getMainGoal) != mvarId0)
      if genSimp then
        let progress_simps ← `(Parser.Tactic.simpLemma| $(mkIdent `progress_simps):term)
        let tac ← `(tactic|simp only [$progress_simps])
        pure #[TaskOrDone.mk (some tac)]
      else pure #[]
    let info : Info := ⟨ .tacs tac, #[] ⟩
    if r.isSome then traceGoalWithNode "after simplification"
    else trace[Progress] "goal proved"
    let goal ← do if r.isSome then pure (some (← getMainGoal)) else pure none
    pure (info, goal)

  traverseProgram (cfg : Config) (fuel : Option Nat) : TacticM Info := do
    withMainContext do
    withTraceNode `Progress (fun _ => do pure m!"traverseProgram") do
    traceGoalWithNode "current goal"
    -- Check if there remains fuel
    let fuel ←
      match fuel with
      | none => pure none
      | some fuel =>
        if fuel = 0 then return { script := .tacs #[], subgoals := #[(← getMainGoal, none)] }
        else pure (some (fuel - 1))
    let targetKind ← analyzeTarget
    match targetKind with
    | .bind varName => do
      let (info, mainGoal) ← onBind cfg varName
      /- Continue, if necessary -/
      match mainGoal with
      | none =>
        -- Stop
        trace[Progress] "stop"
        return info
      | some mainGoal =>
        setGoals [mainGoal]
        let restInfo ← traverseProgram cfg fuel
        return info ++ restInfo
    | .switch bfInfo => do
      let contsTaggedVals ←
        bfInfo.branches.mapM fun br => do
          Utils.lambdaTelescopeN br.toExpr br.numArgs fun xs _ => do
            let names ← xs.mapM (·.fvarId!.getUserName)
            return names
      trace[Progress] "Match over scrutinee: {bfInfo.scrut}"
      let (branchGoals, mkStx) ← onMatch cfg bfInfo contsTaggedVals
      withTraceNode `Progress (fun _ => do pure m!"exploring branches") do
      /- Continue exploring from the subgoals -/
      let branchInfos ← branchGoals.mapM fun mainGoal => do
        setGoals [mainGoal]
        let restInfo ← traverseProgram cfg fuel
        pure restInfo
      /- Put everything together -/
      mkStx branchInfos
    | .result => do
      let (info, mainGoal) ← onResult cfg
      let mainGoal ← match mainGoal with
        | none => pure #[]
        | some mainGoal => pure #[(mainGoal, none)]
      pure { info with subgoals := info.subgoals ++ mainGoal }
    | .unknown => do
      trace[Progress] "don't know what to do: inserting a sorry"
      let subgoals ← pure ((← getUnsolvedGoals).toArray.map fun g => (g, none))
      let tac ←`(tactic| sorry)
      return ({ script := .tacs #[TaskOrDone.mk (some tac)], subgoals })

  onResult (cfg : Config) : TacticM (Info × Option MVarId) := do
    withTraceNode `Progress (fun _ => pure m!"onResult") do
    /- If we encounter `(do f a)` we process it as if it were `(do let res ← f a; return res)`
       since (id = (· >>= pure)) and when we desugar the do block we have that

                            (do f a) == f a
                                     == (f a) >>= pure
                                     == (do let res ← f a; return res)

       We known in advance the result of processing `return res`, which is to do nothing.
       This allows us to prevent code duplication with the `onBind` function. -/
    let res ← onBind cfg (.str .anonymous "res")
    match res.snd with
    | none =>
      trace[Progress] "done"
      pure res
    | some mvarId =>
      let (info', mvarId) ← onFinish mvarId
      pure (res.fst ++ info', mvarId)

  onFinish (mvarId : MVarId) : TacticM (Info × Option MVarId) := do
    withTraceNode `Progress (fun _ => pure m!"onFinish") do
    setGoals [mvarId]
    traceGoalWithNode "goal"
    /- Simplify a bit -/
    let (info, mvarId) ← simplifyTarget
    match mvarId with
    | none => pure (info, mvarId)
    | some mvarId =>
      /- Attempt to finish with a tactic -/
      -- `simp [*]`
      let simpTac : TacticM Syntax.Tactic := do
        let localAsms ← pure ((← (← getLCtx).getAssumptions).map LocalDecl.fvarId)
        let simpArgs : Simp.SimpArgs := {hypsToUse := localAsms.toArray}
        let r ← Simp.simpAt false { maxDischargeDepth := 1 } simpArgs (.targets #[] true)
        -- Raise an error if the goal is not proved
        if r.isSome then throwError "Goal not proved"
        else `(tactic|simp [*])
      -- `scalar_tac`
      let scalarTac : TacticM Syntax.Tactic := do
        ScalarTac.scalarTac {}
        `(tactic|scalar_tac)
      -- TODO: add the tactic given by the user
      let tacStx : IO.Promise Syntax.Tactic ← IO.Promise.new
      let rec tryFinish (tacl : List (String × TacticM Syntax.Tactic)) : TacticM Unit := do
        match tacl with
        | [] =>
          trace[Progress] "could not prove the goal: inserting a sorry"
          tacStx.resolve (← `(tactic| sorry))
        | (name, tac) :: tacl =>
          let stx : Option Syntax.Tactic ←
            withTraceNode `Progress (fun _ => pure m!"Attempting to solve with `{name}`") do
            try
              let stx ← tac
              -- Check that there are no remaining goals
              let gl ← Tactic.getUnsolvedGoals
              if ¬ gl.isEmpty then throwError "tactic failed"
              else pure stx
            catch _ => pure none
          match stx with
          | some stx =>
            trace[Progress] "goal solved"
            tacStx.resolve stx
          | none => tryFinish tacl
      let proof ← Async.asyncRunTactic (tryFinish [("simp [*]", simpTac), ("scalar_tac", scalarTac)])
      let proof := proof.result?.map (fun x => match x with | none | some none => none | some (some x) => some x)
      let info' : Info ← pure { script := .tacs #[.task tacStx.result?], subgoals := #[(mvarId, some (TaskOrDone.task proof))] }
      pure (info ++ info', none)

  onBind (cfg : Config) (varName : Name) : TacticM (Info × Option MVarId) := do
    withTraceNode `Progress (fun _ => pure m!"onBind ({varName})") do
    if let some {usedTheorem, unassignedVars, preconditions, mainGoal } ← tryProgress cfg then
      withTraceNode `Progress (fun _ => pure m!"progress succeeded") do
      match mainGoal with
      | none => trace[Progress] "Main goal solved"
      | some goal =>
        withTraceNode `Progress (fun _ => pure m!"New main goal:") do
        trace[Progress] "{goal.goal}"
      withTraceNode `Progress (fun _ => pure m!"all preconditions") do trace[Progress] "All preconditions:\n{preconditions.map Prod.fst}"
      /- Update the main goal by renaming the fresh variables, if necessary -/
      let ids := match mainGoal with | none => #[] | some goal => makeIds varName.eraseMacroScopes goal.outputs.size goal.posts.size
      trace[Progress] "ids from used theorem: {ids}"
      let mainGoal ← do mainGoal.mapM fun mainGoal => do
        if ¬ ids.isEmpty then
          renameInaccessibles mainGoal.goal ids -- NOTE: Taken from renameI tactic
        else pure mainGoal.goal
      /- Generate the tactic scripts for the preconditions -/
      let currTac ←
        -- TODO: how to factor this out?
        if cfg.prettyPrintedProgress then
          match cfg.preconditionTac with
          | none => `(tactic| let* ⟨$ids,*⟩ ← $(←usedTheorem.toSyntax))
          | some tac => `(tactic| let* ⟨$ids,*⟩ ← $(←usedTheorem.toSyntax) by $(#[tac])*)
        else
          if ids.isEmpty
          then
            match cfg.preconditionTac with
            | none => `(tactic| progress with $(←usedTheorem.toSyntax))
            | some tac => `(tactic| progress with $(←usedTheorem.toSyntax) by $(#[tac])*)
          else
            match cfg.preconditionTac with
            | none => `(tactic| progress with $(←usedTheorem.toSyntax) as ⟨$ids,*⟩)
            | some tac => `(tactic| progress with $(←usedTheorem.toSyntax) as ⟨$ids,*⟩ by $(#[tac])*)
      let sorryStx ← `(tactic|· sorry)
      let preconditionsScript : Array (TaskOrDone (Option Syntax.Tactic)) := preconditions.map fun (_, p) =>
        match p with
        | .none => TaskOrDone.mk (some sorryStx)
        | .task y => TaskOrDone.task (y.map fun (e : Option _) => if e.isNone then some sorryStx else none)
      let preconditions ← preconditions.mapM fun (x, y) => do
        let y := match y with | .none => TaskOrDone.done .none | .task y => TaskOrDone.task y
        pure (x, some y)

      let info : Info := {
          script := .tacs (#[TaskOrDone.mk (some currTac)] ++ preconditionsScript),
          subgoals := preconditions,
        }
      pure (info, mainGoal)
    else
      onFinish (← getMainGoal)

  onMatch (cfg : Config) (bfInfo : Bifurcation.Info) (toBeProcessed : Array (Array Name)): TacticM (List MVarId × (List Info → TacticM Info)) := do
    withTraceNode `Progress (fun _ => pure m!"onMatch") do
    trace[Progress] "onMatch: encountered {bfInfo.kind}"
    if (←getGoals).isEmpty then
      trace[Progress] "onMatch: no goals to be solved!"
      -- Tactic.focus fails if there are no goals to be solved.
      return ({}, fun infos => assert! (infos.length == 0); pure {})
    Tactic.focus do
      let h ← mkFreshUserName `h
      let splitStx ← `(tactic| spec_split)
      let subgoals ← esplitAtSpec h none
      --
      trace[Progress] "onMatch: Bifurcation generated {subgoals.length} subgoals"
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
        let infos := infos.zip mkBranchesStx
        let infos ← do infos.mapM fun (info, mkBranchStx) => do
          let stx ← mkBranchStx info.script
          pure (info.subgoals.toList, stx)
        let subgoals := (List.flatten (infos.map Prod.fst)).toArray
        let branchesStx := infos.map Prod.snd
        let script := Script.split splitStx branchesStx.toArray
        pure ({ script, subgoals } : Info)

      return (infos, mkStx)

  tryProgress (cfg : Config) := do
    try some <$> Progress.evalProgressCore cfg.async (some (.str .anonymous "_")) none #[] cfg.preconditionTac
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

syntax «progress*_args» := (num)? ("by" tacticSeq)?
def parseArgs: TSyntax `Aeneas.ProgressStar.«progress*_args» → CoreM (Config × Option Nat)
| `(«progress*_args»| $(fuel)? $[by $preconditionTac:tacticSeq]?) => do
  withTraceNode `Progress (fun _ => pure m!"parseArgs") do
  let fuel ← do match fuel with
    | none => pure none
    | some fuel =>
      match fuel.raw.isNatLit? with
      | some fuel => pure fuel
      | none => throwUnsupportedSyntax
  let preconditionTac ← do
    match preconditionTac with
    | none => pure {preconditionTac := none}
    | some preconditionTac => do
      let preconditionTac : Syntax.Tactic := ⟨preconditionTac.raw⟩
      trace[Progress] "preconditionTac: {preconditionTac}"
      pure {preconditionTac}
  pure (preconditionTac, fuel)
| _ => throwUnsupportedSyntax

/-- The `progress*` tactic repeatedly applies `progress` and `split` on the goal.

Its variant `progress*?` allows automatically generating the equivalent proof script.
-/
syntax (name := progressStar) "progress" noWs ("*" <|> "*?") «progress*_args»: tactic

@[tactic progressStar]
def evalProgressStarTac : Tactic := fun stx => do
  match stx with
  | `(tactic| progress* $args:«progress*_args») =>
    let (cfg, fuel) ← parseArgs args
    evalProgressStar cfg fuel *> pure ()
  | `(tactic| progress*? $args:«progress*_args») =>
    let (cfg, fuel) ← parseArgs args
    let info ← evalProgressStar cfg fuel
    let suggestion ← info.script.toSyntax
    let suggestion ← `(tacticSeq|$(suggestion)*)
    /- TODO: do not use the Aesop helper but our own (it mentions Aesop in the message)
       See https://github.com/AeneasVerif/aeneas/issues/476 -/
    Aesop.addTryThisTacticSeqSuggestion stx suggestion (origSpan? := ← getRef)
    --TODO: if we use this the indentation is not correct
    --Meta.Tactic.TryThis.addSuggestion stx suggestion (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end ProgressStar

section Examples

open Std.WP

/--
info: Try this:

  [apply]   simp only [progress_simps]
-/
#guard_msgs in
example : True := by progress*?

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
  progress*?

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
  progress* 2

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
  progress*? 2

/--
info: Try this:

  [apply]     simp only [progress_simps]
    let* ⟨ x2, x2_post ⟩ ← U32.add_spec
    let* ⟨ x3, x3_post ⟩ ← U32.add_spec
    let* ⟨ res, res_post ⟩ ← U32.add_spec
    scalar_tac
-/
#guard_msgs in
example (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
  let v := 2 * x.val + 2 * y.val + 4
  add1 x y ⦃ z => z.val = v ⦄ := by
  unfold add1
  progress*?

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
  progress*?

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
  progress*? 3

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
  progress*?

/- Checking that if we can't prove the final goal, we do introduce names for the outputs of the last
   monadic call -/
/--
info: Try this:

  [apply]     let* ⟨ x2, x2_post ⟩ ← U32.add_spec
    let* ⟨ x3, x3_post ⟩ ← U32.add_spec
    let* ⟨ res, res_post ⟩ ← U32.add_spec
    sorry
---
error: unsolved goals
x y : U32
h : 2 * ↑x + 2 * ↑y + 4 ≤ U32.max
x2 : U32
_✝¹ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
x3 : U32
_✝ : [> let x3 ← x2 + x2 <]
x3_post : ↑x3 = ↑x2 + ↑x2
res : U32
_ : [> let res ← x3 + 4#u32 <]
res_post : ↑res = ↑x3 + 4
⊢ ↑x < 32
-/
#guard_msgs in
example (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
      add1 x y ⦃ _ => x.val < 32 ⦄ := by
  unfold add1
  progress*?

example (x y : U32) (h : x.val * y.val ≤ U32.max):
  (do
    let z0 ← x * y
    let z1 ← y * x
    massert (z1 == z0)) ⦃ _ => True ⦄ := by
    progress* by (ring_nf at *; simp [*] <;> scalar_tac)

/--
info: Try this:

  [apply]     spec_split
    · simp only [progress_simps]
    · rename_i x _
      simp only [progress_simps]
-/
#guard_msgs in
example (x : Option Nat) :
  (match x with | none => .ok 0 | some x => .ok x) ⦃ _ => True ⦄ := by
  progress*?

/--
info: Try this:

  [apply]     spec_split
    · simp only [progress_simps]
    · simp only [progress_simps]
-/
#guard_msgs in
example (x : Option α) :
  (match x with | none => .ok 0 | some _ => .ok 1) ⦃ _ => True ⦄ := by
  progress*?

/--
info: Try this:

  [apply]     spec_split
    · simp only [progress_simps]
    · simp only [progress_simps]
    · rename_i a b _ _
      simp only [progress_simps]
-/
#guard_msgs in
example (l : List Nat) :
  (match l with
   | [] | [_] => .ok 0
   | a :: b :: _ => .ok (a + b)) ⦃ _ => True ⦄ := by
  progress*?

/--
info: Try this:

  [apply]     simp only [progress_simps]
    let* ⟨ ⟩ ← core.num.U32.overflowing_add_eq.progress_spec
-/
#guard_msgs in
example (x y : U32) :
  (lift (core.num.U32.overflowing_add x y)) ⦃ (_, _) => True ⦄ := by
  progress*?

end Examples

end Aeneas
