import Aeneas.Progress.Progress
open Lean Meta Elab Tactic

namespace Aeneas

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
    }
  else if let some ma ← Meta.matchMatcherApp? e (alsoCasesOn := true) then
    return some {
      kind := .matcher ma.matcherName
      discrs := ma.discrs.zip ma.discrInfos
        |>.map fun (toExpr, discrInfo) => {toExpr, name? := discrInfo.hName?}
      branches := ma.alts.zip ma.altNumParams
        |>.map fun (toExpr, numArgs) => {toExpr, numArgs}
      matcher := ma.matcherName,
      motive := ma.motive,
      uLevels := ma.matcherLevels.toList,
      params := ma.params
    }
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
  useCase' : Bool := false

inductive TaskOrDone α where
| task (x : Task α)
| done (x : α)

def TaskOrDone.get (x : TaskOrDone α) : α :=
  match x with
  | .task x => x.get
  | .done x => x

def TaskOrDone.mk (x : α) : TaskOrDone α := .done x

inductive Script where
| split (splitStx : Syntax.Tactic) (branches : Array (Option (TSyntax `Lean.Parser.Tactic.caseArg) × Script))
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

/-- Convert the script into syntax.
    This is a blocking operation: it waits for all the sub-components of the script to be generated.
-/
partial def Script.toSyntax (script : Script) : MetaM (Array Syntax.Tactic) := do
  match script with
  | .split splitStx branches =>
    let branches ← branches.mapM fun (caseArgs, branch) => do
      let branch ← branch.toSyntax
      match caseArgs with
      | some caseArgs => `(tactic| case' $caseArgs => $branch*)
      | none => `(tactic|. $branch*)
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
    Progress.monadTelescope (← getMainTarget) fun _xs _zs program _res _post => do
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
  catch _ => pure .unknown

partial def evalProgressStar (cfg: Config) : TacticM Result :=
  withMainContext do focus do
  withTraceNode `Progress (fun _ => do pure m!"evalProgressStar") do
  -- Simplify the target
  let (info, mvarId) ← simplifyTarget
  -- Continue
  match mvarId with
  | some _ =>
    let info' ← traverseProgram cfg
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

  traverseProgram (cfg : Config): TacticM Info := do
    withMainContext do
    withTraceNode `Progress (fun _ => do pure m!"traverseProgram") do
    traceGoalWithNode "current goal"
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
        let restInfo ← traverseProgram cfg
        return info ++ restInfo
    | .switch bfInfo => do
      let contsTaggedVals ←
        bfInfo.branches.mapM fun br => do
          Utils.lambdaTelescopeN br.toExpr br.numArgs fun xs _ => do
            let names ← xs.mapM (·.fvarId!.getUserName)
            return names
      let (branchGoals, mkStx) ← onBif cfg bfInfo contsTaggedVals
      withTraceNode `Progress (fun _ => do pure m!"exploring branches") do
      /- Continue exploring from the subgoals -/
      let branchInfos ← branchGoals.mapM fun mainGoal => do
        setGoals [mainGoal]
        let restInfo ← traverseProgram cfg
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
      /- Update the main goal, if necessary -/
      let ids ← getIdsFromUsedTheorem varName.eraseMacroScopes usedTheorem
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

  onBif (cfg : Config) (bfInfo : Bifurcation.Info) (toBeProcessed : Array (Array Name)): TacticM (List MVarId × (List Info → TacticM Info)) := do
    withTraceNode `Progress (fun _ => pure m!"onBif") do
    trace[Progress] "onBif: encountered {bfInfo.kind}"
    if (←getGoals).isEmpty then
      trace[Progress] "onBif: no goals to be solved!"
      -- Tactic.focus fails if there are no goals to be solved.
      return ({}, fun infos => assert! (infos.length == 0); pure {})
    Tactic.focus do
      let splitStx ← `(tactic| split)
      evalSplit splitStx
      --
      let subgoals ← getUnsolvedGoals
      trace[Progress] "onBif: Bifurcation generated {subgoals.length} subgoals"
      unless subgoals.length == toBeProcessed.size do
        throwError "onBif: Expected {toBeProcessed.size} cases, found {subgoals.length}"

      let infos_mkBranchesStx ← (subgoals.zip toBeProcessed.toList).mapM fun (sg, names) => do
        setGoals [sg]
        -- TODO: rename the variables
        let mkStx (branchScript : Script) : TacticM (Option (TSyntax `Lean.Parser.Tactic.caseArg) × Script) := do
          let caseArgs ←
            if cfg.useCase' then
              pure (some (makeCaseArgs (← sg.getTag) names))
            else pure none
          pure (caseArgs, branchScript)
        pure (sg,  mkStx)
      let (infos, mkBranchesStx) := infos_mkBranchesStx.unzip

      let mkStx (infos : List Info) : TacticM Info := do
        unless infos.length == mkBranchesStx.length do
          throwError "onBif: Expected {mkBranchesStx.length} infos, found {infos.length}"
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
    try some <$> Progress.evalProgressCore cfg.async none (some (.str .anonymous "_")) none #[] cfg.preconditionTac
    catch _ => pure none

  getIdsFromUsedTheorem name usedTheorem: TacticM (Array _) := do
    withTraceNode `Progress (fun _ => do pure m!"getIdsFromUsedTheorem") do
    let some thm ← usedTheorem.getType
      | throwError "Could not infer proposition of {usedTheorem}"
    let (numElem, numPost) ← Progress.monadTelescope thm
      fun _xs zs _program _res postconds => do
        let numPost := Utils.numOfConjuncts <$> postconds |>.getD 0
        trace[Progress] "Number of conjuncts for `{←liftM (Option.traverse ppExpr postconds)}` is {numPost}"
        pure (zs.size, numPost)
    return makeIds (base := name) numElem numPost

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
    let binderIdents := names.map fun n => if n.isInternalDetail
      then mkNode ``Lean.binderIdent #[mkHole mkNullNode]
      else mkNode ``Lean.binderIdent #[mkIdent n]
    Lean.mkNode ``Lean.Parser.Tactic.caseArg #[tag, mkNullNode (args := binderIdents)]

syntax «progress*_args» := ("by" tacticSeq)?
def parseArgs: TSyntax `Aeneas.ProgressStar.«progress*_args» → CoreM Config
| `(«progress*_args»| $[by $preconditionTac:tacticSeq]?) => do
  withTraceNode `Progress (fun _ => pure m!"parseArgs") do
  match preconditionTac with
  | none => return {preconditionTac := none}
  | some preconditionTac => do
    let preconditionTac : Syntax.Tactic := ⟨preconditionTac.raw⟩
    trace[Progress] "preconditionTac: {preconditionTac}"
    return {preconditionTac}
| _ => throwUnsupportedSyntax

elab "progress" noWs "*" stx:«progress*_args»: tactic => do
  let cfg ← parseArgs stx
  evalProgressStar cfg *> pure ()

elab tk:"progress" noWs "*?" stx:«progress*_args»: tactic => do
  let cfg ← parseArgs stx
  let info ← evalProgressStar cfg
  let suggestion ← info.script.toSyntax
  let suggestion ← `(tacticSeq|$(suggestion)*)
  Aesop.addTryThisTacticSeqSuggestion tk suggestion (origSpan? := ← getRef)

end ProgressStar

section Examples

/--
info: Try this:
simp only [progress_simps]
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
  let* ⟨ x2, x2_post ⟩ ← U32.add_spec
  let* ⟨ x3, x3_post ⟩ ← U32.add_spec
  let* ⟨ res, res_post ⟩ ← U32.add_spec
-/
#guard_msgs in
example (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
  ∃ z, add1 x y = ok z := by
  unfold add1
  progress*?

/--
info: Try this:
  simp only [progress_simps]
  let* ⟨ x2, x2_post ⟩ ← U32.add_spec
  let* ⟨ x3, x3_post ⟩ ← U32.add_spec
  let* ⟨ res, res_post ⟩ ← U32.add_spec
  scalar_tac
-/
#guard_msgs in
example (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
  let v := 2 * x.val + 2 * y.val + 4
  ∃ z, add1 x y = ok z ∧ z.val = v:= by
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
  split
  . let* ⟨ x2, x2_post ⟩ ← U32.add_spec
    let* ⟨ x3, x3_post ⟩ ← U32.add_spec
    let* ⟨ res, res_post ⟩ ← U32.add_spec
  . let* ⟨ y, y_post ⟩ ← U32.add_spec
    let* ⟨ res, res_post ⟩ ← U32.add_spec
-/
#guard_msgs in
example b (x y : U32) (h : 2 * x.val + 2 * y.val + 4 ≤ U32.max) :
      ∃ z, add2 b x y = ok z := by
  unfold add2
  progress*?

/--
info: Try this:
  split
  . let* ⟨ x2, x2_post ⟩ ← U32.add_spec
    · sorry
    let* ⟨ x3, x3_post ⟩ ← U32.add_spec
    · sorry
    let* ⟨ res, res_post ⟩ ← U32.add_spec
    · sorry
  . let* ⟨ y, y_post ⟩ ← U32.add_spec
    · sorry
    let* ⟨ res, res_post ⟩ ← U32.add_spec
    · sorry
---
error: unsolved goals
case isTrue.hmax
b : Bool
x y : U32
h✝ : b = true
⊢ ↑x + ↑y ≤ U32.max

case intro.hmax
b : Bool
x y : U32
h✝ : b = true
x2 : U32
_ : [> let x2 ← x + y <]
x2_post : ↑x2 = ↑x + ↑y
⊢ ↑x2 + ↑x2 ≤ U32.max

case intro.hmax
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

case isFalse.hmax
b : Bool
x y : U32
h✝ : ¬b = true
⊢ ↑x + ↑y ≤ U32.max

case intro.hmax
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
      ∃ z, add2 b x y = ok z := by
  unfold add2
  progress*?

example (x y : U32) (h : x.val * y.val ≤ U32.max):
  (do
    let z0 ← x * y
    let z1 ← y * x
    massert (z1 == z0)) = ok () := by
    progress* by (ring_nf at *; simp [*] <;> scalar_tac)

end Examples

end Aeneas
