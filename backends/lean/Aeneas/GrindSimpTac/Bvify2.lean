import Aeneas.Grind.Init
import Aeneas.GrindSimpTac.MonoGrindState
import Aeneas.GrindSimpTac.init
import Aeneas.ScalarTac.CondSimpTac -- TODO: simplify this import

import Aeneas.Bvify.Bvify
import Aeneas.SimpBoolProp.SimpBoolProp
import Aeneas.ScalarTac.Lemmas

/-!
# `grindSimpTac`: simp with grind as a discharger

The core logic (discharge + simp) lives in `GrindM` for efficiency: the grind
context (methods, congruence theorem cache, hash-consing state) is set up once
and shared across all discharge calls from simp.

**Performance optimization — pre-built base GoalState:**
Before calling `simp`, we build a "base" GoalState with all hypotheses already
canonicalized and internalized in the e-graph (`MonoGrindState.initializeFromMVar`).
Each discharge call then reuses this pre-built state instead of re-canonicalizing
all hypotheses from scratch. The `solve` function only needs to process the
discharge target (via `byContra` + `intro` of `¬target`), not all hypotheses.

Hypotheses can optionally be simplified with a preprocessing simpset before being
added to the grind e-graph.
-/

namespace Aeneas.GrindSimpTac

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Utils

initialize registerTraceClass `GrindSimpTac

/-- Arguments for `grindSimpTac`. Mirrors `ScalarTac.CondSimpArgs` but is kept
    separate so the two modules can evolve independently. -/
structure GrindSimpArgs where
  simpThms : Array SimpTheorems := #[]
  simprocs : Simp.SimprocsArray := #[]
  declsToUnfold : Array Name := #[]
  letDeclsToUnfold : Array FVarId := #[]
  addSimpThms : Array Name := #[]
  addSimprocs : Array Name := #[]
  hypsToUse : Array FVarId := #[]

def GrindSimpArgs.toSimpArgs (args : GrindSimpArgs) : Simp.SimpArgs := {
    simpThms := args.simpThms,
    simprocs := args.simprocs,
    declsToUnfold := args.declsToUnfold,
    letDeclsToUnfold := args.letDeclsToUnfold,
    addSimpThms := args.addSimpThms,
    addSimprocs := args.addSimprocs,
    hypsToUse := args.hypsToUse }


/- /-- Format a suggestion string from the used simp theorems.
    Produces something like `tacPrefix only [thm1, thm2, ↓thm3] locSuffix`.

    This is adapted from `Lean.Elab.Tactic.mkSimpOnly`. -/
private def formatSuggestion (tacPrefix : String) (locSuffix : String)
    (usedSimps : Simp.UsedSimps) : MetaM Syntax := do
  let env ← getEnv
  let lctx ← getLCtx
  let mut args : Array String := #[]
  for thm in usedSimps.toArray do
    match thm with
    | .decl declName post inv =>
      if env.contains declName && !Lean.Meta.Match.isMatchEqnTheorem env declName then
        let name ← Lean.unresolveNameGlobalAvoidingLocals declName
        let s := match post, inv with
          | true,  true  => s!"← {name}"
          | true,  false => s!"{name}"
          | false, true  => s!"↓ ← {name}"
          | false, false => s!"↓ {name}"
        args := args.push s
    | .fvar fvarId =>
      if let some ldecl := lctx.find? fvarId then
        if !ldecl.userName.isInaccessibleUserName && !ldecl.userName.hasMacroScopes then
          args := args.push s!"{ldecl.userName}"
    | .stx _ _ | .other _ => pure ()
  let argStr := ", ".intercalate args.toList
  let loc := if locSuffix.isEmpty then "" else s!" {locSuffix}"
  return s!"{tacPrefix} only [{argStr}]{loc}"
-/


/-- Minimal discharger: introduces the target into the pre-built e-graph, asserts
    propagated facts, then loops only the linear arithmetic solvers (linarith + lia).
    No case splits, no tactic checking, no AC/CommRing solvers.
    Optionally includes e-matching (`useEmatch`) and model-based theory combination (`useMbtc`). -/
private def solveMinimal (goal : Lean.Meta.Grind.Goal)
    (useEmatch : Bool := false) (useMbtc : Bool := false)
    (maxIterations : Nat := 1000) : Lean.Meta.Grind.GrindM (Option Lean.Meta.Grind.Goal) := do
  let arith := Lean.Meta.Grind.Action.linarith.andAlso Lean.Meta.Grind.Action.lia
  let instantiate := Lean.Meta.Grind.Action.instantiate
  let mbtc := Lean.Meta.Grind.Action.mbtc
  let step : Lean.Meta.Grind.Action :=
    match useEmatch, useMbtc with
    | false, false => arith
    | true, false => arith <|> instantiate
    | false, true => arith <|> mbtc
    | true, true => arith <|> instantiate <|> mbtc
  let action := Lean.Meta.Grind.Action.intros 0 >> Lean.Meta.Grind.Action.assertAll >> step.loop maxIterations
  match (← action.run goal) with
  | .closed _ => return none
  | .stuck gs =>
    let goal :: _ := gs | return some goal
    return goal

/-- Discharge using a pre-built MonoGrindState.
    The base state has all hypotheses already canonicalized and internalized in
    the e-graph. For each discharge call, we construct a Goal from this base
    state + the discharge mvar, so only the target needs canonicalization.

    When `contextual` simp is enabled, the discharge mvar may have fresh local
    declarations (introduced when simp dives into quantifiers). These are
    internalized via `addFreshLocalDecls` before solving.

    When `useMinimalSolver` is true, uses `solveMinimal` (only linarith + lia,
    no case splits, no tactic checking) instead of the full `solve`. -/
private def grindDischargeWithBase (baseState : MonoGrindState)
    (preprocessCtx : Simp.Context) (preprocessSimprocs : Simp.SimprocsArray)
    (mvarId : MVarId) (useMinimalSolver : Bool) : Lean.Meta.Grind.GrindM Bool := do
  withTraceNode `GrindSimpTac (fun _ => pure m!"grindDischargeWithBase") do
  -- Note: we intentionally do NOT use `withProtectedMCtx` here.
  -- `withProtectedMCtx` enters `withNewMCtxDepth`, which makes the metavariables
  -- stored in the MonoGrindState's e-graph invisible ("unknown metavariable" errors).
  -- Since we reuse the pre-built MonoGrindState across discharge calls, we must stay
  -- in the same mctx depth.
  Lean.Meta.Grind.withGTransparency do
    mvarId.withContext do
    trace[GrindSimpTac] "goal (name: {mvarId.name}): {mvarId}"
    -- Internalize fresh local declarations (from contextual simp)
    let state ← baseState.addFreshLocalDecls mvarId preprocessCtx preprocessSimprocs
    -- Solve
    let goal : Lean.Meta.Grind.Goal := { toGoalState := state.goalState, mvarId }
    let failure? ←
      if useMinimalSolver then solveMinimal goal
      else Lean.Meta.Grind.solve goal
    return failure?.isNone

/-- Preprocess `hypsToUse`: for each prop hypothesis, simplify its type with the
    given simpset. Only introduce a new hypothesis (with `.pp` suffix) when the
    type actually changes. Returns the updated mvarId, updated args (with both
    original and preprocessed hyps in `hypsToUse`), and the FVarIds of the newly
    introduced hypotheses (for cleanup after simp). -/
private def preprocessHypsToUse (mvarId : MVarId) (args : GrindSimpArgs)
    (ppHypsToUseSimpThms : Array SimpTheorems) (ppHypsToUseSimprocs : Simp.SimprocsArray) :
    MetaM (MVarId × GrindSimpArgs × Array FVarId) := do
  if ppHypsToUseSimpThms.isEmpty || args.hypsToUse.isEmpty then
    return (mvarId, args, #[])
  let ppConfig : Simp.Config := { failIfUnchanged := false, maxDischargeDepth := 0 }
  let congrTheorems ← getSimpCongrTheorems
  let ctx ← Simp.mkContext ppConfig (simpTheorems := ppHypsToUseSimpThms) congrTheorems
  let toAssert ← mvarId.withContext do
    let mut toAssert : Array Hypothesis := #[]
    for fvarId in args.hypsToUse do
      let ldecl ← fvarId.getDecl
      if ldecl.isImplementationDetail then continue
      if !(← isProp ldecl.type) then continue
      let type ← instantiateMVars ldecl.type
      let (simpResult, _) ← Lean.Meta.simp type ctx ppHypsToUseSimprocs
      let simplifiedType ← instantiateMVars simpResult.expr
      -- Only introduce a new hyp if the type actually changed
      if simplifiedType != type then
        let proof ← match simpResult.proof? with
          | some p => pure (mkApp4 (mkConst ``Eq.mp [0]) type simplifiedType p ldecl.toExpr)
          | none => pure ldecl.toExpr
        toAssert := toAssert.push { userName := ldecl.userName ++ `pp, type := simplifiedType, value := proof }
    pure toAssert
  if toAssert.isEmpty then
    return (mvarId, args, #[])
  let (newIds, mvarId) ← mvarId.assertHypotheses toAssert
  return (mvarId, { args with hypsToUse := args.hypsToUse ++ newIds }, newIds)

syntax simpArgs := (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?

/-- Core simp+grind logic in GrindM.
    Runs `simp` on the given goal with grind as the discharger.

    Uses `MonoGrindState` to build a pre-built GoalState with all hypotheses
    internalized in the e-graph (optionally simplified with the preprocessing
    simpset). After all hypotheses are processed, e-matching saturation and
    arithmetic pre-derivation run once. Each discharge call reuses this
    pre-built state.

    When `ppHypsToUseSimpThms` is non-empty, `args.hypsToUse` are duplicated,
    the duplicates are simplified with that simpset, and the simplified copies
    are used for the main simp pass (then cleared afterwards). -/
private def grindSimpCoreM
    (mvarId : MVarId) (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool)
    (ppSimpThms : Array SimpTheorems) (ppSimprocs : Simp.SimprocsArray)
    (genPreprocess : Option Nat) (useMinimalSolver : Bool)
    (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) :
    Lean.Meta.Grind.GrindM (Option (Array FVarId × MVarId) × Simp.Stats) := do
  withTraceNode `GrindSimpTac (fun _ => pure m!"grindSimpCoreM") do
  -- Build MonoGrindState from the main goal
  let monoState ← MonoGrindState.initializeFromMVar mvarId ppSimpThms ppSimprocs
  let monoState ← monoState.deriveFacts (genPreprocess := genPreprocess)
  -- Build preprocessing context for fresh local decls during discharge
  /- We keep the default simp congruence lemmas: they should be generally useful, and at this stage we
     do not expect them to pollute the context. -/
  let congrTheorems ← getSimpCongrTheorems
  let ppConfig : Simp.Config := { failIfUnchanged := false, maxDischargeDepth := 0 }
  let preprocessCtx ← Simp.mkContext ppConfig (simpTheorems := ppSimpThms) congrTheorems
  mvarId.withContext do
  /-let discharge ← Simp.tacticToDischarge do
    let mvar ← getMainGoal
    grindDischargeWithBase monoState preprocessCtx ppSimprocs mvar useMinimalSolver

  let discharge : Simp.Discharge := fun e => do
    withTraceNode `GrindSimpTac (fun _ => pure m!"discharge") do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `grind.discharger
    trace[GrindSimpTac] "goal (mvar name: {mvar.mvarId!.name}): {mvar}:\n{mvar.mvarId!}"
    try
      let ok ← grindDischargeWithBase monoState preprocessCtx ppSimprocs mvar.mvarId! useMinimalSolver
      if !ok then return none
      let proof ← instantiateMVars mvar
      if proof.hasExprMVar then
        trace[GrindSimpTac] "No proof"
        return none
      trace[GrindSimpTac] "Found proof"
      return some proof
    catch e =>
      trace[GrindSimpTac] "Unexpected error: {e.toMessageData}"
      return none
  withTraceNode `GrindSimpTac (fun _ => pure m!"simpGoal (with grind discharge)") do
  Lean.Meta.simpGoal mvarId ctx (simprocs := simprocs) (simplifyTarget := simplifyTarget)
        (discharge? := some discharge) (fvarIdsToSimp := fvarIdsToSimp)-/

  controlAt MetaM fun runInMetaM => do
    mvarId.withContext do
    let discharge : Simp.Discharge := fun e => do
      withTraceNode `GrindSimpTac (fun _ => pure m!"discharge") do
      let mvar ← mkFreshExprSyntheticOpaqueMVar e `grind.discharger
      trace[GrindSimpTac] "goal (mvar name: {mvar.mvarId!.name}): {mvar}:\n{mvar.mvarId!}"
      try
        let ok ← runInMetaM (grindDischargeWithBase monoState preprocessCtx ppSimprocs mvar.mvarId! useMinimalSolver)
        if !ok then
          trace[GrindSimpTac] "No proof"
          return none
        let proof ← instantiateMVars mvar
        if proof.hasExprMVar then
          trace[GrindSimpTac] "No proof"
          return none
        trace[GrindSimpTac] "Found proof"
        return some proof
      catch e =>
        trace[GrindSimpTac] "Unexpected error: {e.toMessageData}"
        return none
    withTraceNode `GrindSimpTac (fun _ => pure m!"simpGoal (with grind discharge)") do

      /-let discharge? := some discharge
      let mut stats := {}
      for fvarId in fvarIdsToSimp do
        let localDecl ← fvarId.getDecl
        let type ← instantiateMVars localDecl.type
        let ctx := ctx.setSimpTheorems <| ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId)
        let (r, stats') ← Lean.Meta.simp type ctx simprocs discharge? stats
        stats := stats'
        match r.proof? with
        | none => trace[GrindSimpTac] "Could not simplify: {Expr.fvar fvarId} : {type}"
        | some _ => trace[GrindSimpTac] "Simplified: {Expr.fvar fvarId} : {type}\nto: {r.expr}"
      -- Simplify the target
      if simplifyTarget then
        let type ← instantiateMVars (← mvarId.getType)
        let (r, stats') ← Lean.Meta.simp type ctx simprocs discharge? stats
        stats := stats'
        match r.proof? with
        | none => trace[GrindSimpTac] "Could not simplify target: {type}"
        | some _ => trace[GrindSimpTac] "Simplified target: {type}\nto: {r.expr}"-/

      Lean.Meta.simpGoal mvarId ctx (simprocs := simprocs) (simplifyTarget := simplifyTarget)
        (discharge? := some discharge) (fvarIdsToSimp := fvarIdsToSimp)

/-- Main tactic: simp with grind as a discharger.

    The core logic (discharge + simp) runs in `GrindM`:
    - The grind context (methods, congruence theorem cache, hash-consing state)
      is set up once and shared across all discharge calls
    - The discharge function calls back into GrindM via `controlAt MetaM`

    Parameters:
    - `grindConfig`, `withGroundSimprocs`, `extensions`: configure the grind discharger
    - `simpConfig`: simp configuration
    - `args`: simp lemmas / simprocs / definitions to unfold
    - `loc`: where to simplify (target, hypotheses, or everywhere)
    - `preprocessSimpThms`/`preprocessSimprocs`: simpset used to simplify hypotheses
      before adding them to the grind e-graph
    - `preprocessHypsToUseSimpThms`/`preprocessHypsToUseSimprocs`: simpset used to
      preprocess `hypsToUse` before the main simp pass
    - `genPreprocess`: if provided, overrides `config.gen` (max e-matching generation)
      during the preprocessing `deriveFacts` phase. The normal `config.gen` is used
      when discharging proof obligations.
    - `useMinimalSolver`: use minimal solver (linarith + lia only) instead of full grind solve (default false)
    - `suggestion`: when `true`, it means we should generate a `simp_... only [...]` suggestion: we
      output the corresponding simp args.

    If `suggesttion
-/
def grindSimpTac
    (grindConfig : Lean.Grind.Config)
    (withGroundSimprocs : Bool)
    (extensions : Lean.Meta.Grind.ExtensionStateArray)
    (simpConfig : Simp.Config)
    (args : GrindSimpArgs)
    (loc : Utils.Location)
    (addSimpThms : TacticM (Array FVarId))
    (preprocessSimpThms : Array SimpTheorems := #[])
    (preprocessSimprocs : Simp.SimprocsArray := #[])
    (preprocessHypsToUseSimpThms : Array SimpTheorems := #[])
    (preprocessHypsToUseSimprocs : Simp.SimprocsArray := #[])
    (genPreprocess : Option Nat := none)
    (useMinimalSolver : Bool := false)
    (simpArgsStx : Option (TSyntax ``simpArgs) := none)
    : TacticM (Option (Array FVarId) × Simp.Stats) := do
  Elab.Tactic.focus do
  withTraceNode `GrindSimpTac (fun _ => pure m!"grindSimpTac") do
  withMainContext do
  /- Introduce the additional simp theorems to use -/
  let addSimpThms ← addSimpThms
  withMainContext do
  /- Preprocess hypsToUse -/
  let mvarId ← getMainGoal
  let (mvarId, args, newHypIds) ←
    preprocessHypsToUse mvarId args preprocessHypsToUseSimpThms preprocessHypsToUseSimprocs
  setGoals [mvarId]
  trace[GrindSimpTac] "Goal after preprocessing the hyps to use: {← getMainGoal}"
  /- Initialize the simp context and elaborate the syntax (we have to do this here
    because `elabSimpArgs` lives in `TacticM`, not `MetaM`) -/
  let simpArgs := args.toSimpArgs
  let simpArgs := { simpArgs with hypsToUse := simpArgs.hypsToUse ++ addSimpThms }
  let (ctx, simprocs) ← Simp.mkSimpCtx true simpConfig .simp simpArgs
  let (ctx, simprocs) ← do
      match simpArgsStx with
      | none => pure (ctx, simprocs)
      | some stx => do
        let { ctx, simprocs, simpArgs := _ } ←
          -- This is annoying: `elabSimpArgs` lives in `TacticM`, meaning we
          Lean.Elab.Tactic.elabSimpArgs stx.raw.getArgs[0]! ctx simprocs (eraseLocal := true) .simp
        pure (ctx, simprocs)
  -- Build the grind parameters
  let params ← Aeneas.Grind.mkParams grindConfig extensions withGroundSimprocs
  --
  let (fvarIdsToSimp, simplifyTarget) ← match loc with
    | .targets hyps target => pure (hyps, target)
    | .wildcard => do pure (← mvarId.getNondepPropHyps, true)
  -- Run `simp` with `grind` as a discharger
  let (result?, stats) ← Lean.Meta.Grind.GrindM.run
    (grindSimpCoreM mvarId fvarIdsToSimp simplifyTarget
      preprocessSimpThms preprocessSimprocs
      genPreprocess useMinimalSolver
      ctx simprocs) params
  -- Replace the goal and clear the duplicated `hypsToUse` as well as the additional theorem
  let fvars ←
    match result? with
    | none =>
      trace[GrindSimpTac] "Goal proved!"
      replaceMainGoal []; pure none
    | some (fvars, mvarId) =>
      mvarId.withContext do
      let toClear := newHypIds ++ addSimpThms
      trace[GrindSimpTac] "Resulting goal: {mvarId}\nAssumptions to clear: {toClear.map Expr.fvar}"
      let mvarId ← mvarId.tryClearMany toClear
      replaceMainGoal [mvarId]
      pure (some fvars)
  --
  pure (fvars, stats)

/-- "Standard" way of calling `grindSimpTac` -/
def standardGrindSimpTac (loc : Utils.Location)
    («only» : Bool := false)
    (simps : SimpTheorems × Simprocs)
    (hypsSimps : SimpTheorems × Simprocs)
    (simpArgsStx : Option (TSyntax ``simpArgs))
    (addSimpThms : TacticM (Array FVarId) := pure #[])
    : TacticM Unit := do
  let (simpThms, simprocs) := simps
  let (hypsSimpThms, hypsSimprocs) := hypsSimps
  let simpThms ← if «only» then pure #[] else
    pure #[simpThms, ← SimpBoolProp.simpBoolPropSimpExt.getTheorems]
  let simprocs ← if «only» then pure #[] else
    pure #[simprocs, ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs]
  let simpArgs : GrindSimpArgs := {
    simpThms, simprocs,
  }
  -- TODO: make this a parameter
  let grindConfig : Lean.Grind.Config := {
    splits := 4, ematch := 1, splitMatch := false, splitIte := false,
    splitIndPred := false, funext := false, gen := 2, instances := 1000,
    canonHeartbeats := 1000
  }
  let extensions := #[Grind.agrindExt.getState (← getEnv)]
  let _ ←
    grindSimpTac grindConfig (withGroundSimprocs := true) extensions
      { maxDischargeDepth := 2, failIfUnchanged := false, contextual := true }
      simpArgs loc addSimpThms
      (preprocessSimpThms := #[← ScalarTac.scalarTacSimpExt.getTheorems,
                                ← SimpBoolProp.simpBoolPropSimpExt.getTheorems])
      (preprocessSimprocs := #[← ScalarTac.scalarTacSimprocExt.getSimprocs,
                                ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs])
      (preprocessHypsToUseSimpThms := #[hypsSimpThms,
                                        ← SimpBoolProp.simpBoolPropSimpExt.getTheorems])
      (preprocessHypsToUseSimprocs := #[hypsSimprocs,
                                        ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs])
      (genPreprocess := some 2)
      (simpArgsStx := simpArgsStx)
  pure ()


open Aeneas.Bvify

syntax (name := gsimp_lists) "gbvify" colGt term "only"? simpArgs (location)? : tactic
syntax (name := gsimp_lists?) "gbvify?" colGt term "only"? simpArgs (location)? : tactic

private def gbvifyElab (qmark : Bool)
  (n : Expr)
  (onlyTk : Option Syntax)
  (simpArgsStx : Option (TSyntax ``simpArgs))
  (loc : Option (TSyntax `Lean.Parser.Tactic.location))
  (stx : stx)
  : TacticM Unit := do
  withMainContext do
  let loc ← Utils.parseOptLocation loc
  let «only» := onlyTk.isSome
  let simpThms ← bvifySimpExt.getTheorems
  let simprocs ← bvifySimprocExt.getSimprocs
  let hypsSimpThms ← bvifyHypsSimpExt.getTheorems
  let hypsSimprocs ← bvifyHypsSimprocExt.getSimprocs
  let addSimpThms := bvifyAddSimpThms n
  standardGrindSimpTac loc «only» (simpThms, simprocs)
    (hypsSimpThms, hypsSimprocs) simpArgsStx addSimpThms

elab_rules : tactic
  | `(tactic| gbvify $n $[only%$onlyTk]? $args $[$loc:location]?) => do
    let n ← Elab.Term.elabTerm n (Expr.const ``Nat [])
    gbvifyElab false n onlyTk args loc (← getRef)
  | `(tactic| gbvify? $n $[only%$onlyTk]? $args $[$loc:location]?) => do
    let n ← Elab.Term.elabTerm n (Expr.const ``Nat [])
    gbvifyElab true n onlyTk args loc (← getRef)

open Aeneas Aeneas.Arith Aeneas.Std

example (byte : U8) : 8 ∣ (byte &&& 16#u8).val := by
  --have : (byte &&& 16#u8).val < 2 ^ 8 := by agrind (gen := 1)

  --have : (byte &&& 16#u8).val % 8 < 2^8 := by agrind (gen := 1)
  --set_option trace.profiler true in
  set_option trace.GrindSimpTac true in
  set_option trace.MonoGrindState true in
  gbvify 8
  -- we shoud have: (byte.bv &&& 16#8) % 8#8 = 0#8
  bv_decide

#check Grind.Goal.internalize
#check Grind.Goal.internalizeAll
#check Grind.Goal.introN

-- Grouped together
--#check Lean.Meta.Grind.discharge?
#check Grind.GrindM.run
#check Sym.simp

/-
When I look at Grind.GrindM.run I see that it sets simp methods, with in particular a default discharger
that uses `rfl`. When are the simp methods, and the discharger, used inside of `grind`?
-/

#check Lean.Meta.Sym.Simp.Theorem.rewrite
#check Lean.Meta.Sym.Simp.Theorems.rewrite

end Aeneas.GrindSimpTac
