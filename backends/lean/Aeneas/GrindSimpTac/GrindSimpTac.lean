import Aeneas.GrindSimpTac.Init
import Aeneas.Grind.Init

/-!
# `grindSimpTac`: simp with grind as a discharger

The core logic (discharge + simp) lives in `GrindM` for efficiency: the grind
context (methods, congruence theorem cache, hash-consing state) is set up once
and shared across all discharge calls from simp.

**Performance optimization — pre-built base GoalState:**
Before calling `simp`, we build a "base" GoalState with all hypotheses already
canonicalized and internalized in the e-graph (`buildBaseGoalState`). Each
discharge call then reuses this pre-built state instead of re-canonicalizing
all hypotheses from scratch. The `solve` function only needs to process the
discharge target (via `byContra` + `intro` of `¬target`), not all hypotheses.

When `preprocessSimpArgs` is provided, the tactic:
1. Duplicates all prop assumptions
2. Simplifies them with the given simp args (no discharger)
3. Runs `simp_all` with the same simp args to cross-simplify hypotheses
4. Runs `simp (discharger := grind [grindset]) [simpset] at loc`
5. Clears the duplicated assumptions to restore a clean state

When `preprocessSimpArgs` is `none`, this is just:
  `simp (discharger := grind [grindset]) [simpset] at loc`
-/

namespace Aeneas.GrindSimpTac

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Utils

/-- Build a base GoalState with all hypotheses canonicalized and internalized
    in the e-graph. This is called once before `simp`, so each discharge call
    can reuse the pre-built e-graph instead of re-canonicalizing all hypotheses.

    We use `revert := false` (regardless of the grind config) so hypotheses
    stay in the local context and are processed by `processHypotheses`.

    When `saturationRounds > 0`, we also run e-matching on the base e-graph
    to pre-saturate it with derived facts. This amortizes e-matching cost
    across all discharge calls. -/
private def buildBaseGoalState (mvarId : MVarId) (saturationRounds : Nat := 1) :
    Lean.Meta.Grind.GrindM Lean.Meta.Grind.GoalState := do
  mvarId.withContext do
  -- Create a temporary mvar (same lctx, dummy target) to avoid modifying the main goal
  let tmpMvar ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True) `grind_base
  let tmpMvarId := tmpMvar.mvarId!
  -- Don't revert — we want hypotheses in the lctx for processHypotheses
  let tmpMvarId ← tmpMvarId.unfoldReducible
  let tmpMvarId ← tmpMvarId.betaReduce
  appendTagSuffix tmpMvarId `grind_base
  let goal ← Lean.Meta.Grind.mkGoalCore tmpMvarId
  -- Internalize all hypotheses into the e-graph (this is where canonicalization happens)
  let goal ← Lean.Meta.Grind.processHypotheses goal
  -- Optionally pre-saturate the e-graph with e-matching.
  -- Each round finds new pattern matches from hypothesis terms and adds derived facts.
  let goal ← saturateEmatch goal saturationRounds
  return goal.toGoalState
where
  saturateEmatch (goal : Lean.Meta.Grind.Goal) : Nat → Lean.Meta.Grind.GrindM Lean.Meta.Grind.Goal
    | 0 => return goal
    | n + 1 => do
      if goal.inconsistent then return goal
      let (progress, goal) ← Lean.Meta.Grind.GoalM.run goal Lean.Meta.Grind.ematch
      if !progress then return goal
      -- Process the new facts derived by e-matching
      let goal ← Lean.Meta.Grind.GoalM.run' goal Lean.Meta.Grind.processNewFacts
      if goal.inconsistent then return goal
      saturateEmatch goal n

/-- Discharge using a pre-built base GoalState.
    The base state has all hypotheses already canonicalized and internalized in
    the e-graph. For each discharge call, we construct a Goal from this base
    state + the discharge mvar, so only the target needs canonicalization.

    The `solve` function handles the target via:
    - `byContra?` converts `⊢ P` to `⊢ ¬P → False`
    - `intro` introduces `h : ¬P` and adds it to the pre-built e-graph
    - The search loop checks for inconsistency (True = False) -/
private def grindDischargeWithBase (baseState : Lean.Meta.Grind.GoalState)
    (mvarId : MVarId) : Lean.Meta.Grind.GrindM Bool := do
  -- Use revert := false since hypotheses are already processed in baseState
  let config := { (← Lean.Meta.Grind.getConfig) with revert := false }
  Lean.Meta.Grind.withProtectedMCtx config mvarId fun mvarId' =>
    Lean.Meta.Grind.withGTransparency do
      -- Construct Goal from base state + discharge mvar.
      -- The e-graph already has all hypotheses. nextDeclIdx is past all existing
      -- hypotheses, so solve's intros will only process the target.
      let goal : Lean.Meta.Grind.Goal := { toGoalState := baseState, mvarId := mvarId' }
      let failure? ← Lean.Meta.Grind.solve goal
      return failure?.isNone

/-- Core simp+grind logic in GrindM.
    Runs `simp` on the given goal with grind as the discharger.
    Pre-builds a base GoalState with all hypotheses, then each discharge call
    reuses it via `controlAt MetaM` to bridge GrindM→SimpM. -/
private def grindSimpCoreM (simpConfig : Simp.Config) (args : GrindSimpArgs)
    (mvarId : MVarId) (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool)
    (baseSaturationRounds : Nat) :
    Lean.Meta.Grind.GrindM (Option (Array FVarId × MVarId) × Simp.Stats) := do
  -- Pre-build base GoalState with all hypotheses canonicalized and in the e-graph
  let baseGoalState ← buildBaseGoalState mvarId baseSaturationRounds
  controlAt MetaM fun runInMetaM => do
    mvarId.withContext do
    let discharge : Simp.Discharge := fun e => do
      let mvar ← mkFreshExprSyntheticOpaqueMVar e `grind.discharger
      try
        let ok ← runInMetaM (grindDischargeWithBase baseGoalState mvar.mvarId!)
        if !ok then return none
        let proof ← instantiateMVars mvar
        if proof.hasExprMVar then return none
        return some proof
      catch _ =>
        return none
    let simpArgs := args.toSimpArgs
    let (ctx, simprocs) ← Simp.mkSimpCtx true simpConfig .simp simpArgs
    Lean.Meta.simpGoal mvarId ctx (simprocs := simprocs) (simplifyTarget := simplifyTarget)
      (discharge? := some discharge) (fvarIdsToSimp := fvarIdsToSimp)

/-- Run the GrindM simp core at a given location, translating the result back to TacticM. -/
private def runGrindSimpAt (params : Lean.Meta.Grind.Params)
    (simpConfig : Simp.Config) (args : GrindSimpArgs)
    (loc : Utils.Location) (baseSaturationRounds : Nat) : TacticM Unit := do
  withMainContext do
  let mvarId ← getMainGoal
  let (fvarIdsToSimp, simplifyTarget) ← match loc with
    | .targets hyps target => pure (hyps, target)
    | .wildcard => do pure (← mvarId.getNondepPropHyps, true)
  let (result?, _stats) ← Lean.Meta.Grind.GrindM.run
    (grindSimpCoreM simpConfig args mvarId fvarIdsToSimp simplifyTarget baseSaturationRounds) params
  match result? with
  | none => replaceMainGoal []
  | some (_fvars, mvarId') => replaceMainGoal [mvarId']

/-- Main tactic: simp with grind as a discharger, with optional preprocessing.

    The core logic (discharge + simp) runs in `GrindM`:
    - The grind context (methods, congruence theorem cache, hash-consing state)
      is set up once and shared across all discharge calls
    - The discharge function calls back into GrindM via `controlAt MetaM`

    The preprocessing and goal management remain in `TacticM`.

    Parameters:
    - `grindConfig`, `withGroundSimprocs`, `extensions`: configure the grind discharger
    - `simpConfig`: simp configuration
    - `args`: simp lemmas / simprocs / definitions to unfold
    - `loc`: where to simplify (target, hypotheses, or everywhere)
    - `preprocessSimpArgs`: if provided, duplicate assumptions and run simp + simp_all
      with these args before the main simp+grind pass
-/
def grindSimpTac
    (grindConfig : Lean.Grind.Config)
    (withGroundSimprocs : Bool)
    (extensions : Lean.Meta.Grind.ExtensionStateArray)
    (simpConfig : Simp.Config)
    (args : GrindSimpArgs)
    (loc : Utils.Location)
    (preprocessSimpArgs : Option Simp.SimpArgs := none)
    (baseSaturationRounds : Nat := 1) : TacticM Unit := do
  Elab.Tactic.focus do
  withMainContext do
  -- Build grind parameters
  let params ← Aeneas.Grind.mkParams grindConfig extensions withGroundSimprocs
  -- Optionally preprocess: duplicate assumptions, simplify them, then clear after
  match preprocessSimpArgs with
  | none => runGrindSimpAt params simpConfig args loc baseSaturationRounds
  | some ppArgs => do
    -- Step 1: duplicate all prop assumptions
    let (_oldFvars, newFvars) ← Utils.duplicateAssumptions
    withMainContext do
    -- Step 2: simplify the duplicated assumptions (no discharger)
    let ppConfig : Simp.Config := { failIfUnchanged := false, maxDischargeDepth := 0 }
    let newFvars ← do
      match ← Simp.simpAt true ppConfig ppArgs (.targets newFvars false) with
      | none => return -- goal proved during preprocessing
      | some fvars => pure fvars
    withMainContext do
    -- Save user names of let-decl FVarIds and duplicate FVarIds before simp_all
    let letNames ← args.letDeclsToUnfold.mapM (·.getUserName)
    let newFvarNames ← newFvars.mapM (·.getUserName)
    -- Step 3: simp_all to cross-simplify hypotheses with each other
    let ppAllConfig : Simp.Config := { failIfUnchanged := false, maxDischargeDepth := 0 }
    Simp.simpAll ppAllConfig true ppArgs
    if (← getUnsolvedGoals) == [] then return
    withMainContext do
    -- Re-resolve FVarIds after simp_all (it may have replaced them)
    let resolveNames (names : Array Name) : TacticM (Array FVarId) :=
      names.filterMapM fun name => do
        match (← getLCtx).findFromUserName? name with
        | some decl => pure (some decl.fvarId)
        | none => pure none
    let letDeclsToUnfold ← resolveNames letNames
    let newFvars ← resolveNames newFvarNames
    -- After simp_all, use all current prop hypotheses (equivalent to [*])
    -- since the original FVarIds are stale and the cross-simplified context
    -- may have new useful facts
    let hypsToUse ← do
      let decls ← (← getLCtx).getDecls
      let hyps ← decls.filterMapM fun d => do
        if ← isProp d.type then pure (some d.fvarId) else pure none
      pure hyps.toArray
    let args := { args with hypsToUse, letDeclsToUnfold }
    -- Step 4: run the main simp with grind discharger
    runGrindSimpAt params simpConfig args loc baseSaturationRounds
    -- Step 5: clear the duplicated assumptions
    if (← getUnsolvedGoals) != [] then
      setGoals [← (← getMainGoal).tryClearMany newFvars]

end Aeneas.GrindSimpTac
