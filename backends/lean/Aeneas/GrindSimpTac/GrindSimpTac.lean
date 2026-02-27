import Aeneas.GrindSimpTac.Init
import Aeneas.Grind.Init

/-!
# `grindSimpTac`: simp with grind as a discharger

The core logic (discharge + simp) lives in `GrindM` for efficiency: the grind
context (methods, congruence theorem cache, hash-consing state) is set up once
and shared across all discharge calls from simp.

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

/-- Initialize a grind goal from an MVarId.
    Replicates the logic of the private `Lean.Meta.Grind.initCore`. -/
private def initGrindGoal (mvarId : MVarId) : Lean.Meta.Grind.GrindM Lean.Meta.Grind.Goal := do
  let config ← Lean.Meta.Grind.getConfig
  let mvarId ← if config.clean || !config.revert then pure mvarId else mvarId.markAccessible
  let mvarId ← if config.revert then mvarId.revertAll else pure mvarId
  let mvarId ← mvarId.unfoldReducible
  let mvarId ← mvarId.betaReduce
  appendTagSuffix mvarId `grind
  let goal ← Lean.Meta.Grind.mkGoalCore mvarId
  if config.revert then
    return goal
  else
    Lean.Meta.Grind.processHypotheses goal

/-- Core discharge function in GrindM.
    Tries to prove the goal at `mvarId` using grind within the current
    GrindM context (sharing congruence theorem cache, hash-consing state, etc.). -/
private def grindDischarge (mvarId : MVarId) : Lean.Meta.Grind.GrindM Bool := do
  let config ← Lean.Meta.Grind.getConfig
  Lean.Meta.Grind.withProtectedMCtx config mvarId fun mvarId' =>
    Lean.Meta.Grind.withGTransparency do
      let goal ← initGrindGoal mvarId'
      let failure? ← Lean.Meta.Grind.solve goal
      return failure?.isNone

/-- Core simp+grind logic in GrindM.
    Runs `simp` on the given goal with grind as the discharger.
    Uses `controlAt MetaM` to bridge: the discharge closure (called from SimpM)
    calls back into the current GrindM context via the captured runner. -/
private def grindSimpCoreM (simpConfig : Simp.Config) (args : GrindSimpArgs)
    (mvarId : MVarId) (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) :
    Lean.Meta.Grind.GrindM (Option (Array FVarId × MVarId) × Simp.Stats) :=
  controlAt MetaM fun runInMetaM => do
    mvarId.withContext do
    let discharge : Simp.Discharge := fun e => do
      let mvar ← mkFreshExprSyntheticOpaqueMVar e `grind.discharger
      try
        let ok ← runInMetaM (grindDischarge mvar.mvarId!)
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
    (loc : Utils.Location) : TacticM Unit := do
  withMainContext do
  let mvarId ← getMainGoal
  let (fvarIdsToSimp, simplifyTarget) ← match loc with
    | .targets hyps target => pure (hyps, target)
    | .wildcard => do pure (← mvarId.getNondepPropHyps, true)
  let (result?, _stats) ← Lean.Meta.Grind.GrindM.run
    (grindSimpCoreM simpConfig args mvarId fvarIdsToSimp simplifyTarget) params
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
    (preprocessSimpArgs : Option Simp.SimpArgs := none) : TacticM Unit := do
  Elab.Tactic.focus do
  withMainContext do
  -- Build grind parameters
  let params ← Aeneas.Grind.mkParams grindConfig extensions withGroundSimprocs
  -- Optionally preprocess: duplicate assumptions, simplify them, then clear after
  match preprocessSimpArgs with
  | none => runGrindSimpAt params simpConfig args loc
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
    runGrindSimpAt params simpConfig args loc
    -- Step 5: clear the duplicated assumptions
    if (← getUnsolvedGoals) != [] then
      setGoals [← (← getMainGoal).tryClearMany newFvars]

end Aeneas.GrindSimpTac
