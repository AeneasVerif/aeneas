import Aeneas.GrindSimpTac.Init
import Aeneas.GrindSimpTac.MonoGrindState
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

**Preprocessing — incremental hypothesis simplification:**
When `preprocessSimpArgs` is provided, hypotheses are simplified incrementally
as part of the canonicalization in `buildBaseGoalState`. For each hypothesis
(from oldest to newest), we simplify it using the preprocessing simpset plus
any safe equalities (`a = b` where `a ∉ b`) from earlier hypotheses.
The `SimpTheorems` discrimination tree is built incrementally (not rebuilt
from scratch for each hypothesis). This replaces the previous `simp_all`-based
preprocessing which was expensive.

When `preprocessSimpArgs` is `none`, this is just:
  `simp (discharger := grind [grindset]) [simpset] at loc`
-/

namespace Aeneas.GrindSimpTac

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Utils

initialize registerTraceClass `GrindSimpTac

/-- Preprocess the goal target with the preprocessing simpset + safe equalities.
    The `safeThms` are reused from `MonoGrindState.localSimps` to avoid recomputation.
    This is done as a separate light simp call (no discharger) so the main simp
    pass's simpset stays lean. -/
private def preprocessTarget (mvarId : MVarId) (safeThms : SimpTheorems)
    (ppSimpThms : Array SimpTheorems) (ppSimprocs : Simp.SimprocsArray) :
    Lean.Meta.Grind.GrindM MVarId := do
  withTraceNode `GrindSimpTac (fun _ => pure m!"preprocessTarget") do
  mvarId.withContext do
  let ppConfig : Simp.Config := { failIfUnchanged := false, maxDischargeDepth := 0 }
  let congrTheorems ← getSimpCongrTheorems
  let ctx ← Simp.mkContext ppConfig (simpTheorems := #[safeThms] ++ ppSimpThms) congrTheorems
  let (result?, _stats) ← Lean.Meta.simpTarget mvarId ctx ppSimprocs
  match result? with
  | none => return mvarId  -- goal closed or unchanged
  | some mvarId' => return mvarId'

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

/-- Discharge using a pre-built base GoalState.
    The base state has all hypotheses already canonicalized and internalized in
    the e-graph. For each discharge call, we construct a Goal from this base
    state + the discharge mvar, so only the target needs canonicalization.

    When `useMinimalSolver` is true, uses `solveMinimal` (only linarith + lia,
    no case splits, no tactic checking) instead of the full `solve`. -/
private def grindDischargeWithBase (baseState : Lean.Meta.Grind.GoalState)
    (mvarId : MVarId) (useMinimalSolver : Bool) : Lean.Meta.Grind.GrindM Bool := do
  withTraceNode `GrindSimpTac (fun _ => pure m!"grindDischargeWithBase") do
  let config := { (← Lean.Meta.Grind.getConfig) with revert := false }
  Lean.Meta.Grind.withProtectedMCtx config mvarId fun mvarId' =>
    Lean.Meta.Grind.withGTransparency do
      let goal : Lean.Meta.Grind.Goal := { toGoalState := baseState, mvarId := mvarId' }
      let failure? ←
        if useMinimalSolver then solveMinimal goal
        else Lean.Meta.Grind.solve goal
      return failure?.isNone

/-- Core simp+grind logic in GrindM.
    Runs `simp` on the given goal with grind as the discharger.

    Uses `MonoGrindState` to unify hypothesis preprocessing and grind state
    building into a single pass. Each hypothesis is simplified (if `preprocess`),
    then added to the grind e-graph. After all hypotheses are processed,
    e-matching saturation and arithmetic pre-derivation run once.

    When `preprocess` is true, the target is also preprocessed with the safe
    equalities, and safe equalities are excluded from `fvarIdsToSimp` to avoid
    self-application. -/
private def grindSimpCoreM (simpConfig : Simp.Config) (args : GrindSimpArgs)
    (mvarId : MVarId) (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool)
    (baseSaturationRounds : Nat)
    (ppSimpThms : Array SimpTheorems) (ppSimprocs : Simp.SimprocsArray)
    (preprocess : Bool) (useMinimalSolver : Bool) :
    Lean.Meta.Grind.GrindM (Option (Array FVarId × MVarId) × Simp.Stats) := do
  withTraceNode `GrindSimpTac (fun _ => pure m!"grindSimpCoreM") do
  -- Optionally preprocess hypotheses and target on the main goal first
  let (mvarId, fvarIdsToSimp, args) ←
    if !preprocess then pure (mvarId, fvarIdsToSimp, args)
    else do
      -- Simplify main goal hypotheses using safe equalities + preprocessing simpset
      let (mvarId, localSimps) ← simplifyHypsWithSafeEqs mvarId ppSimpThms ppSimprocs
      -- Simplify the target
      let mvarId ← preprocessTarget mvarId localSimps ppSimpThms ppSimprocs
      -- Re-collect hypotheses: safe equalities go into hypsToUse but are
      -- excluded from fvarIdsToSimp to avoid self-application
      let (hypsToUse, fvarIdsToSimp) ← mvarId.withContext do
        let lctx ← getLCtx
        let mut hypsToUse : Array FVarId := #[]
        let mut fvarIdsToSimp : Array FVarId := #[]
        for decl in lctx do
          if decl.isImplementationDetail then continue
          if !(← isProp decl.type) then continue
          hypsToUse := hypsToUse.push decl.fvarId
          let type ← instantiateMVars decl.type
          if !isSafeEquality type then
            fvarIdsToSimp := fvarIdsToSimp.push decl.fvarId
        pure (hypsToUse, fvarIdsToSimp)
      pure (mvarId, fvarIdsToSimp, { args with hypsToUse })
  -- Build MonoGrindState from (possibly preprocessed) main goal
  let monoState ← MonoGrindState.initializeFromMVar mvarId ppSimpThms ppSimprocs
  let monoState ← monoState.deriveFacts baseSaturationRounds
  -- Use the pre-built GoalState for discharge
  let baseGoalState := monoState.goal.toGoalState
  controlAt MetaM fun runInMetaM => do
    mvarId.withContext do
    let discharge : Simp.Discharge := fun e => do
      let mvar ← mkFreshExprSyntheticOpaqueMVar e `grind.discharger
      try
        let ok ← runInMetaM (grindDischargeWithBase baseGoalState mvar.mvarId! useMinimalSolver)
        if !ok then return none
        let proof ← instantiateMVars mvar
        if proof.hasExprMVar then return none
        return some proof
      catch _ =>
        return none
    let simpArgs := args.toSimpArgs
    let (ctx, simprocs) ← Simp.mkSimpCtx true simpConfig .simp simpArgs
    withTraceNode `GrindSimpTac (fun _ => pure m!"simpGoal (with grind discharge)") do
      Lean.Meta.simpGoal mvarId ctx (simprocs := simprocs) (simplifyTarget := simplifyTarget)
        (discharge? := some discharge) (fvarIdsToSimp := fvarIdsToSimp)

/-- Run the GrindM simp core at a given location, translating the result back to TacticM. -/
private def runGrindSimpAt (params : Lean.Meta.Grind.Params)
    (simpConfig : Simp.Config) (args : GrindSimpArgs)
    (loc : Utils.Location) (baseSaturationRounds : Nat)
    (ppSimpThms : Array SimpTheorems) (ppSimprocs : Simp.SimprocsArray)
    (preprocess : Bool) (useMinimalSolver : Bool) : TacticM Unit := do
  withMainContext do
  let mvarId ← getMainGoal
  let (fvarIdsToSimp, simplifyTarget) ← match loc with
    | .targets hyps target => pure (hyps, target)
    | .wildcard => do pure (← mvarId.getNondepPropHyps, true)
  let (result?, _stats) ← Lean.Meta.Grind.GrindM.run
    (grindSimpCoreM simpConfig args mvarId fvarIdsToSimp simplifyTarget baseSaturationRounds
      ppSimpThms ppSimprocs preprocess useMinimalSolver) params
  match result? with
  | none => replaceMainGoal []
  | some (_fvars, mvarId') => replaceMainGoal [mvarId']

/-- Main tactic: simp with grind as a discharger, with optional preprocessing.

    The core logic (discharge + simp) runs in `GrindM`:
    - The grind context (methods, congruence theorem cache, hash-consing state)
      is set up once and shared across all discharge calls
    - The discharge function calls back into GrindM via `controlAt MetaM`

    Parameters:
    - `grindConfig`, `withGroundSimprocs`, `extensions`: configure the grind discharger
    - `simpConfig`: simp configuration
    - `args`: simp lemmas / simprocs / definitions to unfold
    - `loc`: where to simplify (target, hypotheses, or everywhere)
    - `preprocessSimpArgs`: if provided, hypotheses are incrementally simplified
      (replacing the old simp_all approach). Safe equalities are used to cross-simplify.
    - `baseSaturationRounds`: number of e-matching rounds on the base GoalState (default 1)
    - `useMinimalSolver`: use minimal solver (linarith + lia only) instead of full grind solve (default false)
-/
def grindSimpTac
    (grindConfig : Lean.Grind.Config)
    (withGroundSimprocs : Bool)
    (extensions : Lean.Meta.Grind.ExtensionStateArray)
    (simpConfig : Simp.Config)
    (args : GrindSimpArgs)
    (loc : Utils.Location)
    (preprocessSimpArgs : Option Simp.SimpArgs := none)
    (baseSaturationRounds : Nat := 1)
    (useMinimalSolver : Bool := false) : TacticM Unit := do
  Elab.Tactic.focus do
  withTraceNode `GrindSimpTac (fun _ => pure m!"grindSimpTac") do
  withMainContext do
  -- Build grind parameters
  let params ← Aeneas.Grind.mkParams grindConfig extensions withGroundSimprocs
  -- Extract preprocessing simp theorems/simprocs (empty if no preprocessing)
  match preprocessSimpArgs with
  | none =>
    runGrindSimpAt params simpConfig args loc baseSaturationRounds #[] #[]
      (preprocess := false) (useMinimalSolver := useMinimalSolver)
  | some ppArgs =>
    runGrindSimpAt params simpConfig args loc baseSaturationRounds ppArgs.simpThms ppArgs.simprocs
      (preprocess := true) (useMinimalSolver := useMinimalSolver)

end Aeneas.GrindSimpTac
