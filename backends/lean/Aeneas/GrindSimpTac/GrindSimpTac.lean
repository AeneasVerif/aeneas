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
private def grindSimpCoreM (simpConfig : Simp.Config) (args : GrindSimpArgs)
    (mvarId : MVarId) (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool)
    (baseSaturationRounds : Nat)
    (ppSimpThms : Array SimpTheorems) (ppSimprocs : Simp.SimprocsArray)
    (ppHypsToUseSimpThms : Array SimpTheorems) (ppHypsToUseSimprocs : Simp.SimprocsArray)
    (useMinimalSolver : Bool) :
    Lean.Meta.Grind.GrindM (Option (Array FVarId × MVarId) × Simp.Stats) := do
  withTraceNode `GrindSimpTac (fun _ => pure m!"grindSimpCoreM") do
  -- Preprocess hypsToUse
  let (mvarId, args, newHypIds) ←
    preprocessHypsToUse mvarId args ppHypsToUseSimpThms ppHypsToUseSimprocs
  -- Build MonoGrindState from the main goal
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
    let result ← withTraceNode `GrindSimpTac (fun _ => pure m!"simpGoal (with grind discharge)") do
      Lean.Meta.simpGoal mvarId ctx (simprocs := simprocs) (simplifyTarget := simplifyTarget)
        (discharge? := some discharge) (fvarIdsToSimp := fvarIdsToSimp)
    -- Clear the preprocessed hypsToUse copies from the context
    let result ← match result with
    | (some (fvars, mvarId'), stats) =>
      if newHypIds.isEmpty then return (some (fvars, mvarId'), stats)
      let mvarId' ← mvarId'.tryClearMany newHypIds
      return (some (fvars, mvarId'), stats)
    | other => pure other
    return result

/-- Run the GrindM simp core at a given location, translating the result back to TacticM. -/
private def runGrindSimpAt (params : Lean.Meta.Grind.Params)
    (simpConfig : Simp.Config) (args : GrindSimpArgs)
    (loc : Utils.Location) (baseSaturationRounds : Nat)
    (ppSimpThms : Array SimpTheorems) (ppSimprocs : Simp.SimprocsArray)
    (ppHypsToUseSimpThms : Array SimpTheorems) (ppHypsToUseSimprocs : Simp.SimprocsArray)
    (useMinimalSolver : Bool) : TacticM Unit := do
  withMainContext do
  let mvarId ← getMainGoal
  let (fvarIdsToSimp, simplifyTarget) ← match loc with
    | .targets hyps target => pure (hyps, target)
    | .wildcard => do pure (← mvarId.getNondepPropHyps, true)
  let (result?, _stats) ← Lean.Meta.Grind.GrindM.run
    (grindSimpCoreM simpConfig args mvarId fvarIdsToSimp simplifyTarget baseSaturationRounds
      ppSimpThms ppSimprocs ppHypsToUseSimpThms ppHypsToUseSimprocs useMinimalSolver) params
  match result? with
  | none => replaceMainGoal []
  | some (_fvars, mvarId') => replaceMainGoal [mvarId']

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
      simplify duplicated `hypsToUse` before the main simp pass
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
    (preprocessSimpThms : Array SimpTheorems := #[])
    (preprocessSimprocs : Simp.SimprocsArray := #[])
    (preprocessHypsToUseSimpThms : Array SimpTheorems := #[])
    (preprocessHypsToUseSimprocs : Simp.SimprocsArray := #[])
    (baseSaturationRounds : Nat := 1)
    (useMinimalSolver : Bool := false) : TacticM Unit := do
  Elab.Tactic.focus do
  withTraceNode `GrindSimpTac (fun _ => pure m!"grindSimpTac") do
  withMainContext do
  -- Build grind parameters
  let params ← Aeneas.Grind.mkParams grindConfig extensions withGroundSimprocs
  runGrindSimpAt params simpConfig args loc baseSaturationRounds preprocessSimpThms preprocessSimprocs
    preprocessHypsToUseSimpThms preprocessHypsToUseSimprocs (useMinimalSolver := useMinimalSolver)

end Aeneas.GrindSimpTac
