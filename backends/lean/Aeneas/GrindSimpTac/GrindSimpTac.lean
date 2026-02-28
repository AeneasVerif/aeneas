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

/-- Check if a type is a "safe" equality usable as a simp rewrite rule.
    Returns true iff the type is exactly `@Eq α lhs rhs` where `lhs` does not
    appear as a subexpression of `rhs` (to avoid rewriting loops). -/
private def isSafeEquality (type : Expr) : Bool :=
  if let some (_, lhs, rhs) := type.eq? then
    !(rhs.find? (· == lhs)).isSome
  else
    false

/-- Incrementally simplify hypotheses of an mvar.
    Pre-scans all hypotheses to collect initial safe equalities, then does
    a forward pass simplifying each hypothesis with the full set.

    For each hypothesis `hi` (from oldest to newest):
    1. Simplify using current simp context (base simpset + all safe equalities
       except `hi` itself)
    2. If `hi` changed (new FVarId), update the SimpTheorems entry

    Pre-scanning ensures safe equalities from later hypotheses are available
    for earlier ones (e.g., `hi : ↑i = 2 * i0` simplifies `hc1` even though
    `hc1` was declared before `hi`). -/
private def simplifyHypsIncremental (mvarId : MVarId) (ppSimpThms : Array SimpTheorems)
    (ppSimprocs : Simp.SimprocsArray) : MetaM MVarId := do
  mvarId.withContext do
  -- Collect prop hypothesis FVarIds in declaration order (oldest first)
  let lctx := (← mvarId.getDecl).lctx
  let propHyps ← lctx.foldlM (init := #[]) fun acc decl => do
    if !decl.isImplementationDetail then
      if ← isProp decl.type then
        return acc.push decl.fvarId
    return acc
  -- Pre-scan: collect initial safe equalities from all hypotheses into entry 0.
  let mut initialSimpThms : SimpTheorems := {}
  for fvarId in propHyps do
    let type ← instantiateMVars (← fvarId.getType)
    if isSafeEquality type then
      initialSimpThms ← initialSimpThms.add (.fvar fvarId) #[] (mkFVar fvarId)
  -- Build the initial simp context: [initialSimpThms] ++ ppSimpThms
  let ppConfig : Simp.Config := { failIfUnchanged := false, maxDischargeDepth := 0 }
  let congrTheorems ← getSimpCongrTheorems
  let mut ctx ← Simp.mkContext ppConfig (simpTheorems := #[initialSimpThms] ++ ppSimpThms) congrTheorems
  let mut mvarId := mvarId
  for fvarId in propHyps do
    let ok ← mvarId.withContext do
      let lctx ← getLCtx
      unless lctx.contains fvarId do return (true, ctx, mvarId)
      -- Erase the hypothesis itself from simp theorems to avoid self-loops
      let localCtx := ctx.setSimpTheorems (ctx.simpTheorems.eraseTheorem (.fvar fvarId))
      let (result?, _stats) ← Lean.Meta.simpLocalDecl mvarId fvarId localCtx ppSimprocs
        (mayCloseGoal := false)
      match result? with
      | none =>
        return (false, ctx, mvarId)
      | some (newFvarId, newMvarId) =>
        if newFvarId != fvarId then
          -- FVarId changed: the old origin (.fvar fvarId) is in the erased set,
          -- but the new origin (.fvar newFvarId) is NOT, so addTheorem works.
          let ctx ← newMvarId.withContext do
            let type ← instantiateMVars (← newFvarId.getType)
            let simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar fvarId)
            if isSafeEquality type then
              let simpTheorems ← simpTheorems.addTheorem (.fvar newFvarId) (mkFVar newFvarId)
                (config := ctx.indexConfig)
              return ctx.setSimpTheorems simpTheorems
            else
              return ctx.setSimpTheorems simpTheorems
          return (true, ctx, newMvarId)
        else
          -- FVarId unchanged: keep existing SimpTheorems entry from pre-scan (no erase needed)
          return (true, ctx, mvarId)
    let (continue_, ctx', mvarId') := ok
    ctx := ctx'
    mvarId := mvarId'
    if !continue_ then break
  return mvarId

/-- Preprocess the goal target with the preprocessing simpset + safe equalities
    from the context. This is done as a separate light simp call (no discharger)
    so the main simp pass's simpset stays lean. -/
private def preprocessTarget (mvarId : MVarId) (ppSimpThms : Array SimpTheorems)
    (ppSimprocs : Simp.SimprocsArray) : MetaM MVarId := do
  mvarId.withContext do
  -- Collect safe equalities from the context
  let lctx := (← mvarId.getDecl).lctx
  let mut safeThms : SimpTheorems := {}
  for decl in lctx do
    if decl.isImplementationDetail then continue
    if !(← isProp decl.type) then continue
    let type ← instantiateMVars decl.type
    if isSafeEquality type then
      safeThms ← safeThms.add (.fvar decl.fvarId) #[] (mkFVar decl.fvarId)
  let ppConfig : Simp.Config := { failIfUnchanged := false, maxDischargeDepth := 0 }
  let congrTheorems ← getSimpCongrTheorems
  let ctx ← Simp.mkContext ppConfig (simpTheorems := #[safeThms] ++ ppSimpThms) congrTheorems
  let (result?, _stats) ← Lean.Meta.simpTarget mvarId ctx ppSimprocs
  match result? with
  | none => return mvarId  -- goal closed or unchanged
  | some mvarId' => return mvarId'

/-- Build a base GoalState with all hypotheses canonicalized and internalized
    in the e-graph. This is called once before `simp`, so each discharge call
    can reuse the pre-built e-graph instead of re-canonicalizing all hypotheses.

    We use `revert := false` (regardless of the grind config) so hypotheses
    stay in the local context and are processed by `processHypotheses`.

    When `ppSimpThms`/`ppSimprocs` are provided, hypotheses are incrementally
    simplified before internalization (replacing the previous `simp_all` approach).

    When `saturationRounds > 0`, we also run e-matching on the base e-graph
    to pre-saturate it with derived facts. -/
private def buildBaseGoalState (mvarId : MVarId) (saturationRounds : Nat := 1)
    (ppSimpThms : Array SimpTheorems := #[]) (ppSimprocs : Simp.SimprocsArray := #[]) :
    Lean.Meta.Grind.GrindM Lean.Meta.Grind.GoalState := do
  mvarId.withContext do
  -- Create a temporary mvar (same lctx, dummy target) to avoid modifying the main goal
  let tmpMvar ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True) `grind_base
  let tmpMvarId := tmpMvar.mvarId!
  -- Incrementally simplify hypotheses before canonicalization
  let tmpMvarId ←
    if ppSimpThms.isEmpty then pure tmpMvarId
    else simplifyHypsIncremental tmpMvarId ppSimpThms ppSimprocs
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
    (baseSaturationRounds : Nat)
    (ppSimpThms : Array SimpTheorems) (ppSimprocs : Simp.SimprocsArray) :
    Lean.Meta.Grind.GrindM (Option (Array FVarId × MVarId) × Simp.Stats) := do
  -- Pre-build base GoalState with all hypotheses canonicalized and in the e-graph
  let baseGoalState ← buildBaseGoalState mvarId baseSaturationRounds ppSimpThms ppSimprocs
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
    (loc : Utils.Location) (baseSaturationRounds : Nat)
    (ppSimpThms : Array SimpTheorems) (ppSimprocs : Simp.SimprocsArray) : TacticM Unit := do
  withMainContext do
  let mvarId ← getMainGoal
  let (fvarIdsToSimp, simplifyTarget) ← match loc with
    | .targets hyps target => pure (hyps, target)
    | .wildcard => do pure (← mvarId.getNondepPropHyps, true)
  let (result?, _stats) ← Lean.Meta.Grind.GrindM.run
    (grindSimpCoreM simpConfig args mvarId fvarIdsToSimp simplifyTarget baseSaturationRounds
      ppSimpThms ppSimprocs) params
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
  -- Extract preprocessing simp theorems/simprocs (empty if no preprocessing)
  let (ppSimpThms, ppSimprocs) ← match preprocessSimpArgs with
    | none => pure (#[], #[])
    | some ppArgs => pure (ppArgs.simpThms, ppArgs.simprocs)
  match preprocessSimpArgs with
  | none =>
    runGrindSimpAt params simpConfig args loc baseSaturationRounds ppSimpThms ppSimprocs
  | some _ppArgs => do
    -- Preprocessing: incrementally simplify all prop hypotheses
    -- using safe equalities from earlier hypotheses + the preprocessing simpset.
    -- This replaces the previous simp + simp_all approach.
    let mvarId ← getMainGoal
    let mvarId ← simplifyHypsIncremental mvarId ppSimpThms ppSimprocs
    -- Also preprocess the TARGET with ppSimpThms + safe equalities (the incremental
    -- simp only processes hypotheses). We do this as a separate light simp call
    -- to avoid bloating the main simp pass's simpset.
    let mvarId ← preprocessTarget mvarId ppSimpThms ppSimprocs
    replaceMainGoal [mvarId]
    withMainContext do
    -- After incremental simp, collect all prop hypotheses.
    -- Safe equalities go into `hypsToUse` (as rewrite rules in the simpset)
    -- but are EXCLUDED from `fvarIdsToSimp` to avoid self-application
    -- (e.g., `hi : ↑i = 2 * i0` would rewrite itself to `True`).
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
    let args := { args with hypsToUse }
    -- Use explicit targets to control which hypotheses are simplified
    let loc := Utils.Location.targets fvarIdsToSimp true
    -- Run the main simp with grind discharger
    runGrindSimpAt params simpConfig args loc baseSaturationRounds ppSimpThms ppSimprocs

end Aeneas.GrindSimpTac
