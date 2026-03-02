import Aeneas.GrindSimpTac.MonoGrindState
import Aeneas.Grind.Init
import Aeneas.ScalarTac.CondSimpTac -- TODO: simplify this import

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
  let config := { (← Lean.Meta.Grind.getConfig) with revert := false }
  Lean.Meta.Grind.withProtectedMCtx config mvarId fun mvarId' =>
    Lean.Meta.Grind.withGTransparency do
      -- Internalize fresh local declarations (from contextual simp)
      let state ← baseState.addFreshLocalDecls mvarId' preprocessCtx preprocessSimprocs
      -- Solve
      let goal : Lean.Meta.Grind.Goal := { toGoalState := state.goal.toGoalState, mvarId := mvarId' }
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
  controlAt MetaM fun runInMetaM => do
    mvarId.withContext do
    let discharge : Simp.Discharge := fun e => do
      let mvar ← mkFreshExprSyntheticOpaqueMVar e `grind.discharger
      try
        let ok ← runInMetaM (grindDischargeWithBase monoState preprocessCtx ppSimprocs mvar.mvarId! useMinimalSolver)
        if !ok then return none
        let proof ← instantiateMVars mvar
        if proof.hasExprMVar then return none
        return some proof
      catch _ =>
        return none
    withTraceNode `GrindSimpTac (fun _ => pure m!"simpGoal (with grind discharge)") do
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
  /- Preprocess hypsToUse -/
  let mvarId ← getMainGoal
  let (mvarId, args, newHypIds) ←
    preprocessHypsToUse mvarId args preprocessHypsToUseSimpThms preprocessHypsToUseSimprocs
  setGoals [mvarId]
  /- Initialize the simp context and elaborate the syntax (we have to do this here
    because `elabSimpArgs` lives in `TacticM`, not `MetaM`) -/
  let (ctx, simprocs) ← Simp.mkSimpCtx true simpConfig .simp args.toSimpArgs
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
  -- Replace the goal and clear the duplicated `hypsToUse`
  let fvars ←
    match result? with
    | none => replaceMainGoal []; pure none
    | some (fvars, mvarId) =>
      let mvarId ← mvarId.tryClearMany newHypIds
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
  let grindConfig : Lean.Grind.Config := {
    splits := 4, ematch := 1, splitMatch := false, splitIte := false,
    splitIndPred := false, funext := false, gen := 2, instances := 1000,
    canonHeartbeats := 1000
  }
  let extensions := #[Grind.agrindExt.getState (← getEnv)]
  let _ ←
    grindSimpTac grindConfig (withGroundSimprocs := true) extensions
      { maxDischargeDepth := 2, failIfUnchanged := false, contextual := true }
      simpArgs loc
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

syntax "test_elab" simpArgs : tactic

elab_rules : tactic
  | `(tactic| test_elab $simpArgs) => do
    let (ctx, simprocs) ← Simp.mkSimpCtx true {} .simp {}
    let stx ← Lean.Elab.Tactic.elabSimpArgs simpArgs.raw.getArgs[0]! ctx simprocs (eraseLocal := true) .simp
    println! "{stx.simpArgs.map Prod.fst}"
    pure ()

example : True := by
  test_elab [Nat, Int]
  sorry

example : True := by
  test_elab [*]
  sorry


end Aeneas.GrindSimpTac
