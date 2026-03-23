/-
Copyright (c) 2025 Aeneas contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Son Ho
-/
import Lean
import Aeneas.Tactic.Solver.ScalarTac
import Aeneas.Tactic.Step.Init
import Aeneas.Tactic.Solver.Grind.Init

/-!
# Grind State Threading for `step` / `step*`

This module manages a grind state that is threaded through successive `step` calls
(especially in `step*`), reusing simp caches, the e-graph, and derived facts across
iterations instead of rebuilding from scratch each time.

## Key Design Decisions

- **Thread `GoalState` (not `Goal`)**: Avoids carrying an MVarId between proof states.
- **Custom internalization**: Uses Aeneas simpsets (scalar_tac_simps, etc.) for hypothesis
  simplification, followed by grind's `canon`/`shareCommon` for canonical form, then `add`.
- **Preprocessing per proposition**: After each prop hypothesis is internalized, we run
  the preprocessing loop (`assertAll >> solvers.loop`). This ensures:
  - we preprocess fact derivation
  - the fact that we run it after *each* prop hypothesis ensures the grind state at any
    point is identical whether we initialize from scratch (single `step`) or incrementally
    (threaded `step*`).
- **No GrindM.run fork**: We use `GrindM.run` as-is and use `set`/`get` inside the action
  to inject/extract the `Grind.State` and `Sym.State`.

## Discharge with `Grind.solve`

To discharge preconditions, we construct a `Goal` from the precondition `MVarId` and the
threaded GoalState, then call `Grind.solve`. Both `Grind.State` and `Sym.State` are
restored before the solve call via `set`/`get` inside `GrindM.run`.

## State Management Pattern

```
runGrindWithState params savedGrindState savedSymState do
  -- Both Grind.State and Sym.State are restored via set/get
  let goal := { toGoalState := savedGoalState, mvarId := currentMVarId }
  -- ... operations on goal ...
  -- Returns (result, finalGrindState, finalSymState)
```
-/

namespace Aeneas

namespace Step

-- Only open `Lean Meta` (not `Elab`/`Tactic`) to avoid ambiguity with `Tactic.Grind.State`
open Lean Meta
open Lean.Meta.Grind (GrindM GoalM Goal GoalState)

/-- Build `Grind.Params` from `Step.Config`, reusing the logic from `Aeneas.Grind`.
    We set `clean := false` and `revert := false` to prevent `mkGoalCore` from mutating the
    proof goal's MVarId (via `exposeNames` / `revertAll`). Our use of grind is purely for
    building a knowledge base, not for solving the goal directly. -/
private def mkGrindParams (config : Config) : MetaM Grind.Params := do
  let grindConfig := { config.toGrindConfig with clean := false, revert := false }
  Aeneas.Grind.mkParams grindConfig
    (← Aeneas.Grind.getAgrindExtensions config.nla) config.withGroundSimprocs

/-- Build the Aeneas simp context for hypothesis preprocessing.
    Uses the same simpsets as `scalar_tac` (scalar_tac_simps, simp_bool_prop_simps, etc.)
    combined with the standard Lean simp theorems. -/
private def mkAeneasSimpCtx : MetaM (Simp.Context × Simp.SimprocsArray) := do
  let simpArgs ← ScalarTac.getSimpArgs
  let defaultSimpThms ← getSimpTheorems
  let congrTheorems ← getSimpCongrTheorems
  let defaultSimprocs ← Simp.getSimprocs
  let ctx ← Simp.mkContext
    (config := { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 })
    (simpTheorems := #[defaultSimpThms] ++ simpArgs.simpThms)
    congrTheorems
  pure (ctx, #[defaultSimprocs] ++ simpArgs.simprocs)

/-- Run a `GrindM` action with injected `Grind.State` and `Sym.State`,
    returning all final states alongside the result.

    Uses `GrindM.run` as-is, and injects/extracts state via `get`/`set` inside the action.
    For fresh initialization, pass default `{}` for both states (the `set` is a no-op). -/
def runGrindWithState {α} (params : Grind.Params)
    (savedGrindState : Grind.State)
    (savedSymState : Lean.Meta.Sym.State)
    (action : GrindM α) : MetaM (α × Grind.State × Lean.Meta.Sym.State) := do
  Grind.GrindM.run (params := params) do
    set savedGrindState
    modifyThe Lean.Meta.Sym.State fun _ => savedSymState
    let result ← action
    let finalGrindState ← get
    let finalSymState ← getThe Lean.Meta.Sym.State
    pure (result, finalGrindState, finalSymState)

/-- Internalize local hypotheses into a grind goal, using Aeneas simpsets.

    **Invariant:** Preprocessing runs after each *proposition* hypothesis is internalized.
    This ensures the grind state at any point is identical whether we:
    (a) Initialize from scratch with all current hypotheses (single `step` call), or
    (b) Incrementally add hypotheses one by one (threaded `step*`)

    This invariant is critical for `step*?`: the generated proof script (individual
    `step` calls) must produce the same grind state as `step*` (threaded calls),
    so proofs work identically in both modes (otherwise the risk is that the number of unsolved
    preconditions is not the same when we call `step*` or when we expand it to the script generated
    by `step*?`).

    For each local declaration (starting from `goal.nextDeclIdx`):
    - **All declarations**: `internalizeLocalDecl` first (adds the fvar to the e-graph).
    - **Propositions** (additionally): Simplify type with Aeneas simpsets, apply grind's
      `canon`/`shareCommon`, add the simplified type as a fact, run the preprocessing loop
      (`assertAll >> solvers.loop`). -/
private def internalizeHypotheses (goal : Goal) (config : Config)
    (simpCtx : Simp.Context) (simprocs : Simp.SimprocsArray)
    : GrindM (Goal × Bool) := do
  -- Build the preprocessing action (solvers + instantiate) once
  let solvers ← Grind.Solvers.mkAction
  let preprocessAction : Grind.Action :=
    Grind.Action.assertAll >> (solvers <|> Grind.Action.instantiate).loop config.grindPreprocessIters
  -- GoalM.run' runs inside goal.mvarId.withContext and returns the final Goal
  let (contradiction, goal) ← GoalM.run goal do
    let mut contradiction := false
    let mvarDecl ← goal.mvarId.getDecl
    let decls := mvarDecl.lctx.decls.toList.drop goal.nextDeclIdx
    for localDecl? in decls do
      let some localDecl := localDecl? | continue
      if localDecl.isImplementationDetail then continue
      -- Internalize the fvar itself (for dependent type references in the e-graph)
      Grind.internalizeLocalDecl localDecl
      let type := localDecl.type
      if (← isProp type) then
        -- Prop hypothesis: simplify with Aeneas simpsets, then use grind's preprocessHypothesis
        let (simplifiedType, simpProof?) ← do
          let (simpResult, _) ← Lean.Meta.simp type simpCtx simprocs
          let simplifiedType ← instantiateMVars simpResult.expr
          pure (simplifiedType, simpResult.proof?)
        -- Use grind's preprocessHypothesis for normalization
        let r ← Grind.preprocessHypothesis simplifiedType
        -- Build proof chain: fvar → (optional Eq.mp for simp) → (optional Eq.mp for preprocess)
        let basePrf : Expr :=
          if let some simpH := simpProof? then
            mkApp4 (mkConst ``Eq.mp [0]) type simplifiedType simpH localDecl.toExpr
          else
            localDecl.toExpr
        if let some ppH := r.proof? then
          Grind.add r.expr
            (mkApp4 (mkConst ``Eq.mp [0]) simplifiedType r.expr ppH basePrf)
        else
          Grind.add r.expr basePrf
        -- Optionally run preprocessing after THIS hypothesis
        if config.preprocessGrind then
          let goal ← get
          match ← preprocessAction.run goal with
          | .closed _ =>
            contradiction := true
            break
          | .stuck gs =>
            match gs with
            | goal :: _ => set goal
            | [] => pure ()
    Grind.setNextDeclToEnd
    pure contradiction
  return (goal, contradiction)

/-- Initialize the grind state from the current proof context.
    Creates a fresh `GoalState` and internalizes all current local hypotheses. -/
def initStepGrindState (config : Config) (mvarId : MVarId) : MetaM StepGrindState := do
  let params ← mkGrindParams config
  let (simpCtx, simprocs) ← mkAeneasSimpCtx
  let ((goalState, contradiction), grindState, symState) ← runGrindWithState params {} {} do
    -- Create a fresh Goal for the current MVarId
    let goal ← Grind.mkGoalCore mvarId
    -- Internalize all current hypotheses
    let (goal, contradiction) ← internalizeHypotheses goal config simpCtx simprocs
    pure (goal.toGoalState, contradiction)
  pure { grindState, symState, goalState, contradiction, params, simpCtx, simprocs }

/-- Update the grind state after new fvars have been introduced (by `introOutputs` or
    case splits). Only processes fvars with index ≥ `nextDeclIdx` (incremental). -/
def updateStepGrindState (state : StepGrindState) (config : Config) (mvarId : MVarId)
    : MetaM StepGrindState := do
  let ((goalState, contradiction), grindState, symState) ←
    runGrindWithState state.params state.grindState state.symState do
      -- Reconstruct Goal from saved GoalState + current MVarId
      let goal : Goal := { toGoalState := state.goalState, mvarId }
      -- Process only NEW fvars (via nextDeclIdx)
      let (goal, contradiction) ← internalizeHypotheses goal config state.simpCtx state.simprocs
      pure (goal.toGoalState, contradiction)
  pure { state with grindState, symState, goalState, contradiction := state.contradiction || contradiction }

/-- Discharge a precondition using `Grind.solve` with the threaded grind state.

    The threaded state (e-graph, satellite solvers, Sym.State) contains all accumulated
    knowledge from prior `step` calls. `Grind.solve` adds the negation of the target
    to the e-graph and runs the full solver pipeline (assertAll, satellite solvers,
    e-matching, case splitting) to find a contradiction.

    Returns `true` if the precondition was solved, `false` otherwise.
    On failure, all MetaM state changes are reverted (via `observing?`). -/
def dischargeWithGrindState (state : StepGrindState) (precondMVarId : MVarId)
    : MetaM Bool := do
  let result ← observing? do
    let mvarDecl ← precondMVarId.getDecl
    let goalState : GoalState :=
      { state.goalState with
        nextDeclIdx := mvarDecl.lctx.decls.size }
    let (solved, _, _) ←
      runGrindWithState state.params state.grindState state.symState do
        let goal : Goal := { toGoalState := goalState, mvarId := precondMVarId }
        match ← Grind.solve goal with
        | none   => pure true
        | some _ => pure false
    unless solved do throwError "grind could not solve precondition"
  return result.isSome

end Step

end Aeneas
