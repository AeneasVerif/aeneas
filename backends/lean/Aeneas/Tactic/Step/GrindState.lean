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
- **No GrindM.run fork**: We replicate the `GrindM.run` monad stack construction once
  (`runGrindFresh`), save all contexts (`Sym.Context`, `Grind.Context`, `MethodsRef`),
  and reuse them in subsequent calls (`runGrindWithState`) to preserve pointer identity.

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
/- Build a simp context for preprocessing hypotheses before internalization.
   Uses the SAME simpset as `ScalarTac.getSimpArgs` (scalar_tac_simps + simpBoolProp)
   so that internalized hypotheses are normalized identically to how `threadedGrindTac`
   and `evalAGrindWithPreprocess` normalize them before calling grind. Using a different
   simpset (e.g., the full `@[simp]` set) would cause form mismatches in the e-graph. -/
private def mkPreprocessSimpCtx : MetaM (Simp.Context × Simp.SimprocsArray) := do
  let simpArgs ← ScalarTac.getSimpArgs
  let congrTheorems ← getSimpCongrTheorems
  let ctx ← Simp.mkContext
    (config := { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 })
    (simpTheorems := simpArgs.simpThms)
    congrTheorems
  pure (ctx, simpArgs.simprocs)

/-- Run a `GrindM` action with a fresh monad stack (via `GrindM.run`).
    Used for initialization — reads out all contexts and states for subsequent reuse. -/
def runGrindFresh {α} (params : Grind.Params)
    (action : GrindM α) : MetaM (α × Grind.State × Lean.Meta.Sym.State × Lean.Meta.Sym.Context × Grind.Context × Grind.MethodsRef) :=
  Grind.GrindM.run (params := params) do
    let result ← action
    let grindState ← get
    let symState ← getThe Lean.Meta.Sym.State
    let symCtx ← readThe Lean.Meta.Sym.Context
    let grindCtx ← readThe Grind.Context
    let methodsRef ← readThe Grind.MethodsRef
    pure (result, grindState, symState, symCtx, grindCtx, methodsRef)

/-- Run a `GrindM` action reusing saved contexts and states from a previous run.
    Preserves pointer identity of all contexts (`Sym.Context`, `Grind.Context`,
    `MethodsRef`) to avoid PANICs in the e-graph's proof reconstruction. -/
def runGrindWithState {α} (state : StepGrindState) (action : GrindM α)
    : MetaM (α × Grind.State × Lean.Meta.Sym.State) := do
  let wrappedAction : GrindM (α × Grind.State × Lean.Meta.Sym.State) := do
    let result ← action
    let finalGrindState ← get
    let finalSymState ← getThe Lean.Meta.Sym.State
    pure (result, finalGrindState, finalSymState)
  -- Reuse the exact same MethodsRef, Grind.Context, Sym.Context from init.
  -- Pass saved Grind.State and Sym.State as initial values to .run'.
  let symAction : Lean.Meta.Sym.SymM _ :=
    (wrappedAction state.methodsRef state.grindCtx).run' state.grindState
  (symAction state.symCtx).run' state.symState

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
    - **Propositions** (additionally):
      1. Internalize exactly like grind does: `preprocessHypothesis` on the original type,
         then `Grind.add`.
      2. Additionally: simplify with Aeneas simpsets (scalar_tac_simps, etc.) and, if the
         simplified type differs from the original, internalize the simplified fact too.
      3. Optionally run the preprocessing loop (`assertAll >> solvers.loop`). -/
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
        /- Helper: internalize a proposition into the grind e-graph.
           Runs preprocessHypothesis for normalization, then Grind.add with proof chaining. -/
        let addProp (propType : Expr) (proof : Expr) : GoalM Unit := do
          let r ← Grind.preprocessHypothesis propType
          if let some ppH := r.proof? then
            Grind.add r.expr (mkApp4 (mkConst ``Eq.mp [0]) propType r.expr ppH proof)
          else
            Grind.add r.expr proof
        /- Step 1: internalize the proposition exactly the way grind does -/
        addProp type localDecl.toExpr
        /- Step 2: additionally, simplify with Aeneas simpsets and, if the resulting
           type is different from the original, internalize this simplified fact too.
           Note: the type may differ even when `simpResult.proof?` is none (proof by
           reflection / definitional equality), so we compare expressions directly. -/
        let (simpResult, _) ← Lean.Meta.simp type simpCtx simprocs
        let simplifiedType ← instantiateMVars simpResult.expr
        if !simplifiedType.equal type then
          let simpPrf : Expr :=
            if let some simpH := simpResult.proof? then
              mkApp4 (mkConst ``Eq.mp [0]) type simplifiedType simpH localDecl.toExpr
            else
              localDecl.toExpr
          addProp simplifiedType simpPrf
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
  let (simpCtx, simprocs) ← mkPreprocessSimpCtx
  let ((goalState, contradiction), grindState, symState, symCtx, grindCtx, methodsRef) ←
    runGrindFresh params do
      let goal ← Grind.mkGoalCore mvarId
      let (goal, contradiction) ← internalizeHypotheses goal config simpCtx simprocs
      pure (goal.toGoalState, contradiction)
  pure { grindState, symState, symCtx, grindCtx, methodsRef, goalState, contradiction, params, simpCtx, simprocs }

/-- Update the grind state after new fvars have been introduced (by `introOutputs` or
    case splits). Only processes fvars with index ≥ `nextDeclIdx` (incremental). -/
def updateStepGrindState (state : StepGrindState) (config : Config) (mvarId : MVarId)
    : MetaM StepGrindState := do
  let action : GrindM _ := do
    -- Reconstruct Goal from saved GoalState + current MVarId
    let goal : Goal := { toGoalState := state.goalState, mvarId }
    -- Process only NEW fvars (via nextDeclIdx)
    let (goal, contradiction) ← internalizeHypotheses goal config state.simpCtx state.simprocs
    pure (goal.toGoalState, contradiction)
  let ((goalState, contradiction), grindState, symState) ←
    runGrindWithState state action
  pure { state with grindState, symState, goalState, contradiction := state.contradiction || contradiction }

/-- Discharge a precondition using `Grind.solve` with the threaded grind state.

    The threaded state (e-graph, satellite solvers, Sym.State) contains all accumulated
    knowledge from prior `step` calls. `Grind.solve` adds the negation of the target
    to the e-graph and runs the full solver pipeline (assertAll, satellite solvers,
    e-matching, case splitting) to find a contradiction.

    The proof is wrapped in an auxiliary theorem (`mkAuxTheorem`) to prevent kernel
    reduction loops in recursive theorems. Without this, the grind proof term (which
    chains through `Classical.byContradiction` + linear arithmetic) can trigger
    `maxRecDepth` during the kernel's well-founded recursion checking.

    Returns `true` if the precondition was solved, `false` otherwise.
    On failure, all MetaM state changes are reverted (via `observing?`). -/
def dischargeWithGrindState (state : StepGrindState) (precondMVarId : MVarId)
    : MetaM Bool := do
  let result ← observing? do
    let mvarDecl ← precondMVarId.getDecl
    let goalState : GoalState :=
      { state.goalState with
        nextDeclIdx := mvarDecl.lctx.decls.size }
    let action : GrindM _ := do
      let goal : Goal := { toGoalState := goalState, mvarId := precondMVarId }
      match ← Grind.solve goal with
      | none   => pure true
      | some _ => pure false
    let (solved, _, _) ← runGrindWithState state action
    unless solved do throwError "grind could not solve precondition"
    /- Wrap the proof in an auxiliary theorem to prevent kernel reduction loops.
       Grind proofs chain through Classical.byContradiction + Int.Linear.eq_of_core
       which cause maxRecDepth in the kernel during well-founded recursion checking
       for recursive theorems (the kernel tries to reduce the proof, which references
       hypotheses from the recursive call, triggering infinite unfolding). -/
    let proof ← instantiateMVars (mkMVar precondMVarId)
    let goalType ← precondMVarId.getType
    let auxTheorem ← Lean.Meta.mkAuxTheorem goalType proof (zetaDelta := true)
    precondMVarId.assign auxTheorem
  return result.isSome

/-- Update the step state by internalizing new hypotheses from the given goal.
    No-op if grind state threading is disabled (`grindState? = none`). -/
def StepState.update (state : StepState) (config : Config) (mvarId : MVarId) : MetaM StepState :=
  match state.grindState? with
  | some gs => do
    let gs' ← updateStepGrindState gs config mvarId
    pure { state with grindState? := some gs' }
  | none => pure state
end Step

end Aeneas
