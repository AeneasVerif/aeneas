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
- **Persistent SymM session**: A single SymM session (Context + mutable IO.Ref State)
  is created once at initialization and shared across all `runGrindWithState` calls.
  SymM caches (inferType, congrInfo, hash-consing) grow monotonically and benefit all
  iterations. This replaces the old value-based save/restore of `Sym.State`, which
  required creating a fresh `SymM.run` session each time and broke cache accumulation.
- **Custom internalization**: Uses Aeneas simpsets (scalar_tac_simps, etc.) for hypothesis
  simplification, followed by grind's `canon`/`shareCommon` for canonical form, then `add`.
- **Preprocessing per proposition**: After each prop hypothesis is internalized, we run
  the preprocessing loop (`assertAll >> solvers.loop`). This ensures:
  - we preprocess fact derivation
  - the fact that we run it after *each* prop hypothesis ensures the grind state at any
    point is identical whether we initialize from scratch (single `step`) or incrementally
    (threaded `step*`).

## Session Architecture

```
createPersistentSymSession
  → (symCtx : Sym.Context, symRef : IO.Ref Sym.State)

extractGrindConfig params
  → (grindCtx : Grind.Context, methodsRef : Grind.MethodsRef)

runGrindFresh / runGrindWithState
  → layers GrindM on top of the persistent SymM session (symCtx, symRef)
  → GrindM state is passed by value (saved/restored per call)
  → Sym.State mutations (caches) persist through symRef
```

## Discharge with `Grind.solve`

To discharge preconditions, we construct a `Goal` from the precondition `MVarId` and the
threaded GoalState, then call `Grind.solve`. Grind.State is restored from the saved value
via `StateRefT.run'`; Sym.State is accessed through the persistent `symRef` (no
save/restore needed — cache additions are safe to keep even on rollback via `observing?`).
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

/-- Create a persistent SymM session (Context + mutable State ref).
    The Context holds pointer-identical SharedExprs (True, False, etc.);
    the IO.Ref holds the Sym.State (share tables, inferType cache, etc.)
    and persists across all subsequent `runGrindWithState` calls. -/
private def createPersistentSymSession
    : MetaM (Lean.Meta.Sym.Context × IO.Ref Lean.Meta.Sym.State) :=
  Lean.Meta.Sym.SymM.run do
    let ctx ← readThe Lean.Meta.Sym.Context
    let state ← getThe Lean.Meta.Sym.State
    let ref ← IO.mkRef state
    return (ctx, ref)

/-- Extract `Grind.Context` and `MethodsRef` from a temporary `GrindM.run`.
    These are pure config objects (no SharedExprs references) and can be
    used across SymM sessions. -/
private def extractGrindConfig (params : Grind.Params)
    : MetaM (Grind.Context × Grind.MethodsRef) :=
  Grind.GrindM.run (params := params) do
    pure (← readThe Grind.Context, ← readThe Grind.MethodsRef)

/-- Run a `GrindM` action on a persistent SymM session with a fresh Grind.State.
    Used for initialization — returns the final Grind.State for subsequent reuse. -/
private def runGrindFresh {α} (symCtx : Lean.Meta.Sym.Context)
    (symRef : IO.Ref Lean.Meta.Sym.State)
    (grindCtx : Grind.Context) (methodsRef : Grind.MethodsRef)
    (action : GrindM α) : MetaM (α × Grind.State) := do
  let wrappedAction : GrindM (α × Grind.State) := do
    let result ← action
    let grindState ← get
    pure (result, grindState)
  -- Layer GrindM (ReaderT MethodsRef → ReaderT Grind.Context → StateRefT Grind.State)
  -- on top of the persistent SymM session (symCtx, symRef).
  -- Fresh Grind.State starts as default ({}).
  let symAction : Lean.Meta.Sym.SymM _ :=
    (wrappedAction methodsRef grindCtx).run' {}
  symAction symCtx symRef

/-- Run a `GrindM` action reusing saved contexts and states from a previous run.
    Preserves pointer identity of SharedExprs via the persistent `symRef`.
    SymM caches grow monotonically across calls (mutations through symRef persist). -/
def runGrindWithState {α} (state : StepGrindState) (action : GrindM α)
    : MetaM (α × Grind.State) := do
  let wrappedAction : GrindM (α × Grind.State) := do
    let result ← action
    let finalGrindState ← get
    pure (result, finalGrindState)
  -- Reuse the exact same MethodsRef, Grind.Context, Sym.Context from init.
  -- Restore saved Grind.State as initial value via .run'.
  -- Sym.State is accessed through the persistent symRef (no save/restore needed).
  let symAction : Lean.Meta.Sym.SymM _ :=
    (wrappedAction state.methodsRef state.grindCtx).run' state.grindState
  symAction state.symCtx state.symRef

/-- Internalize local hypotheses into a grind goal.

    **Why we simplify hypotheses on the fly:** For grind to successfully discharge
    preconditions, hypotheses need to be simplified first (normalizing scalar casts,
    unfolding constants via Aeneas simpsets). Previously, `step` would do
    `simp [...] at *; agrind`, which modified the proof context. With threading, we want
    to incrementally internalize hypotheses *without modifying the context* (so the user
    sees a clean context after `step*`). To achieve this, we simplify each hypothesis type
    on the fly during internalization and add the simplified version to the e-graph.

    **What we internalize for each proposition:** We internalize both the original type
    and the simplified type:
    1. The **original type** is internalized first (exactly as grind would). This is done
       out of precaution: if some fvar `f` refers to hypothesis `h` in its type, `h`
       should also be present in the e-graph (though it's unclear whether this is strictly
       necessary).
    2. The **simplified type** (after applying Aeneas simpsets: `scalar_tac_simps`, etc.)
       is additionally internalized if it differs from the original. This is the version
       that grind actually needs to discharge most preconditions.

    **Invariant:** The internalization procedure runs identically whether we:
    (a) initialize from scratch with all current hypotheses (single `step` call), or
    (b) incrementally add hypotheses one by one (threaded `step*`).
    This is critical for `step*?`: the generated proof script (individual `step` calls)
    must produce the same grind state as `step*` (threaded calls), so the number of
    unsolved preconditions is the same in both modes.

    For each local declaration (starting from `goal.nextDeclIdx`):
    - **All declarations**: `internalizeLocalDecl` first (adds the fvar to the e-graph).
    - **Propositions** (additionally):
      1. Internalize the original type via `preprocessHypothesis` + `Grind.add`.
      2. Simplify with Aeneas simpsets and, if the simplified type differs, internalize
         the simplified fact too.
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
           Runs preprocessHypothesis for normalization, then Grind.add with proof chaining.

           **Resilience:** `Grind.add` may throw if the proposition involves types whose
           algebraic instances are incompatible with grind's linarith satellite solver.
           Specifically, `Grind.Arith.Linear.getStructId?` calls `ensureToHomoFieldDefEq`
           which checks that the `HAdd`/`HMul` instances on a type are definitionally equal
           to instances derived from the standard algebra hierarchy (`Grind.AddCommMonoid`,
           etc.). Types with raw `HAdd`/`HMul` instances (not derived from `CommRing`,
           `AddCommMonoid`, etc.) cause this check to throw.

           **Example:** In the SymCrypt ML-KEM verification project, `Spec.Polynomial`
           (polynomials over `Spec.Zq`) has direct `HAdd`/`HMul` instances defined via
           pointwise operations, not derived from any algebra hierarchy. When `step*`
           applies a spec whose postcondition involves `Spec.Polynomial` addition (e.g.,
           `to_poly peSrc1 = to_poly pe_src7 * 3303 * 2 ^ 16`), `Grind.add` throws:
           `` `grind linarith` expected Spec.instHAddPolynomial to be definitionally
           equal to instHAdd ``

           This is a bug (or limitation) in Lean's grind linarith: `getStructId?` should
           return `none` for types it can't handle instead of throwing. Until that is fixed
           upstream (Lean/Meta/Tactic/Grind/Arith/Linear/StructId.lean:234), we catch the
           error here and skip the hypothesis — the e-graph simply has less information,
           which is the correct best-effort behavior. -/
        let addProp (propType : Expr) (proof : Expr) : GoalM Unit := do
          let r ← Grind.preprocessHypothesis propType
          try
            if let some ppH := r.proof? then
              Grind.add r.expr (mkApp4 (mkConst ``Eq.mp [0]) propType r.expr ppH proof)
            else
              Grind.add r.expr proof
          catch e =>
            trace[Step] "addProp: Grind.add failed on hypothesis (skipping):\n  \
              type: {propType}\n  error: {e.toMessageData}"
        /- Step 1: internalize the original type (out of precaution, so that fvars
           referring to this hypothesis in their types also get internalized) -/
        addProp type localDecl.toExpr
        /- Step 2: simplify with Aeneas simpsets (scalar_tac_simps, etc.) and internalize
           the simplified type. This is the version grind actually needs to discharge most
           preconditions — previously `step` would do `simp [...] at *; agrind`, but here
           we simplify on the fly to avoid modifying the user-visible context.
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
    Creates a persistent SymM session, extracts grind config, and internalizes
    all current local hypotheses into a fresh e-graph. -/
def initStepGrindState (config : Config) (mvarId : MVarId) : MetaM StepGrindState := do
  let params ← mkGrindParams config
  let (simpCtx, simprocs) ← mkPreprocessSimpCtx
  -- Create persistent SymM session (Context with SharedExprs + mutable State ref)
  let (symCtx, symRef) ← createPersistentSymSession
  -- Extract grind config (temporary GrindM.run — config objects are session-independent)
  let (grindCtx, methodsRef) ← extractGrindConfig params
  -- Run initialization on the persistent SymM session
  let ((goalState, contradiction), grindState) ←
    runGrindFresh symCtx symRef grindCtx methodsRef do
      let goal ← Grind.mkGoalCore mvarId
      let (goal, contradiction) ← internalizeHypotheses goal config simpCtx simprocs
      pure (goal.toGoalState, contradiction)
  pure { grindState, symRef, symCtx, grindCtx, methodsRef, goalState, contradiction, params, simpCtx, simprocs }

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
  let ((goalState, contradiction), grindState) ←
    runGrindWithState state action
  pure { state with grindState, goalState, contradiction := state.contradiction || contradiction }

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
def dischargeWithGrindState (state : StepGrindState) (config : Config)
    (precondMVarId : MVarId) : MetaM Bool := do
  let result ← observing? do
    /- First, internalize any fvars the e-graph hasn't seen yet.
      The precondition goal's local context may contain hypotheses introduced
      after the last `StepState.update` (e.g., by `split_ifs`, `cases`, or
      tactic-generated intermediate goals). This is unlikely (and would be a bug)
      but something to account for. -/
    let state ← updateStepGrindState state config precondMVarId
    let mvarDecl ← precondMVarId.getDecl
    let goalState : GoalState :=
      { state.goalState with
        nextDeclIdx := mvarDecl.lctx.decls.size }
    let action : GrindM _ := do
      let goal : Goal := { toGoalState := goalState, mvarId := precondMVarId }
      match ← Grind.solve goal with
      | none   => pure true
      | some _ => pure false
    let (solved, _) ← runGrindWithState state action
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
