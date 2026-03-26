/-
Copyright (c) 2025 Aeneas contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Son Ho
-/
import Lean
import AeneasMeta.Simp.Simp
import AeneasMeta.Utils

/-!
# SymM Helpers for Step Tactics

Utility functions for running the `step`/`step*` tactic pipeline within `SymM`
(the incremental expression-sharing monad). These helpers bridge between SymM and
TacticM where necessary, and provide SymM-native replacements for TacticM simp
operations to avoid costly TacticM bridging.

## Background

The `step`/`step*` tactics are being migrated from `TacticM` to `SymM` for performance
(incremental expression sharing/caching). `SymM` wraps `MetaM`, not `TacticM`, so we
need helpers to call TacticM from within the SymM pipeline (e.g., for `step by tactic`
or for running precondition-solving automation that lives in TacticM).

## SymM-Native Simp

The `simpAtM` and `dsimpAtM` functions are MetaM-level replacements for the TacticM
`Simp.simpAt` and `Simp.dsimpAt`. They call `simpGoal`/`dsimpGoal` directly, avoiding
the overhead of `Tactic.run` + `pruneSolvedGoals` + goal state management that the
TacticM bridge (`runTacticMOnGoal`) imposes.
-/

namespace Aeneas

namespace Step

open Lean Meta Elab

/-- Run a tactic (given as `Syntax`) on a goal from within `MetaM`.

    Adapted from Mathlib's `Lean.Elab.runTactic'`
    (Copyright (c) Mathlib contributors, MIT license).

    This allows calling TacticM-based tactics from SymM (which wraps MetaM) without
    needing TacticM in the monad stack. Returns the list of unsolved goals. -/
def runTacticFromMeta (mvarId : MVarId) (tacticCode : Syntax)
    (ctx : Term.Context := {}) (s : Term.State := {}) : MetaM (List MVarId) := do
  instantiateMVarDeclMVars mvarId
  let go : TermElabM (List MVarId) :=
    Term.withSynthesize do
      Tactic.run mvarId (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)
  go.run' ctx s

/-- Run a `TacticM` action on a goal from within `MetaM`.

    Useful for running TacticM closures (e.g., `assumTac`, `solvePreconditionTac`)
    from the SymM-based step pipeline. Returns the list of unsolved goals. -/
def runTacticMFromMeta (mvarId : MVarId) (tac : Tactic.TacticM Unit)
    (ctx : Term.Context := {}) (s : Term.State := {}) : MetaM (List MVarId) := do
  let go : TermElabM (List MVarId) :=
    Tactic.run mvarId (tac *> Tactic.pruneSolvedGoals)
  go.run' ctx s

/-- Run a `TacticM α` action on a goal from within `MetaM`, returning both
    the action's result and the list of unsolved goals.

    This is used when the TacticM action produces a value we need (e.g.,
    `simpAt` returns `Option (Array FVarId)`). The value is communicated
    back through an `IO.Ref`. -/
def runTacticMOnGoal (mvarId : MVarId) (tac : Tactic.TacticM α) : MetaM (α × List MVarId) := do
  let resultRef : IO.Ref (Option α) ← IO.mkRef none
  let goals ← runTacticMFromMeta mvarId (do
    let r ← tac
    resultRef.set (some r))
  match ← resultRef.get with
  | some r => return (r, goals)
  | none => throwError "runTacticMOnGoal: tactic did not produce a result"

open Lean.Meta.Sym (SymM)

/-- Run a `SymM` action within `MetaM`.
    Creates a fresh SymM session (Sym.Context + Sym.State) and discards the
    state after completion. For single `step` calls, this is appropriate.
    For `step*`, a persistent session should be used instead. -/
def runInSymM (x : SymM α) : MetaM α :=
  Lean.Meta.Sym.SymM.run x

/-- A persistent SymM session that can be reused across multiple SymM actions.
    Created once at the start of `step*` and passed to each `tryStep` call
    so that inferType caches accumulate across steps. -/
structure SymSession where
  ctx : Lean.Meta.Sym.Context
  stateRef : IO.Ref Lean.Meta.Sym.State

/-- Create a fresh persistent SymM session. -/
def SymSession.create : MetaM SymSession := do
  -- Use SymM.run to create the context and initial state, then capture them
  let ctxRef ← IO.mkRef (none : Option Lean.Meta.Sym.Context)
  let stateRef ← IO.mkRef (none : Option Lean.Meta.Sym.State)
  Lean.Meta.Sym.SymM.run (do
    ctxRef.set (some (← read))
    stateRef.set (some (← get)))
  let some ctx ← ctxRef.get | throwError "SymSession.create: failed to capture context"
  let some state ← stateRef.get | throwError "SymSession.create: failed to capture state"
  let persistentRef ← IO.mkRef state
  return { ctx, stateRef := persistentRef }

/-- Run a `SymM` action within an existing persistent session.
    The state is preserved across calls, so inferType caches accumulate. -/
def SymSession.run (session : SymSession) (x : SymM α) : MetaM α := do
  let state ← session.stateRef.get
  let stRef ← ST.mkRef state
  let result ← x session.ctx stRef
  session.stateRef.set (← stRef.get)
  return result

/-! ## SymM-Native Simp Operations

These replace `runTacticMOnGoal mvarId do Simp.simpAt ...` with direct MetaM calls.
The underlying `simpGoal`/`dsimpGoal` are MetaM and auto-lift into SymM.

**Why this matters for performance:** Each `runTacticMOnGoal` call creates a full
TacticM context via `Tactic.run`, runs `pruneSolvedGoals`, and tears down the context.
These direct MetaM calls skip all of that overhead. In `evalStepCore`, there were 6
such bridges for simp operations — each called on every step in `step*`. -/

/-- Cached version: takes a pre-built simp context instead of rebuilding it each time.
    Use when the same simp configuration is applied on every step. -/
def simpAtTargetMCached (mvarId : MVarId) (ctx : Lean.Meta.Simp.Context)
    (simprocs : Lean.Meta.Simp.SimprocsArray) : MetaM (Option MVarId) := do
  mvarId.withContext do
  let (result?, _stats) ← Lean.Meta.simpGoal mvarId ctx
    (simprocs := simprocs) (simplifyTarget := true) (fvarIdsToSimp := #[])
  match result? with
  | none => return none
  | some (_fvars, mvarId) => return some mvarId

/-- SymM-native replacement for `simpAt` on the target.
    Calls `simpGoal` directly in MetaM (auto-lifted to SymM).
    Returns `none` if the goal was closed, `some mvarId` otherwise. -/
def simpAtTargetM (mvarId : MVarId) (simpOnly : Bool) (config : Lean.Meta.Simp.Config)
    (args : Aeneas.Simp.SimpArgs) : MetaM (Option MVarId) := do
  mvarId.withContext do
  let (ctx, simprocs) ← Aeneas.Simp.mkSimpCtx simpOnly config .simp args
  simpAtTargetMCached mvarId ctx simprocs

/-- Cached version for dsimp. -/
def dsimpAtTargetMCached (mvarId : MVarId) (ctx : Lean.Meta.Simp.Context)
    (simprocs : Lean.Meta.Simp.SimprocsArray) : MetaM (Option MVarId) := do
  mvarId.withContext do
  let (result?, _stats) ← Lean.Meta.dsimpGoal mvarId ctx
    (simprocs := simprocs) (simplifyTarget := true) (fvarIdsToSimp := #[])
  match result? with
  | none => return none
  | some mvarId => return some mvarId

/-- SymM-native replacement for `dsimpAt` on the target.
    Calls `dsimpGoal` directly in MetaM (auto-lifted to SymM).
    Returns `none` if the goal was closed, `some mvarId` otherwise. -/
def dsimpAtTargetM (mvarId : MVarId) (simpOnly : Bool) (config : Lean.Meta.Simp.Config)
    (args : Aeneas.Simp.SimpArgs) : MetaM (Option MVarId) := do
  mvarId.withContext do
  let (ctx, simprocs) ← Aeneas.Simp.mkSimpCtx simpOnly config .dsimp args
  dsimpAtTargetMCached mvarId ctx simprocs

/-- Cached version of simpAtM. -/
def simpAtMCached (mvarId : MVarId) (ctx : Lean.Meta.Simp.Context)
    (simprocs : Lean.Meta.Simp.SimprocsArray) (fvarIdsToSimp : Array FVarId := #[])
    (simplifyTarget : Bool := true) : MetaM (Option (Array FVarId × MVarId)) := do
  mvarId.withContext do
  let (result?, _stats) ← Lean.Meta.simpGoal mvarId ctx
    (simprocs := simprocs) (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIdsToSimp)
  match result? with
  | none => return none
  | some (freshFVarIds, mvarId) =>
    mvarId.withContext do
    let lctx ← getLCtx
    let ldecls := lctx.foldl (fun set decl => set.insert decl.fvarId) Std.HashSet.emptyWithCapacity
    let filteredFVars := fvarIdsToSimp.filter ldecls.contains ++ freshFVarIds
    return some (filteredFVars, mvarId)

/-- SymM-native replacement for `simpAt` that can also simplify hypotheses.
    When `fvarIdsToSimp` is non-empty, simplifies those hypotheses too.
    Returns `none` if the goal was closed, `some (freshFVars, mvarId)` otherwise.
    The `freshFVars` include both surviving original fvars and new replacement fvars
    (replicating the behavior of Aeneas.Simp.customSimpLocation). -/
def simpAtM (mvarId : MVarId) (simpOnly : Bool) (config : Lean.Meta.Simp.Config)
    (args : Aeneas.Simp.SimpArgs) (fvarIdsToSimp : Array FVarId := #[])
    (simplifyTarget : Bool := true) : MetaM (Option (Array FVarId × MVarId)) := do
  mvarId.withContext do
  let (ctx, simprocs) ← Aeneas.Simp.mkSimpCtx simpOnly config .simp args
  simpAtMCached mvarId ctx simprocs fvarIdsToSimp simplifyTarget

/-! ## Cached Simp Contexts for Step Pipeline

Each `step` call uses ~7 simp invocations with fixed configurations. Building the
`Simp.Context` + `SimprocsArray` from scratch each time is wasteful — these can be
built once and reused across all steps in a `step*` traversal. -/

/-- Pre-built simp contexts for the step pipeline. Built once at the start of
    `step*` or `step`, then passed through `StepState` to each step. -/
structure SimpCaches where
  /-- stepSimpExt theorems — used for initial simplification + introOutputs final simp -/
  stepSimps : Lean.Meta.Simp.Context × Lean.Meta.Simp.SimprocsArray
  /-- Decompose nested `predn` (introOutputs phase 1) -/
  decompPredn : Lean.Meta.Simp.Context × Lean.Meta.Simp.SimprocsArray
  /-- Eliminate `qimp_spec`/`qimp` (introOutputs phase 2) -/
  elimQimp : Lean.Meta.Simp.Context × Lean.Meta.Simp.SimprocsArray
  /-- Eliminate `imp` + fold scalar types (introOutputs phase 3, dsimp) -/
  elimImp : Lean.Meta.Simp.Context × Lean.Meta.Simp.SimprocsArray
  /-- Post-condition simplification -/
  postSimps : Lean.Meta.Simp.Context × Lean.Meta.Simp.SimprocsArray
  /-- Final target simplification (stepSimps + unfold pure) -/
  finalSimps : Lean.Meta.Simp.Context × Lean.Meta.Simp.SimprocsArray

/-! ## SymM-Native Assumption Tactic

MetaM port of `singleAssumptionTac` to avoid the `runTacticMOnGoal` bridge.
The original TacticM version uses `withMainContext`/`getMainGoal` which are just
convenience wrappers around `mvarId.withContext` and goal-state management. -/

/-- Build a discrimination tree from the local context of `mvarId`.
    MetaM port of `filterAssumptionTacPreprocess`. -/
def filterAssumptionTacPreprocessM (mvarId : MVarId) : MetaM (DiscrTree FVarId) :=
  mvarId.withContext do
  let decls ← (← getLCtx).getDecls
  let mut dtree := DiscrTree.empty
  for decl in decls do
    dtree ← dtree.insert decl.type decl.fvarId
  pure dtree

/-- Try to close `mvarId` by matching against a local hypothesis using the dtree.
    MetaM port of `filterAssumptionTacCore`. Returns `true` if the goal was closed. -/
def filterAssumptionTacCoreM (mvarId : MVarId) (dtree : DiscrTree FVarId) : MetaM Bool :=
  mvarId.withContext do
  let type ← instantiateMVars (← mvarId.getType)
  let candidates ← dtree.getMatch type
  let asm ← candidates.findM? fun fvar => do
    let localDecl ← fvar.getDecl
    isDefEq type localDecl.type
  match asm with
  | none => return false
  | some fvarId => mvarId.assign (mkFVar fvarId); return true

/-- MetaM port of `singleAssumptionTacCore`.
    Tries to close `mvarId` by matching against a hypothesis.
    When `instMVars` is true, also tries to instantiate metavariables. -/
def singleAssumptionTacCoreM (mvarId : MVarId) (dtree : DiscrTree FVarId)
    (instMVars : Bool) : MetaM Unit :=
  mvarId.withContext do
  mvarId.checkNotAssigned `sassumption
  let goal ← instantiateMVars (← mvarId.getType)
  let goalMVars ← Utils.getMVarIds goal
  if goalMVars.isEmpty then
    unless ← filterAssumptionTacCoreM mvarId dtree do
      throwError "sassumption: failed to find matching assumption"
  else if instMVars then
    match ← Utils.getMatchingAssumptions goal with
    | [(localDecl, _)] =>
      let _ ← isDefEq goal localDecl.type
      mvarId.assign (mkFVar localDecl.fvarId)
    | [] => throwError "Could not find an assumption matching the goal"
    | fvars =>
      let fvars := fvars.map Prod.snd
      throwError "Several assumptions match the goal: {fvars}"
  else throwError "Could not find an assumption matching the goal"

end Step

end Aeneas
