/-
Copyright (c) 2025 Aeneas contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Son Ho
-/
import Lean
import AeneasMeta.Simp.Simp
import AeneasMeta.Split
import AeneasMeta.Utils
import Aeneas.Tactic.Step.GrindState

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

/-! ## SymM-Native Precondition Discharge

Direct MetaM/SymM replacement for the TacticM `solvePreconditionTac` path.
When `threadGrindState` is enabled (default), preconditions are solved by:
1. Preprocessing the target with ScalarTac simp (target-only, not hypotheses)
2. Calling `dischargeWithGrindState` which uses the warm e-graph from prior steps

This avoids the `runTacticMOnGoal` → TacticM → `solvePreconditionTac` overhead. -/

/-- Preprocess a precondition goal by simplifying the target with ScalarTac simpsets.
    This resolves e.g. `UScalar.cast`, `U128.max` to their simplified forms.
    We must NOT simplify hypotheses: the grind e-graph already has them internalized.
    Returns `none` if simp solved the goal, `some mvarId` otherwise. -/
def preprocessPreconditionTargetM (mvarId : MVarId) : MetaM (Option MVarId) := do
  mvarId.withContext do
  let simpArgs ← Aeneas.ScalarTac.getSimpArgs
  let sconfig : Lean.Meta.Simp.Config := { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
  let (ctx, simprocs) ← Aeneas.Simp.mkSimpCtx true sconfig .simp simpArgs
  simpAtTargetMCached mvarId ctx simprocs

/-- Try to discharge a precondition using the threaded grind state.
    Preprocesses the target, then calls `dischargeWithGrindState`.
    Returns `true` if the goal was solved. -/
def dischargeWithThreadedGrindM (gs : StepGrindState) (config : Config) (mvarId : MVarId) : MetaM Bool := do
  withTraceNode `Step (fun _ => pure m!"dischargeWithThreadedGrindM") do
  match ← preprocessPreconditionTargetM mvarId with
  | none =>
    trace[Step] "Precondition solved by preprocessing!"
    return true
  | some mvarId =>
    dischargeWithGrindState gs config mvarId

/-- Solve a precondition directly in MetaM/SymM, bypassing TacticM.
    When a threaded grind state is available, uses `dischargeWithThreadedGrindM`.
    Returns `true` if the goal was solved. -/
def solvePreconditionM (gs? : Option StepGrindState) (config : Config) (mvarId : MVarId) : MetaM Bool := do
  withTraceNode `Step (fun _ => pure m!"solvePreconditionM") do
  trace[Step] "Precondition: {mvarId}"
  match gs? with
  | some gs =>
    try
      let solved ← dischargeWithThreadedGrindM gs config mvarId
      if solved then
        trace[Step] "Precondition solved via threaded grind!"
        return true
      else
        trace[Step] "Threaded grind failed"
        return false
    catch _ =>
      trace[Step] "Threaded grind threw an exception"
      return false
  | none =>
    return false

/-- Try to discharge a "finish" goal (onFinish in step*) directly in MetaM.
    Uses the threaded grind state if available, with target preprocessing.
    For onFinish, we also try a standalone agrind as fallback (like `evalAGrindWithPreprocess`).
    Returns `true` if the goal was solved.
    IMPORTANT: The caller must save/restore the MetaVar context if this returns `false`,
    because preprocessing simp may have assigned the input mvarId. -/
def dischargeWithThreadedGrindM_onFinish (config : Config) (gs? : Option StepGrindState)
    (mvarId : MVarId) : MetaM Bool := do
  withTraceNode `Step (fun _ => pure m!"dischargeWithThreadedGrindM_onFinish") do
  -- Try threaded grind state first if available
  match gs? with
  | some gs =>
    try
      if ← dischargeWithThreadedGrindM gs config mvarId then
        trace[Step] "Finish goal solved via threaded grind!"
        return true
    catch _ =>
      trace[Step] "Threaded grind threw exception, trying standalone agrind"
  | none => pure ()
  -- Fallback: standalone agrind with preprocessing (MetaM-native)
  mvarId.withContext do
  let simpArgs ← Aeneas.ScalarTac.getSimpArgs
  let sconfig : Lean.Meta.Simp.Config := { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
  -- Preprocess: simp target only (lighter than simpGoal which also does hypotheses)
  let (ctx, simprocs) ← Aeneas.Simp.mkSimpCtx true sconfig .simp simpArgs
  let (result?, _stats) ← Lean.Meta.simpTarget mvarId ctx simprocs
  match result? with
  | none =>
    trace[Step] "Finish goal solved by preprocessing simp!"
    return true
  | some mvarId' =>
    -- Run agrind (MetaM-native, avoids TacticM bridge)
    try
      let params ← Aeneas.Grind.mkParams config.toGrindConfig (← Aeneas.Grind.getAgrindExtensions config.nla) config.withGroundSimprocs
      mvarId'.withContext do
        Lean.Meta.Grind.withProtectedMCtx config.toGrindConfig mvarId' fun mvarId'' => do
          let result ← Lean.Meta.Grind.main mvarId'' params
          if result.hasFailed then
            throwError "`agrind` failed\n{← result.toMessageData}"
      return true
    catch _ =>
      trace[Step] "agrind failed on finish goal"
      return false

/-! ## MVarId-Based Match/ITE Splitting

MetaM ports of `esplitIteAtSpec` and `esplitMatchAtSpec` that work with explicit
MVarId threading instead of TacticM's `focus`/`setGoals`/`getMainGoal`. These are
called from `onMatchSplit` in SymM without bridging to TacticM.

The key changes from the TacticM versions:
- Take `MVarId` explicitly instead of using `getMainGoal`
- Return new `MVarId`s directly instead of using `setGoals`
- Use `mvarId.withContext` instead of `withMainContext`
- `simpGoal` (MetaM) instead of `Simp.simpAt` (TacticM) -/

/-- Split an `if then else` in a spec predicate (MVarId-based, no TacticM).
    Returns list of (hypothesis fvarId, new goal MVarId) pairs. -/
def esplitIteAtSpecM (h : Name) (mvarId : MVarId) : MetaM (List (FVarId × MVarId)) := do
  mvarId.withContext do
  let tgt ← mvarId.getType
  tgt.consumeMData.withApp fun spec? args => do
  if ¬ (spec?.isConstOf ``Std.WP.spec) ∨ args.size ≠ 3 then throwError "Not a valid spec goal"
  let prog := args[1]!
  prog.withApp fun ite? args => do
  trace[Utils] "ite?: {ite?}, args: {args}"
  if ¬ ite?.isConstOf ``ite ∧ ¬ ite?.isConstOf ``dite then throwError "Not an if then else"
  if args.size ≠ 5 then throwError "Incorrect number of arguments"
  let prop := args[1]!
  let decInst := args[2]!
  let target ← mvarId.getType
  let thm ← mkAppOptM ``Decidable.byCases #[prop, target, decInst]
  let thmTy ← inferType thm
  let (goals, _, _) ← forallMetaTelescope thmTy
  let thm := mkAppN thm goals
  mvarId.assign thm
  let goalMVarIds := goals.toList.map Expr.mvarId!
  -- Introduce the equality and simplify each branch
  let results ← goalMVarIds.filterMapM fun goal => do
    let (hFVar, goal) ← goal.intro h
    goal.withContext do
    -- Build simp context: add h as a rewrite rule + ite/dite lemmas
    let mut simpThms : Lean.Meta.SimpTheorems := {}
    simpThms ← simpThms.add (.fvar hFVar) #[] (mkFVar hFVar) (post := true) (inv := false)
    simpThms ← simpThms.addConst ``Bool.false_eq_true
    simpThms ← simpThms.addConst ``ite_false
    simpThms ← simpThms.addConst ``ite_true
    simpThms ← simpThms.addConst ``dite_true
    simpThms ← simpThms.addConst ``dite_false
    let ctx ← Lean.Meta.Simp.mkContext {}
      (simpTheorems := #[simpThms])
      (← Lean.Meta.getSimpCongrTheorems)
    let (result?, _stats) ← Lean.Meta.simpGoal goal ctx
      (simprocs := #[])
      (simplifyTarget := true)
      (fvarIdsToSimp := #[])
    match result? with
    | none => pure none
    | some (_fvars, newGoal) => pure (some (hFVar, newGoal))
  pure results

/-- Split a match in a spec predicate (MVarId-based, no TacticM).
    Returns list of (introduced variables, hypothesis fvarId, new goal MVarId). -/
def esplitMatchAtSpecM (h : Name) (names : Option (List (List (Option Name)))) (mvarId : MVarId)
    : MetaM (List (Array FVarId × FVarId × MVarId)) := do
  withTraceNode `Utils (fun _ => do pure m!"esplitMatchAtSpecM") do
  mvarId.withContext do
  let tgt ← mvarId.getType
  tgt.consumeMData.withApp fun spec? args => do
  if ¬ (spec?.isConstOf ``Std.WP.spec) ∨ args.size ≠ 3 then throwError "Not a valid spec goal"
  let prog := args[1]!
  let some ma ← Meta.matchMatcherApp? prog (alsoCasesOn := true)
    | throwError "not a matcher: {prog}"
  if ma.discrs.size ≠ 1 then throwError "Don't know what to do with > 1 scrutinees: discrs"
  let matcherName := ma.matcherName
  let scrut := ma.discrs[0]!
  let names ← do
    match names with
    | none =>
      ma.alts.toList.mapM fun alt => do
      lambdaTelescope alt.consumeMData fun args _ => do
      args.toList.mapM fun arg => do
      pure (some (← arg.fvarId!.getDecl).userName)
    | some names => pure names
  -- Split — this calls into `Split.esplitCasesOn` which is TacticM.
  -- We bridge through runTacticMOnGoal once for the core splitting logic.
  let goals ← runTacticMOnGoal mvarId do
    Lean.Elab.Tactic.focus do
    Split.esplitCasesOn true scrut matcherName h names
  let goals := goals.1
  trace[Utils] "after esplitCasesOn:\n{goals.map fun (_, _, g) => g}"
  -- Simplify the goal with the equality — this part is MetaM-native
  let goals ← goals.filterMapM fun (vars, hFVar, goal) => do
    goal.withContext do
    trace[Goal] "About to simplify the goal (with h: {← hFVar.getType}):\n{goal}"
    -- Add h as a rewrite rule in the simp context
    let mut simpThms : Lean.Meta.SimpTheorems := {}
    simpThms ← simpThms.add (.fvar hFVar) #[] (mkFVar hFVar) (post := true) (inv := false)
    let ctx ← Lean.Meta.Simp.mkContext {}
      (simpTheorems := #[simpThms])
      (← Lean.Meta.getSimpCongrTheorems)
    let (result?, _stats) ← Lean.Meta.simpGoal goal ctx
      (simprocs := #[])
      (simplifyTarget := true)
      (fvarIdsToSimp := #[])
    match result? with
    | none => pure none
    | some (_fvars, newGoal) => pure (some (vars, hFVar, newGoal))
  pure goals

/-- Split a match or if-then-else in a spec predicate (MVarId-based).
    Returns list of (introduced variables, hypothesis fvarId, new goal MVarId). -/
def esplitAtSpecM (h : Name) (names : Option (List (List (Option Name)))) (mvarId : MVarId)
    : MetaM (List (Array FVarId × FVarId × MVarId)) := do
  withTraceNode `Utils (fun _ => do pure m!"esplitAtSpecM") do
  mvarId.withContext do
  let tgt ← mvarId.getType
  tgt.consumeMData.withApp fun spec? args => do
  if ¬ (spec?.isConstOf ``Std.WP.spec) ∨ args.size ≠ 3 then throwError "Not a valid spec goal"
  let prog := args[1]!
  let ma ← Meta.matchMatcherApp? prog (alsoCasesOn := true)
  if ma.isSome then
    trace[Utils] "splitting a match"
    esplitMatchAtSpecM h names mvarId
  else
    trace[Utils] "splitting an if then else"
    pure ((← esplitIteAtSpecM h mvarId).map fun (hFVar, g) => (#[], hFVar, g))

end Step

end Aeneas
