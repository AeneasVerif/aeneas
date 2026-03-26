/-
Copyright (c) 2025 Aeneas contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Son Ho
-/
import Lean

/-!
# SymM Helpers for Step Tactics

Utility functions for running the `step`/`step*` tactic pipeline within `SymM`
(the incremental expression-sharing monad). These helpers bridge between SymM and
TacticM where necessary.

## Background

The `step`/`step*` tactics are being migrated from `TacticM` to `SymM` for performance
(incremental expression sharing/caching). `SymM` wraps `MetaM`, not `TacticM`, so we
need helpers to call TacticM from within the SymM pipeline (e.g., for `step by tactic`
or for running precondition-solving automation that lives in TacticM).
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

end Step

end Aeneas
