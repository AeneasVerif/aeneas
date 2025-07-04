import AeneasMeta.Async.Async
import AeneasMeta.Simp
import Lean

/-! We're putting the tactics used in the tests in a file different from the tests themselves because
  running tactics from the current file waits on compilation of all definitions.
  See https://github.com/AeneasVerif/aeneas/pull/561#event-18412506656
 -/

namespace Aeneas.Async.Test

open Lean Elab Tactic Utils

/- Solve the goal by splitting the conjunctions.
Note that `scalarTac` does quite a few things, so it tends to be expensive (in the example below,
looking at the trace for the synchronous case, it requires ~0.016s for every subgoal).
-/
def trySyncOmega : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure "repeatTac") (repeatTac splitConjTarget)
  allGoals (Tactic.Omega.omegaTactic {})

scoped syntax "sync_solve_omega" : tactic
scoped elab "sync_solve_omega" : tactic => do trySyncOmega

def tryAsyncOmega : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure "repeatTac") (repeatTac splitConjTarget)
  allGoalsAsync (Tactic.Omega.omegaTactic {})

scoped syntax "async_solve_omega" : tactic
scoped elab "async_solve_omega" : tactic => do tryAsyncOmega

def tryAsyncSimp : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure "repeatTac") (repeatTac splitConjTarget)
  allGoalsAsync (do
    let _ ← Simp.simpAt false {} {} (.targets #[] true)) (prio := .max)

scoped syntax "async_solve_simp" : tactic
scoped elab "async_solve_simp" : tactic => do tryAsyncSimp

namespace Aeneas.Async.Test
