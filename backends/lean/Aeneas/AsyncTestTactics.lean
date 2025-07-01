import AeneasMeta.Async.Async
import AeneasMeta.COmega
import Aeneas.ScalarTac

namespace Aeneas.Async.Test

open Lean Elab Tactic Utils

/- Solve the goal by splitting the conjunctions.
Note that `scalarTac` does quite a few things, so it tends to be expensive (in the example below,
looking at the trace for the synchronous case, it requires ~0.016s for every subgoal).
-/
def trySync : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure "repeatTac") (repeatTac splitConjTarget)
  allGoals (do
    Tactic.Omega.omegaTactic {})

scoped syntax "sync_solve" : tactic
scoped elab "sync_solve" : tactic => do trySync

def tryAsync : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure "repeatTac") (repeatTac splitConjTarget)
  allGoalsAsync (do
    Aeneas.omegaTactic {})

scoped syntax "async_solve" : tactic
scoped elab "async_solve" : tactic => do tryAsync

namespace Aeneas.Async.Test
