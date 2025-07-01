import Aeneas.Async.Async
import Aeneas.ScalarTac

namespace Aeneas.Async.Test

open Lean Elab Tactic Utils

/- Run `tac` on the current goals in parallel -/
def allGoalsAsync (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let promises ← asyncRunTacticOnGoals tac mvarIds
  -- Wait for the tasks
  let mut unsolved := #[]
  for (mvarId, promise) in List.zip mvarIds promises.toList do
    match promise.result?.get with
    | none =>
      unsolved := unsolved.push mvarId
    | some x =>
      match x with
      | .none =>
        unsolved := unsolved.push mvarId
      | .some x =>
        /- Successfully generated a proof! Assign the meta-variable -/
        mvarId.assign x
  setGoals unsolved.toList


/- Solve the goal by splitting the conjunctions.
Note that `scalarTac` does quite a few things, so it tends to be expensive (in the example below,
looking at the trace for the synchronous case, it requires ~0.016s for every subgoal).
-/
def trySync : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure "repeatTac") (repeatTac splitConjTarget)
  allGoals (do
    ScalarTac.scalarTac {})

local syntax "sync_solve" : tactic
local elab "sync_solve" : tactic => do trySync

def tryAsync : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure "repeatTac") (repeatTac splitConjTarget)
  allGoalsAsync (do
    ScalarTac.scalarTac {})

local syntax "async_solve" : tactic
local elab "async_solve" : tactic => do tryAsync

-- This is: `x * y < bound ∧ x * y < bound + 1 ∧ ...` (there are `count` conjuncts)
def goal (x y bound count : Nat) : Prop :=
  if count = 0 then True
  else x * y < bound ∧ goal x y (bound + 1) (count - 1)

/- Note that when measuring time the variance is quite big -/
--set_option trace.profiler true in
set_option maxRecDepth 2048 in
def test (x y : Nat) (h : x < 10) (h : y < 20) : goal x y 200 200
  := by
  simp [goal]
  --sync_solve -- 3.072428s
  async_solve -- 1.18s


namespace Aeneas.Async.Test
