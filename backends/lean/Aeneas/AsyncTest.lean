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

local syntax "sync_solve" : tactic
local elab "sync_solve" : tactic => do trySync

def tryAsync : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure "repeatTac") (repeatTac splitConjTarget)
  allGoalsAsync (do
    Aeneas.omegaTactic {})

local syntax "async_solve" : tactic
local elab "async_solve" : tactic => do tryAsync

-- This is: `x * y < bound ∧ x * y < bound + 1 ∧ ...` (there are `count` conjuncts)
def goal (x y bound count : Nat) : Prop :=
  if count = 0 then True
  else x + y < bound ∧ goal x y (bound + 1) (count - 1)

/- Note that when measuring time the variance is quite big -/
--set_option trace.profiler true in
set_option maxRecDepth 2048 in
def test (x y : Nat) (h : x < 10) (h : y < 20) : goal x y 200 200
  := by
  simp only [goal, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.reduceAdd, Nat.add_one_sub_one, one_ne_zero,
    tsub_self, and_true]
  --sync_solve -- 3.072428s (scalar_tac) -- 0.53 (omega)
  async_solve -- 1.18s (scalar_tac) -- 0.67s (omega) -- 0.23s (no replaceLevel) -- 0.19s (no auxiliary lemma)


namespace Aeneas.Async.Test
