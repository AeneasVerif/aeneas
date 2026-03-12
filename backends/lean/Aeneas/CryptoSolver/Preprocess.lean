import Lean
import Aeneas.CryptoSolver.Init

namespace Aeneas.CryptoSolver

open Lean Meta Elab Tactic

/-- Try to split a conjunction goal into subgoals.
    Non-recursive to avoid termination issues. -/
def trySplitConj (goal : MVarId) : MetaM (Option (MVarId × MVarId)) := do
  goal.withContext do
    let tgt ← goal.getType
    let tgt ← whnfD tgt
    match_expr tgt with
    | And _ _ =>
      let gs ← goal.apply (mkConst ``And.intro)
      match gs with
      | [g1, g2] => return some (g1, g2)
      | _ => return none
    | _ => return none

/-- Split all conjunctions in a goal (iterative) -/
def splitAllConj (goal : MVarId) : MetaM (List MVarId) := do
  let mut worklist := [goal]
  let mut result := []
  let mut fuel := 20  -- prevent infinite loops
  while !worklist.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let g := worklist.head!
    worklist := worklist.tail!
    match ← trySplitConj g with
    | some (g1, g2) =>
      worklist := g1 :: g2 :: worklist
    | none =>
      result := result ++ [g]
  return result ++ worklist

/-- Preprocess: substitute equalities and split conjunctions -/
def preprocessGoal (goal : MVarId) : MetaM (List MVarId) := do
  -- Step 1: Substitute equalities from context
  let goal ← try
    match ← goal.substEqs with
    | some g => pure g
    | none => pure goal
  catch _ => pure goal
  -- Step 2: Split conjunctions
  splitAllConj goal

end Aeneas.CryptoSolver
