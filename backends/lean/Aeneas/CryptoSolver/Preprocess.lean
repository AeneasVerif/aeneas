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

/-- Unfold user-defined functions in the goal type.
    Only unfolds constants defined in the current module (not imported from
    Lean core, Mathlib, etc.), so library definitions are left intact. -/
private def unfoldUserDefs (goal : MVarId) : MetaM MVarId := do
  goal.withContext do
    let tgt ← goal.getType
    let env ← getEnv
    let tgt' ← Meta.transform tgt (pre := fun e => do
      if !e.isApp then return .continue
      let fn := e.getAppFn
      if !fn.isConst then return .continue
      let name := fn.constName!
      -- Only unfold constants defined in the current module (user-defined)
      if env.getModuleIdxFor? name |>.isSome then return .continue
      -- Try to unfold this user-defined constant
      match ← withTransparency .all <| Meta.unfoldDefinition? e with
      | some e' => return .visit e'
      | none => return .continue)
    -- Zeta-reduce any let-bindings introduced by unfolding
    let tgt' ← Meta.zetaReduce tgt'
    if tgt' != tgt then goal.change tgt'
    else pure goal

/-- Preprocess: substitute equalities, unfold user defs, unfold let-bindings,
    destructure ∧ hypotheses, and split conjunctions -/
def preprocessGoal (goal : MVarId) : MetaM (List MVarId) := do
  -- Step 1: Substitute equalities from context
  let goal ← try
    match ← goal.substEqs with
    | some g => pure g
    | none => pure goal
  catch _ => pure goal
  -- Step 2: Unfold user-defined functions (e.g. mont_reduce)
  let goal ← unfoldUserDefs goal
  -- Step 3: Unfold let-bindings in the goal (let t := ... in ...)
  let goal ← do
    let tgt ← goal.getType
    if tgt.isLet then
      let tgt' ← Meta.zetaReduce tgt
      goal.change tgt'
    else
      pure goal
  -- Step 4: Destructure ∧ in hypotheses (h : A ∧ B → h.1 : A, h.2 : B)
  let goal ← destructureAndHyps goal
  -- Step 5: Split conjunctions in the goal
  splitAllConj goal
where
  /-- Destructure conjunction hypotheses into components -/
  destructureAndHyps (goal : MVarId) : MetaM MVarId := do
    destructureLoop goal 10
  destructureLoop (g : MVarId) : Nat → MetaM MVarId
    | 0 => return g
    | fuel + 1 => do
      -- Find a conjunction hypothesis
      let andDecl? ← g.withContext do
        let ctx ← getLCtx
        for decl in ctx do
          if decl.isAuxDecl then continue
          let ty ← instantiateMVars decl.type
          let ty ← whnfD ty
          match_expr ty with
          | And _ _ => return some decl
          | _ => continue
        return none
      match andDecl? with
      | some decl =>
        -- Use cases to split h : A ∧ B
        let #[s] ← g.cases decl.fvarId #[{ varNames := [`left, `right] }]
          | return g
        destructureLoop s.mvarId fuel
      | none => return g

end Aeneas.CryptoSolver
