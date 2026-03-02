import Aeneas.GrindSimpTac.Init
import Aeneas.Grind.Init

/-!
# MonoGrindState: grind state building with preprocessing simpset

`MonoGrindState` builds a grind e-graph from local declarations, optionally
simplifying each hypothesis with a preprocessing simpset before adding it.

The safe-equality cross-simplification of hypotheses is a **separate pass**
that runs before `MonoGrindState` is built (see `simplifyHypsWithSafeEqs`).
This separation keeps the grind state building straightforward.

After all hypotheses are processed, `deriveFacts` runs e-matching saturation
and arithmetic solver pre-computation on the resulting state.
-/

namespace Aeneas.GrindSimpTac

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

/-- Grind e-graph state built from local declarations. -/
structure MonoGrindState where
  /-- The grind Goal containing the e-graph with internalized hypotheses. -/
  goal : Lean.Meta.Grind.Goal
  /-- Set of FVarIds that have been processed (added to the grind state). -/
  processedFVars : FVarIdSet := {}

/-- Add a local declaration to the `MonoGrindState`.

    For propositions:
    1. Simplify the type with `preprocessCtx` (if non-empty)
    2. Add the (possibly simplified) fact to the grind e-graph via `Lean.Meta.Grind.add`

    For non-propositions:
    - Internalize the local declaration in the grind e-graph

    The simplified type is added to grind with a properly constructed proof
    (`Eq.mp` from the original type to the simplified type). -/
def MonoGrindState.addLocalDecl (state : MonoGrindState) (fvarId : FVarId)
    (preprocessCtx : Simp.Context) (preprocessSimprocs : Simp.SimprocsArray) :
    Lean.Meta.Grind.GrindM MonoGrindState := do
  let localDecl ← fvarId.getDecl
  if localDecl.isImplementationDetail then return state
  let type ← instantiateMVars localDecl.type
  if !(← isProp type) then
    -- Non-prop: just internalize in grind
    let goal ← Lean.Meta.Grind.GoalM.run' state.goal
      (Lean.Meta.Grind.internalizeLocalDecl localDecl)
    return { state with goal, processedFVars := state.processedFVars.insert fvarId }
  -- Prop hypothesis: optionally simplify with preprocessing simpset
  let (simplifiedType, simpProof?) ←
    if !preprocessCtx.simpTheorems.isEmpty then do
      let (simpResult, _) ← Lean.Meta.simp type preprocessCtx preprocessSimprocs
      let simplifiedType ← instantiateMVars simpResult.expr
      pure (simplifiedType, simpResult.proof?)
    else
      pure (type, none)
  -- Add to grind e-graph, mirroring processHypotheses
  let goal ← Lean.Meta.Grind.GoalM.run' state.goal do
    let r ← Lean.Meta.Grind.preprocessHypothesis simplifiedType
    -- Build proof chain: fvar → (optional Eq.mp for simp) → (optional Eq.mp for preprocess)
    let basePrf : Expr :=
      if let some simpH := simpProof? then
        mkApp4 (mkConst ``Eq.mp [0]) type simplifiedType simpH localDecl.toExpr
      else
        localDecl.toExpr
    if let some ppH := r.proof? then
      Lean.Meta.Grind.add r.expr
        (mkApp4 (mkConst ``Eq.mp [0]) simplifiedType r.expr ppH basePrf)
    else
      Lean.Meta.Grind.add r.expr basePrf
  return { goal, processedFVars := state.processedFVars.insert fvarId }

/-- Initialize a `MonoGrindState` from an MVarId.

    Creates a fresh grind Goal with a dummy target, then processes all local
    declarations (oldest first) via `addLocalDecl`, simplifying each prop
    hypothesis with the preprocessing simpset before adding it to the grind
    e-graph. -/
def MonoGrindState.initializeFromMVar (mvarId : MVarId)
    (preprocessSimpThms : Array SimpTheorems) (preprocessSimprocs : Simp.SimprocsArray)
    (preprocessSimpConfig : Simp.Config := { failIfUnchanged := false, maxDischargeDepth := 0 }) :
    Lean.Meta.Grind.GrindM MonoGrindState := do
  mvarId.withContext do
  -- Create a temporary mvar (same lctx, dummy target) for the grind Goal
  let tmpMvar ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True) `grind_base
  let tmpMvarId := tmpMvar.mvarId!
  let tmpMvarId ← tmpMvarId.unfoldReducible
  let tmpMvarId ← tmpMvarId.betaReduce
  appendTagSuffix tmpMvarId `grind_base
  let goal ← Lean.Meta.Grind.mkGoalCore tmpMvarId
  -- Build preprocessing simp context
  let congrTheorems ← getSimpCongrTheorems
  let preprocessCtx ← Simp.mkContext preprocessSimpConfig
    (simpTheorems := preprocessSimpThms) congrTheorems
  -- Process all local declarations (oldest first)
  let mut state : MonoGrindState := { goal }
  let lctx := (← tmpMvarId.getDecl).lctx
  for decl in lctx do
    if (← Lean.Meta.Grind.GoalM.run state.goal (return (← Lean.Meta.Grind.isInconsistent))).1 then
      break
    state ← state.addLocalDecl decl.fvarId preprocessCtx preprocessSimprocs
  -- Mark all decls as processed in the grind goal
  let goal ← Lean.Meta.Grind.GoalM.run' state.goal Lean.Meta.Grind.setNextDeclToEnd
  return { state with goal }

/-- Run e-matching saturation and arithmetic pre-derivation on the grind state.

    1. E-matching saturation (configurable number of rounds)
    2. `assertAll` to drain pending facts
    3. `Solvers.check` to pre-compute arithmetic solver state -/
def MonoGrindState.deriveFacts (state : MonoGrindState) (saturationRounds : Nat := 1) :
    Lean.Meta.Grind.GrindM MonoGrindState := do
  let mut goal := state.goal
  -- E-matching saturation
  for _ in List.range saturationRounds do
    if goal.inconsistent then break
    let (progress, goal') ← Lean.Meta.Grind.GoalM.run goal Lean.Meta.Grind.ematch
    goal := goal'
    if !progress then break
    goal ← Lean.Meta.Grind.GoalM.run' goal Lean.Meta.Grind.processNewFacts
  -- Drain pending facts + pre-derive arithmetic
  goal ←
    match (← (Lean.Meta.Grind.Action.assertAll).run goal) with
    | .closed _ => pure goal
    | .stuck gs => do
      let g := gs[0]? |>.getD goal
      let (_, g) ← Lean.Meta.Grind.GoalM.run g (discard Lean.Meta.Grind.Solvers.check)
      pure g
  return { state with goal }

end Aeneas.GrindSimpTac
