import Lean
import AeneasMeta.Utils

/-!
# The shared part of an `intro_tactic`

`step` hands the mono/bind premise left by a step theorem to the tactic the specification
statement registers as its `intro_tactic`, which has to bring it to the
`∀ outputs, facts → …` shape `step` introduces the outputs from.

What the judgments have in common there is the treatment of the facts: the markers the
postcondition notation leaves behind have to be reduced, and a fact standing for several
of them has to be split. `intro_split` does exactly that and nothing else, which is all a
judgment whose premise already *is* `∀ x, P x → …` needs; a separation-logic judgment
extracts its facts from an assertion first, and then reuses these same helpers.
-/

namespace Aeneas.Step.Intro

open Lean Meta Elab Tactic

/-- Reduce an application which is stuck on a definition that destructures its argument:
this is the shape of the markers a multi-binder postcondition is built from, which apply
the body of the postcondition to the result tuple.

The definition is unfolded once, and the reduction is kept only when it fires a match with
a *single* alternative, i.e. an irrefutable destructuring. A definition which merely
abbreviates its body is left alone, and so is a genuine case analysis — for a separation
logic, opening a representation predicate would leave an assertion the frame inference can
no longer match. -/
def reduceMarker? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  unless e.getAppFn.isConst && e.getAppNumArgs > 0 do return none
  let some unfolded ← unfoldDefinition? e | return none
  let some matcher ← matchMatcherApp? unfolded | return none
  unless matcher.alts.size == 1 do return none
  let reduced ← whnfCore unfolded
  if reduced == unfolded then return none
  return some reduced

/-- Reduce the markers at the head of `e`. -/
partial def reduceMarkers (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  match ← reduceMarker? e with
  | some e' => reduceMarkers e'
  | none => return e

/-- Normalize the type of a freshly introduced fact and split it into the hypotheses it
stands for: its conjuncts, and the witnesses of its existentials. A fact which says nothing
is dropped. -/
partial def splitHypothesis (goal : MVarId) (fvarId : FVarId) : MetaM MVarId := do
  let goal ← goal.withContext do
    let type ← instantiateMVars (← fvarId.getType)
    let type' ← reduceMarkers type
    /- `replaceLocalDeclDefEq` keeps `fvarId`, unlike `changeLocalDecl`. -/
    if type' == type.consumeMData then pure goal else goal.replaceLocalDeclDefEq fvarId type'
  let type ← goal.withContext do instantiateMVars (← fvarId.getType)
  if type.consumeMData.isConstOf ``True then
    return (← goal.tryClear fvarId)
  unless type.consumeMData.isAppOfArity ``And 2
      || type.consumeMData.isAppOfArity ``Exists 2 do
    return goal
  let subgoals ← goal.cases fvarId
  let some subgoal := subgoals[0]? | return goal
  unless subgoals.size == 1 do return goal
  let mut goal := subgoal.mvarId
  /- The fields are processed from the last one on: modifying one invalidates the
     hypotheses which follow it. -/
  for field in subgoal.fields.reverse do
    if let some fvarId := field.consumeMData.fvarId? then
      goal ← splitHypothesis goal fvarId
  return goal

/-- The hypotheses of the main goal, to be compared with the context a later step reaches. -/
def localHypotheses : TacticM (Std.HashSet FVarId) := do
  (← getMainGoal).withContext do
    pure <| (← getLCtx).foldl (init := ∅) fun acc decl => acc.insert decl.fvarId

/-- Normalize and split the hypotheses which appeared since `before` was taken. -/
def splitNewHypotheses (before : Std.HashSet FVarId) : TacticM Unit := do
  let goal ← getMainGoal
  let introduced ← goal.withContext do
    pure <| (← getLCtx).foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail || before.contains decl.fvarId then acc
      else acc.push decl.fvarId
  let mut goal := goal
  for fvarId in introduced.reverse do
    goal ← splitHypothesis goal fvarId
  replaceMainGoal [goal]

/-- Introduce the binders of the premise, and normalize and split the facts among them.

`step` reverts what this introduces, so the premise comes back in the `∀ outputs, facts → …`
shape it introduces the outputs from — with one binder per fact. -/
elab (name := introSplit) "intro_split" : tactic => do
  let before ← localHypotheses
  replaceMainGoal [(← (← getMainGoal).intros).2]
  withMainContext do
  splitNewHypotheses before

end Aeneas.Step.Intro
