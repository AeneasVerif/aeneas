module
public import Aeneas.SepLogic.Tactic.IFrame
public meta import Aeneas.SepLogic.Tactic.IFrame
public meta import Lean
public meta import AeneasMeta.Simp
public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

namespace IFrame

private def cancelGoal (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless target.isAppOfArity ``Entails 2 do return goal
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
  let mut remaining ← flatten source
  let mut matched := #[]
  let mut unmatched := #[]
  for expected in ← flatten destination do
    let mut found := none
    for h : i in [:remaining.size] do
      if ← isDefEq expected remaining[i] then
        found := some i
        break
    match found with
    | some i =>
      matched := matched.push expected
      remaining := remaining.eraseIdx! i
    | none => unmatched := unmatched.push expected
  if matched.isEmpty then return goal
  let frame := mkStar matched
  let left := mkStar remaining
  let right := mkStar unmatched
  let residual ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Entails #[left, right])
  let leftEq ← proveEqAC source (← mkAppM ``sep #[frame, left])
  let rightEq ← proveEqAC (← mkAppM ``sep #[frame, right]) destination
  let framed ← mkAppM ``sep_mono #[← mkAppM ``entails_refl #[frame], residual]
  let finish ← mkAppM ``entails_trans #[framed, ← mkAppM ``entails_of_eq #[rightEq]]
  goal.assign (← mkAppM ``entails_trans #[← mkAppM ``entails_of_eq #[leftEq], finish])
  return residual.mvarId!

partial def simplifyGoal (goal : MVarId) (useHyps : Bool := true) : TacticM (List MVarId) := do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  if target.isAppOfArity ``postEntails 3 then
    let (_, next) ← goal.intro1P
    return ← simplifyGoal next useHyps
  unless target.isAppOfArity ``Entails 2 do return [goal]
  if ← isFrameInference goal then return [goal]
  let before ← goal.withContext do
    return (← getLCtx).foldl (init := (∅ : Std.HashSet FVarId))
      fun ids decl => ids.insert decl.fvarId
  let goal ← pullLeft goal
  let facts ← goal.withContext do
    return (← (← getLCtx).getAssumptions).filterMap fun decl =>
      if before.contains decl.fvarId then none else some decl.fvarId
  let some goal ← if useHyps then rewritePureFacts goal facts.toArray else pure (some goal)
    | return []
  let (goal, witnesses) ← instantiateRightExists goal
  let goal ← cancelGoal (← exposeGoal goal)
  let wandGoal? ← goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    let args := target.getAppArgs
    unless target.isAppOfArity ``Entails 2 do return none
    let destination ← reducePostApplication args[1]!
    unless destination.isAppOfArity ``postWand 3 do return none
    let wandArgs := destination.getAppArgs
    let premise ← mkAppM ``postEntails
      #[← mkAppM ``postSep #[wandArgs[1]!, args[0]!], wandArgs[2]!]
    let next ← mkFreshExprSyntheticOpaqueMVar premise
    goal.assign (← mkAppM ``postWand_intro #[next])
    return some next.mvarId!
  if let some wandGoal := wandGoal? then
    let goals ← simplifyGoal wandGoal useHyps
    return ← (witnesses.toList ++ goals).filterM fun goal => return !(← goal.isAssigned)
  let finish ← if useHyps then
    `(tactic| (
      simp (config := { failIfUnchanged := false }) only
        [sep_emp_l_eq, sep_emp_r_eq, sep_ipure_eq, entails_emp_ipure_iff, entails_refl,
          and_true, true_and, *];
      try assumption))
    else
    `(tactic| (
      simp (config := { failIfUnchanged := false }) only
        [sep_emp_l_eq, sep_emp_r_eq, sep_ipure_eq, entails_emp_ipure_iff, entails_refl,
          and_true, true_and];
      try assumption))
  let (goals, _) ← runTactic goal finish
  return ← (witnesses.toList ++ goals).filterM fun goal => return !(← goal.isAssigned)

end IFrame

/-- Like `iframe`, but leaves unsolved pure obligations as goals. -/
syntax (name := iSimp) "isimp" (" only")? (" [" term,* "]")? : tactic

private def evalISimp (lemmas : Array (TSyntax `term)) (simpOnly : Bool := false) : TacticM Unit :=
  Tactic.focus do withMainContext do
    let simpLemmas ← lemmas.mapM fun stx => `(Parser.Tactic.simpLemma| $stx:term)
    let goal ← getMainGoal
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    let spatial := target.isAppOfArity ``Entails 2 || target.isAppOfArity ``postEntails 3
    let frameInference ← IFrame.isFrameInference goal
    if spatial && !frameInference && !simpOnly then
      evalTactic (← `(tactic|
        simp (config := { failIfUnchanged := false, dsimp := false }) only
          [isimps, $simpLemmas,*]))
    else if !lemmas.isEmpty then
      evalTactic (← `(tactic|
        simp (config := { failIfUnchanged := false, dsimp := false }) only [$simpLemmas,*]))
    unless (← getUnsolvedGoals).isEmpty || frameInference do normalizeSep
    unless (← getUnsolvedGoals).isEmpty || !spatial || frameInference do
      replaceMainGoal (← IFrame.simplifyGoal (← getMainGoal) (!simpOnly))

elab_rules : tactic
  | `(tactic| isimp) => evalISimp #[]
  | `(tactic| isimp [$lemmas,*]) => evalISimp lemmas.getElems
  | `(tactic| isimp only) => evalISimp #[] true
  | `(tactic| isimp only [$lemmas,*]) => evalISimp lemmas.getElems true

end Aeneas.SepLogic
