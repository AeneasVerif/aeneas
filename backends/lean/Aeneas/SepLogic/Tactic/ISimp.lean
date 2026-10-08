module
public import Aeneas.SepLogic.Tactic.IFrame
public meta import Aeneas.SepLogic.Tactic.IFrame
public meta import Lean
public meta import AeneasMeta.Simp

/-! `isimp` is the non-failing `iframe`: it simplifies an entailment and leaves what it cannot prove
as goals. It runs the `isimps` simp set and `normalizeSep`, then `prepareGoal` (shared with
`iframe`), cancels only atoms with a unique match (`cancelGoal (unique := true)`), introduces
wands and simplifies the residue. Like CFML `xsimpl` leaving a residual entailment; refusing to
choose among ambiguous matches is specific to this tactic. -/

public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Normalize Matchers

namespace IFrame

/-- Like `solveGoal`, but stops at what it cannot prove instead of failing; with
`useHyps := false`, the goal is never rewritten with the hypotheses. -/
partial def simplifyGoal (goal : MVarId) (useHyps : Bool := true) : TacticM (List MVarId) := do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  if target.isAppOfArity ``postEntails 3 then
    let (_, next) ← goal.intro1P
    return ← simplifyGoal next useHyps
  unless target.isAppOfArity ``Entails 2 do return [goal]
  if ← isFrameInference goal then return [goal]
  let some (goal, witnesses) ← prepareGoal goal useHyps | return []
  let goal ← cancelGoal goal (unique := true)
  let wandGoal? ← goal.withContext do
    let some (source, destination) ← entailment? goal | return none
    let some (lemmaName, premise) ← wandIntro? source (← reducePostApplication destination)
      | return none
    let next ← mkFreshExprSyntheticOpaqueMVar premise
    goal.assign (← mkAppM lemmaName #[next])
    return some next.mvarId!
  let goals ← match wandGoal? with
    | some wandGoal => simplifyGoal wandGoal useHyps
    | none => do
      let hyps ← if useHyps then goal.withContext do
          return (← (← getLCtx).getAssumptions).map (·.fvarId) |>.toArray
        else pure #[]
      let some goal ← simpGoal goal true
          { addSimpThms := #[``sep_emp_l_eq, ``sep_emp_r_eq, ``sep_ipure_eq,
              ``entails_emp_ipure_iff, ``entails_refl, ``and_true, ``true_and],
            hypsToUse := hyps }
        | pure []
      if ← goal.withContext goal.assumptionCore then pure [] else pure [goal]
  (witnesses.toList ++ goals).filterM fun goal => return !(← goal.isAssigned)

end IFrame

/-- Like `iframe`, but leaves unsolved pure obligations as goals. `isimp only` neither unfolds
with `isimps` nor rewrites with the hypotheses. -/
syntax (name := iSimp) "isimp" (" only")? (" [" term,* "]")? : tactic

private def evalISimp (lemmas : Array (TSyntax `term)) (simpOnly : Bool := false) : TacticM Unit :=
  Tactic.focus do withMainContext do
    let simpLemmas ← lemmas.mapM fun stx => `(Parser.Tactic.simpLemma| $stx:term)
    let goal ← getMainGoal
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    let spatial := target.isAppOfArity ``Entails 2 || target.isAppOfArity ``postEntails 3
    let frameInference ← isFrameInference goal
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
