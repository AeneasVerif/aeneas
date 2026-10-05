module
public import Aeneas.SepLogic.Tactic.IFrame
public meta import Lean
public meta import AeneasMeta.Simp
public section

namespace Aeneas.SepLogic

/-- Marks the frame inferred by `step`, so that `iintro_shallow` does not traverse it. -/
@[expose] def introFrame (F : IProp) : IProp := F

theorem introFrame_eq (F : IProp) : introFrame F = F := by
  rfl

theorem entails_pure_keep {P : Prop} {H H' H₀ : IProp}
    (hExtract : H₀ ⊢ ⌜P⌝ ∗ H) (h : P → H₀ ⊢ H') : H₀ ⊢ H' := by
  intro heap hH₀
  have ⟨hP, _⟩ := (sep_pure_l P H heap).mp (hExtract heap hH₀)
  exact h hP heap hH₀

end Aeneas.SepLogic

end

public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

private partial def extractPure? (pre : Expr) : Option (Expr × Expr) :=
  let pre := pre.consumeMData
  if pre.isAppOfArity ``ipure 1 then
    none
  else if pre.isAppOfArity ``sep 2 then
    let args := pre.getAppArgs
    let left := args[0]!.consumeMData
    let right := args[1]!.consumeMData
    if left.isAppOfArity ``ipure 1 then
      some (left.appArg!, right)
    else if right.isAppOfArity ``ipure 1 then
      some (right.appArg!, left)
    else
      match extractPure? left with
      | some (proposition, rest) =>
        some (proposition, mkApp2 (mkConst ``sep) rest right)
      | none =>
        match extractPure? right with
        | some (proposition, rest) =>
          some (proposition, mkApp2 (mkConst ``sep) left rest)
        | none => none
  else
    none

elab "iintro_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← IFrame.exposeEntailment? target
    | throwError "iintro_step: the goal is not a separation-logic entailment"
  let args := entailment.getAppArgs
  let source := args[0]!
  let destination := args[1]!
  let (simpCtx, simprocs) ← Aeneas.Simp.mkSimpCtx true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    .simp
    { addSimpThms :=
        #[``sep_exists_l_eq, ``sep_exists_r_eq,
          ``sep_emp_l_eq, ``sep_emp_r_eq] }
  let (simpResult, _) ← Lean.Meta.simp source simpCtx simprocs
  let normalizedSource ← instantiateMVars simpResult.expr
  let (goal, target, source) ←
    if normalizedSource == source then
      pure (goal, target, source)
    else
      let normalizedTarget ←
        IFrame.mkEntailmentLike target source destination normalizedSource
      let next ← mkFreshExprSyntheticOpaqueMVar normalizedTarget
      let hEq ←
        match simpResult.proof? with
        | some proof => pure proof
        | none => mkEqRefl source
      goal.assign (← mkAppM ``entails_trans
        #[← mkAppM ``entails_of_eq #[hEq], next])
      pure (next.mvarId!, normalizedTarget, normalizedSource)
  let precondition ← IFrame.exposeConnective source
  let head := precondition.consumeMData.getAppFn
  let pure? ←
    if precondition.consumeMData.isAppOfArity ``ipure 1 then
      pure (some (precondition.consumeMData.appArg!, mkConst `Aeneas.SepLogic.emp))
    else if precondition.consumeMData.isAppOfArity ``sep 2 then
      let preArgs := precondition.consumeMData.getAppArgs
      let leading ← IFrame.exposeConnective preArgs[0]!
      if leading.consumeMData.isAppOfArity ``ipure 1 then
        pure (some (leading.consumeMData.appArg!, preArgs[1]!))
      else
        pure (extractPure? precondition)
    else
      pure none
  if head.isConstOf ``iexists then
    let some u := head.constLevels!.head?
      | throwError "could not determine the universe of {precondition}"
    let preArgs := precondition.consumeMData.getAppArgs
    let ι := preArgs[0]!
    let body := preArgs[1]!
    let newType ← withLocalDeclD `x ι fun x => do
      let newSource ← Lean.Core.betaReduce (mkApp body x)
      let newTarget ← IFrame.mkEntailmentLike target source destination newSource
      mkForallFVars #[x] newTarget
    let next ← mkFreshExprSyntheticOpaqueMVar newType
    goal.assign (mkAppN (mkConst ``entails_exists_l [u])
      #[ι, destination, body, next])
    replaceMainGoal [next.mvarId!]
  else if let some (proposition, rest) := pure? then
    let normalized := mkApp2 (mkConst ``sep)
      (mkApp (mkConst ``ipure) proposition) rest
    let reorder ← mkAppM ``entails_of_eq #[← IFrame.proveEqAC precondition normalized]
    let newTarget ← IFrame.mkEntailmentLike target source destination rest
    let newType ← withLocalDeclD `h proposition fun h =>
      mkForallFVars #[h] newTarget
    let next ← mkFreshExprSyntheticOpaqueMVar newType
    let extract := mkAppN (mkConst ``entails_pure_l)
      #[proposition, rest, destination, next]
    goal.assign (← mkAppM ``entails_trans #[reorder, extract])
    replaceMainGoal [next.mvarId!]
  else
    throwError "iintro_step: the precondition has no quantifier or pure fact \
      left to extract:\n{precondition}"

/-- Move the existentials and pure facts of an entailment's precondition into the context. -/
syntax (name := iIntro) "iintro" (ppSpace colGt rintroPat)* : tactic

macro_rules
  | `(tactic| iintro $ps:rintroPat*) => do
    if ps.isEmpty then
      `(tactic| repeat (iintro_step; rintro _))
    else
      let steps ← ps.mapM fun p => `(tactic| (iintro_step; rintro $p:rintroPat))
      `(tactic| ($[$steps]*))

/-- Whether `pre` exposes a fact without opening a predicate a later `step` must match. -/
private partial def isPullable (pre : Expr) : Bool :=
  let pre := pre.consumeMData
  if pre.isAppOfArity ``iexists 2 || pre.isAppOfArity ``ipure 1 then true
  else if pre.isAppOfArity ``sep 2 then
    isPullable pre.appFn!.appArg! || isPullable pre.appArg!
  else false

private partial def pullPrecondition (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← IFrame.exposeEntailment? target | return goal
  unless isPullable entailment.getAppArgs[0]! do return goal
  setGoals [goal]
  try
    evalTactic (← `(tactic| iintro_step))
  catch _ =>
    return goal
  let (_, goal) ← (← getMainGoal).intro1P
  pullPrecondition goal

elab "iintro_shallow" : tactic => withMainContext do
  setGoals [← pullPrecondition (← getMainGoal)]

elab "iintro_shallow_post" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← IFrame.exposeEntailment? target
    | normalizeSep
      return
  let args := entailment.getAppArgs
  let source := args[0]!.consumeMData
  unless source.isAppOfArity ``sep 2 do
    normalizeSep
    unless (← getUnsolvedGoals).isEmpty do
      evalTactic (← `(tactic| iintro_shallow))
    return
  let sourceArgs := source.getAppArgs
  let markedSource := mkApp2 (mkConst ``sep) sourceArgs[0]!
    (mkApp (mkConst ``introFrame) sourceArgs[1]!)
  let markedTarget ← IFrame.mkEntailmentLike target args[0]! args[1]! markedSource
  let goal ← goal.change markedTarget
  replaceMainGoal [goal]
  normalizeSep
  unless (← getUnsolvedGoals).isEmpty do
    evalTactic (← `(tactic| iintro_shallow))
  unless (← getUnsolvedGoals).isEmpty do
    evalTactic (← `(tactic| simp only [introFrame_eq]))
    normalizeSep

elab "iintro_keep_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← IFrame.exposeEntailment? target
    | throwError "iintro_keep_step: the goal is not a separation-logic entailment"
  let args := entailment.getAppArgs
  let source := args[0]!
  let precondition ← IFrame.exposeConnective source
  unless precondition.consumeMData.isAppOfArity ``sep 2 do
    throwError "iintro_keep_step: the precondition is not a separating conjunction"
  let leading ← IFrame.exposeConnective precondition.consumeMData.appFn!.appArg!
  unless leading.consumeMData.isAppOfArity ``ipure 1 do
    throwError "iintro_keep_step: the precondition does not start with a pure fact"
  let proposition := leading.consumeMData.appArg!
  if ← (← getLCtx).anyM fun decl =>
      pure !decl.isImplementationDetail <&&> isDefEq decl.type proposition then
    throwError "iintro_keep_step: this pure fact is already in the context"
  let exposed := mkApp2 (mkConst ``sep) leading precondition.consumeMData.appArg!
  let hExtract ← mkAppM ``entails_of_eq #[← IFrame.proveEqAC precondition exposed]
  let newType ← withLocalDeclD .anonymous proposition fun h =>
    mkForallFVars #[h] target
  let next ← mkFreshExprSyntheticOpaqueMVar newType
  goal.assign (← mkAppM ``entails_pure_keep #[hExtract, next])
  let (_, next) ← next.mvarId!.intro1P
  replaceMainGoal [next]

/-- Copy the pure facts of the precondition into the context without consuming them. -/
macro "iintro_keep" : tactic => `(tactic| repeat (iintro_keep_step; rename_i _))

/-- Alias of `iframe`. -/
syntax "isimpl" (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| isimpl) => `(tactic| iframe)
  | `(tactic| isimpl by $tac) => `(tactic| iframe by $tac)

elab "iintro_entail" : tactic => Tactic.focus do withMainContext do
  replaceMainGoal [← IFrame.pullGoal (← getMainGoal)]

end Aeneas.SepLogic
