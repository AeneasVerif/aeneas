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

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Normalize Common

/-- Move one existential or pure fact of the precondition into the goal, as a `∀`/`→`. With
`unfold := false`, only syntactic `⌜P⌝` atoms count as pure facts, so that the predicates a later
`step` must match are never opened. -/
private def introStep (unfold : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← exposeEntailment? target
    | throwError "iintro_step: the goal is not a separation-logic entailment"
  let args := entailment.getAppArgs
  let source := args[0]!
  let destination := args[1]!
  let (simpCtx, simprocs) ← Aeneas.Simp.mkSimpCtx true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    .simp { addSimpThms := sepNormThms }
  let (simpResult, _) ← Lean.Meta.simp source simpCtx simprocs
  let normalizedSource ← instantiateMVars simpResult.expr
  let (goal, target, source) ←
    if normalizedSource == source then
      pure (goal, target, source)
    else
      let normalizedTarget ←
        mkEntailmentLike target source destination normalizedSource
      let next ← mkFreshExprSyntheticOpaqueMVar normalizedTarget
      let hEq ←
        match simpResult.proof? with
        | some proof => pure proof
        | none => mkEqRefl source
      goal.assign (← mkAppM ``entails_trans
        #[← mkAppM ``entails_of_eq #[hEq], next])
      pure (next.mvarId!, normalizedTarget, normalizedSource)
  let precondition ← if unfold then exposeConnective source else pure source
  let head := precondition.consumeMData.getAppFn
  if head.isConstOf ``iexists then
    let some u := head.constLevels!.head?
      | throwError "could not determine the universe of {precondition}"
    let preArgs := precondition.consumeMData.getAppArgs
    let ι := preArgs[0]!
    let body := preArgs[1]!
    let newType ← withLocalDeclD `x ι fun x => do
      let newSource ← Lean.Core.betaReduce (mkApp body x)
      let newTarget ← mkEntailmentLike target source destination newSource
      mkForallFVars #[x] newTarget
    let next ← mkFreshExprSyntheticOpaqueMVar newType
    goal.assign (mkAppN (mkConst ``entails_exists_l [u])
      #[ι, destination, body, next])
    replaceMainGoal [next.mvarId!]
  else
    let some (props, rest, eq) ←
        splitPures precondition (limit := some 1) (unfold := unfold)
      | throwError "iintro_step: the precondition has no quantifier or pure fact \
          left to extract:\n{precondition}"
    let proposition := props[0]!
    let newTarget ← mkEntailmentLike target source destination rest
    let newType ← withLocalDeclD `h proposition fun h =>
      mkForallFVars #[h] newTarget
    let next ← mkFreshExprSyntheticOpaqueMVar newType
    let extract := mkAppN (mkConst ``entails_pure_l)
      #[proposition, rest, destination, next]
    goal.assign (← mkAppM ``entails_trans #[← mkAppM ``entails_of_eq #[eq], extract])
    replaceMainGoal [next.mvarId!]

elab "iintro_step" : tactic => introStep true

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
  let some entailment ← exposeEntailment? target | return goal
  unless isPullable entailment.getAppArgs[0]! do return goal
  setGoals [goal]
  introStep (unfold := false)
  let (_, goal) ← (← getMainGoal).intro1P
  pullPrecondition goal

elab "iintro_shallow" : tactic => withMainContext do
  setGoals [← pullPrecondition (← getMainGoal)]

elab "iintro_shallow_post" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← exposeEntailment? target
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
  let markedTarget ← mkEntailmentLike target args[0]! args[1]! markedSource
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
  let some entailment ← exposeEntailment? target
    | throwError "iintro_keep_step: the goal is not a separation-logic entailment"
  let args := entailment.getAppArgs
  let source := args[0]!
  let precondition ← exposeConnective source
  let lctx ← getLCtx
  let inContext (proposition : Expr) : MetaM Bool := lctx.anyM fun decl =>
    pure !decl.isImplementationDetail <&&>
      withNewMCtxDepth (isDefEq decl.type proposition)
  let some (props, rest, eq) ← splitPures precondition (limit := some 1)
      (select := fun proposition => return !(← inContext proposition))
    | throwError "iintro_keep_step: the precondition has no pure fact left to copy"
  let proposition := props[0]!
  let hExtract ← mkAppM ``entails_of_eq #[eq]
  let newType ← withLocalDeclD .anonymous proposition fun h =>
    mkForallFVars #[h] target
  let next ← mkFreshExprSyntheticOpaqueMVar newType
  goal.assign (mkAppN (mkConst ``entails_pure_keep)
    #[proposition, rest, args[1]!, source, hExtract, next])
  let (_, next) ← next.mvarId!.intro1P
  replaceMainGoal [next]

/-- Copy the pure facts of the precondition into the context without consuming them. -/
macro "iintro_keep" : tactic => `(tactic| repeat (iintro_keep_step; rename_i _))

/-- Move the existentials and pure facts of an `Entails`/`postEntails` precondition into the
context. -/
elab "iintro_entail" : tactic => Tactic.focus do withMainContext do
  let goal ← getMainGoal
  if ← isFrameInference goal then
    throwError "iintro_entail: this is a frame-inference goal.  Extracting anything \
      from its left-hand side would lose it from the frame, which was created in \
      an outer context; pull at the level of the specification instead, with `iintro`."
  let goal ← if (← instantiateMVars (← goal.getType)).consumeMData.isAppOfArity ``postEntails 3
    then pure (← goal.intro1P).2 else pure goal
  replaceMainGoal [← pullLeft goal]

end Aeneas.SepLogic
