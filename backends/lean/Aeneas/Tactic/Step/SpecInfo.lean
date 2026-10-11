module
public import Aeneas.Tactic.Step.PrepareIntroOutputs
public section

namespace Aeneas.Std.WP

#register_spec_info {
    spec_name := ``Std.WP.spec
    arity := 3
    program_index := 1
    post_index := 2
    mk_spec_mono := ``Std.WP.spec_mono
    mk_spec_mono_skip_args := 2
    mk_spec_bind := ``Std.WP.spec_bind
    mk_spec_bind_skip_args := 4
    prepare_intro_outputs := ``Aeneas.Step.prepareIntroOutputs
    to_mvcgen := .some ``Std.WP.spec_to_mvcgen
    liftings := #[
      { from_statement := ``Std.WP.ispec
        conversion_thm := ``Std.WP.ispec_spec
        conversion_thm_inferred_args := 3 }
    ]
  }

#register_spec_info {
    spec_name := ``Std.WP.dspec
    arity := 3
    program_index := 1
    post_index := 2
    mk_spec_mono := ``Std.WP.dspec_mono
    mk_spec_mono_skip_args := 2
    mk_spec_bind := ``Std.WP.dspec_bind
    mk_spec_bind_skip_args := 4
    prepare_intro_outputs := ``Aeneas.Step.prepareIntroOutputs
    to_mvcgen := .some ``Std.WP.dspec_to_mvcgen
    liftings := #[
      { from_statement := ``Std.WP.spec
        conversion_thm := ``Std.WP.spec_dspec
        conversion_thm_inferred_args := 3 },
      { from_statement := ``Std.WP.ispec
        conversion_thm := ``Std.WP.ispec_dspec
        conversion_thm_inferred_args := 3 },
      { from_statement := ``Std.WP.dispec
        conversion_thm := ``Std.WP.dispec_dspec
        conversion_thm_inferred_args := 3 }
    ]
  }

section

open Std Result
open Aeneas.SepLogic
open Lean Elab Meta Tactic

namespace Intro

meta partial def isOutputLike (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if e.isFVar || e.isLit || e.isSort then return true
  if e.isProj then return ← isOutputLike e.projExpr!
  if ← isConstructorApp e then
    return (← e.getAppArgs.allM (fun arg => isOutputLike arg))
  let f := e.getAppFn.consumeMData
  if f.isFVar then return true
  if let .const name _ := f then
    if let some info ← getProjectionFnInfo? name then
      let args := e.getAppArgs
      if h : info.numParams < args.size then
        return ← isOutputLike args[info.numParams]
  return false

meta def reduceMarker? (markers : Array Name) (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  let .const name _ := e.getAppFn | return none
  unless markers.contains name do return none
  let some unfolded ← unfoldDefinition? e | return none
  let some matcher ← matchMatcherApp? unfolded | return none
  unless matcher.alts.size == 1 do return none
  for discr in matcher.discrs do
    unless ← isOutputLike discr do return none
  match ← Lean.Meta.reduceMatcher? unfolded with
  | .reduced reduced => return some reduced
  | _ => return none

meta partial def reduceMarkers (markers : Array Name) (e : Expr) (fuel : Nat := 20) :
    MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    match ← reduceMarker? markers e with
    | some e' => reduceMarkers markers e' fuel
    | none => return e

meta def slMarkers : Array Name := #[``Aeneas.Std.WP.uncurry', ``Aeneas.Std.uncurry]

meta def localHypotheses : TacticM (Std.HashSet FVarId) := do
  (← getMainGoal).withContext do
    pure <| (← getLCtx).foldl (init := ∅) fun acc decl => acc.insert decl.fvarId

private meta partial def normalizeAssertion (e : Expr) : MetaM Expr := do
  let e ← reduceMarkers slMarkers e
  if e.isAppOfArity ``sep 2 then
    let left ← normalizeAssertion e.appFn!.appArg!
    let right ← normalizeAssertion e.appArg!
    return mkApp2 (mkConst ``sep) left right
  if e.isAppOfArity ``ipure 1 then
    return mkApp (mkConst ``ipure) (← reduceMarkers slMarkers e.appArg!)
  return e

private meta def normalizePost (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  let .forallE name domain _ binfo := ← whnf (← inferType e) | return e
  withLocalDecl name binfo domain fun value => do
    mkLambdaFVars #[value] (← normalizeAssertion (mkApp e value))

private meta partial def normalizeRamified (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  let args := e.getAppArgs
  if e.isAppOfArity ``postWand 3 then
    return mkApp3 e.getAppFn args[0]! (← normalizePost args[1]!) (← normalizePost args[2]!)
  if e.isAppOfArity ``sep 2 then
    return mkApp2 e.getAppFn args[0]! (← normalizeRamified args[1]!)
  return e

private meta def normalizeGoal : TacticM Unit := do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  let newTarget ←
    if target.isAppOfArity ``ispec 4 || target.isAppOfArity ``dispec 4 then
      pure (mkAppN target.getAppFn (args.set! 1 (← normalizeAssertion args[1]!)))
    else if target.isAppOfArity ``Entails 2 then
      pure (mkApp2 target.getAppFn args[0]! (← normalizeRamified args[1]!))
    else pure target
  if newTarget != target then
    replaceMainGoal [← goal.change newTarget]

/-- `isimp only` on an entailment; `normalizeSep` on other goals. -/
private meta def simplifySpatialGoal : TacticM Unit := do
  unless (← getUnsolvedGoals).isEmpty do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    let spatial := target.isAppOfArity ``Entails 2 || target.isAppOfArity ``postEntails 3
    discard <| commitWhen do
      if spatial then evalTactic (← `(tactic| isimp only)) else Normalize.normalizeSep
      let goals ← getUnsolvedGoals
      return !(goals.length > 1 || (← goals.anyM fun goal =>
        goal.withContext do return !(← isProp (← goal.getType))))

/-- `@ispec α P m Q` (resp. `@dispec`) as the entailment it unfolds to, `P ⊢ @iwp α true m Q`
(resp. `false`). -/
meta def unfoldSpec? (target : Expr) : Option Expr := do
  let target := target.consumeMData
  let .const name us := target.getAppFn | none
  let total ← if name == ``ispec then some (mkConst ``Bool.true)
    else if name == ``dispec then some (mkConst ``Bool.false) else none
  let #[α, P, m, Q] := target.getAppArgs | none
  return mkApp2 (mkConst ``Entails) P (mkApp4 (mkConst ``iwp us) α total m Q)

/-- The inverse of `unfoldSpec?`. -/
meta def foldSpec? (target : Expr) : Option Expr := do
  let target := target.consumeMData
  guard (target.isAppOfArity ``Entails 2)
  let wp := target.appArg!.consumeMData
  let .const ``iwp us := wp.getAppFn | none
  let #[α, total, m, Q] := wp.getAppArgs | none
  let name ← if total.isConstOf ``Bool.true then some ``ispec
    else if total.isConstOf ``Bool.false then some ``dispec else none
  return mkApp4 (mkConst name us) α target.appFn!.appArg! m Q

end Intro

/-- Run `tac` on `P ⊢ iwp b m Q`, the entailment behind the `ispec`/`dispec` main goal, then fold
back each goal `tac` leaves of the shape `P' ⊢ iwp b m Q'`. -/
meta def onSpecEntailment (tac : TacticM Unit) : TacticM Unit := Tactic.focus do
  let goal ← getMainGoal
  let some entailment := Intro.unfoldSpec? (← instantiateMVars (← goal.getType))
    | throwError "iwp: expected an `ispec`/`dispec` goal, got{indentExpr (← goal.getType)}"
  replaceMainGoal [← goal.replaceTargetDefEq entailment]
  tac
  setGoals (← (← getUnsolvedGoals).mapM fun goal => do
    match Intro.foldSpec? (← instantiateMVars (← goal.getType)) with
    | some spec => goal.replaceTargetDefEq spec
    | none => pure goal)

/-- The tactic `step` runs on the goals it prepares for `ispec` and `dispec`. -/
meta def introIspec : TacticM Unit := do
  withMainContext do
    replaceMainGoal [(← (← getMainGoal).intros).2]
    withMainContext do
    Intro.normalizeGoal
    if (Intro.unfoldSpec? (← instantiateMVars (← getMainTarget))).isSome then
      onSpecEntailment pullShallowPost
    else pullShallowPost
    unless (← getUnsolvedGoals).isEmpty do
      withMainContext do
      let _ ← Aeneas.Simp.simpAt true
        { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
        { addSimpThms :=
            #[``sep_emp_l_eq, ``sep_emp_r_eq, ``ipure_true_eq_emp,
              ``entails_emp_ipure_iff, ``entails_refl,
              ``ispec_ipure_iff, ``dispec_ipure_iff, ``uncurry'_pair,
              ``and_imp, ``exists_imp, ``forall_unit, ``true_imp_iff] }
        (.targets #[] true)
    Intro.simplifySpatialGoal

elab (name := intro_ispec) "intro_ispec" : tactic => introIspec

/-- `iwp => tac`: unfolds `ispec`/`dispec` goals to the underlying entailment `P ⊢ iwp b m Q`,
                  runs `tac`, and then folds back, if possible, to `ispec`/`dispec`.  -/
syntax (name := iwpTac) "iwp" " => " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| iwp => $tac) => onSpecEntailment (evalTactic tac)

end

open Lean Elab Meta Tactic Step in
/-- Goal preparation shared by `ispec` and `dispec`. The bind rule leaves
`∀ v, ispec (Qm v ∗ F) (k v) Q`, whose output pattern comes from `k`; the mono rule leaves
`F ⊢ Qm -∗+ Q`, whose pattern comes from the caller's postcondition `Q`. -/
meta def ispecPrepareIntro : PrepareIntroOutputs := do
  withMainContext do
  let goalTy ← instantiateMVars (← getMainTarget)
  let tree ← if goalTy.consumeMData.isForall then getOutputTree goalTy
    else match goalTy.find? (·.isAppOfArity ``SepLogic.postWand 3) with
      | some wand => getContInput wand.getAppArgs[2]!
      | none => pure (.leaf none)
  let before ← Intro.localHypotheses
  introIspec
  let goal ← match ← getUnsolvedGoals with
    | [] => return 0
    | [goal] => pure goal
    | _ => throwError "ispecPrepareIntro: expected a single goal"
  let introduced ← goal.withContext do
    pure <| (← getLCtx).getFVarIds.filter (!before.contains ·)
  /- Reduce the `match` of a destructuring `let` in the facts (`let (a, b) := p; A ∧ B`), so that
  the conjunctions it hides are split into one hypothesis each. `dsimp` keeps the facts in place,
  so their order, which the names of the call site follow, is unchanged. -/
  let facts ← goal.withContext <| introduced.filterM fun fvar => do isProp (← fvar.getType)
  Aeneas.Simp.dsimpAt true { failIfUnchanged := false } {} (.targets facts false)
  let goal ← match ← getUnsolvedGoals with
    | [] => return 0
    | [goal] => pure goal
    | _ => throwError "ispecPrepareIntro: expected a single goal"
  let (_, goal) ← goal.revert introduced (preserveOrder := true)
  setGoals [goal]
  let goalTy ← instantiateMVars (← goal.getType)
  let .forallE _ domain _ _ := goalTy.consumeMData | return 0
  if ← isProp domain then return 0
  prepareIntroOutputsWith goalTy tree simpOutputEquiv

open Lean Elab Tactic in
/-- Discharge the entailments `step` generates for `ispec` and `dispec`, and the alignment and
non-nullness preconditions of the raw-pointer specifications (`RawPtr.Aligned`,
`RawPtr.NotNull`), which `simp` proves from the hypotheses (e.g. the alignment of the pointers
given by `as_ptr`), or, for `NotNull q n`, from `0 < n`. -/
public meta def ispec_discharge : DischargeTactic := do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let ty := ty.consumeMData
  let isAligned := ty.isAppOf `Aeneas.Std.RawPtr.Aligned
  let isNotNull := ty.isAppOf `Aeneas.Std.RawPtr.NotNull
  if isAligned || isNotNull then
    -- The `Pointee` instances of the specification may not be synthesized yet
    for m in (← Meta.getMVars ty) do
      if (← Meta.isClass? (← m.getType)).isSome then
        if let some inst ← (try Meta.synthInstance? (← m.getType) catch _ => pure none) then
          m.assign inst
    let ty ← instantiateMVars ty
    if ty.hasExprMVar then throwError "ispec_discharge: the pointer is not known yet"
    if isAligned then
      evalTactic (← `(tactic| first | assumption | simp | simp_all))
    else
      evalTactic (← `(tactic| first | assumption | (simp; done) |
        (apply Aeneas.Std.RawPtr.notNull_of_pos; simp_all <;> omega) | simp_all))
  else
    evalTactic (← `(tactic| iframe))

#register_spec_info {
    spec_name := ``Std.WP.ispec
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``Std.WP.ispec_mono
    mk_spec_mono_skip_args := 5
    mk_spec_bind := ``Std.WP.ispec_bind
    mk_spec_bind_skip_args := 7
    prepare_intro_outputs := ``Std.WP.ispecPrepareIntro
    discharge_tactic := some ``Std.WP.ispec_discharge
    to_mvcgen := none
    liftings := #[
      { from_statement := ``Std.WP.spec
        conversion_thm := ``Std.WP.spec_ispec
        conversion_thm_inferred_args := 3 }
    ]
  }

#register_spec_info {
    spec_name := ``Std.WP.dispec
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``Std.WP.dispec_mono
    mk_spec_mono_skip_args := 5
    mk_spec_bind := ``Std.WP.dispec_bind
    mk_spec_bind_skip_args := 7
    prepare_intro_outputs := ``Std.WP.ispecPrepareIntro
    discharge_tactic := some ``Std.WP.ispec_discharge
    to_mvcgen := none
    liftings := #[
      { from_statement := ``Std.WP.ispec
        conversion_thm := ``Std.WP.ispec_dispec
        conversion_thm_inferred_args := 4 },
      { from_statement := ``Std.WP.spec
        conversion_thm := ``Std.WP.spec_dispec
        conversion_thm_inferred_args := 3 },
      { from_statement := ``Std.WP.dspec
        conversion_thm := ``Std.WP.dspec_dispec
        conversion_thm_inferred_args := 3 }
    ]
  }

end Aeneas.Std.WP
