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
/-- Discharge the entailments `step` generates for `ispec` and `dispec`. -/
public meta def ispec_discharge : DischargeTactic := do
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
