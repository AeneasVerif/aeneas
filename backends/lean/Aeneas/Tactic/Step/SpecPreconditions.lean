module
public import Aeneas.Tactic.Step.Step
public section
open Lean Meta Elab Tactic

/-!
# Preconditions which are specifications

E.g. `harea : ∀ x, f x ≤ U32.max → inst.area x ⦃ a => a.val = f x ⦄`, with `f` a ghost variable.
The discharge tactic proves it by stepping through `inst.area`, then instantiates `f` from the
postcondition. The ghosts are frozen while stepping, so that intermediate preconditions can't
instantiate them wrongly.
-/

namespace Aeneas.Step

/-- Simplify the target with `global_simps`, `WP.spec_ok` and the hypotheses without
meta-variables (rewriting with a ghost could instantiate it wrongly). -/
syntax (name := simpGroundHyps) "simp_ground_hyps" : tactic

@[tactic simpGroundHyps]
meta def evalSimpGroundHyps : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let mut thms : SimpTheorems := {}
  if let some ext ← getSimpExtension? `global_simps then
    thms ← ext.getTheorems
  thms ← thms.addConst ``Aeneas.Std.WP.spec_ok
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (← isProp ty) && !ty.hasExprMVar then
      thms ← thms.add (.fvar d.fvarId) #[] d.toExpr
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simpGoal g ctx (fvarIdsToSimp := #[])
  match r with
  | none => replaceMainGoal []
  | some (_, g') => replaceMainGoal [g']

/-- Close the goals mentioning ghosts, instantiating them: first those whose target mentions them
(the postcondition), then those whose hypotheses do. Other goals are kept. -/
syntax (name := closeGhostGoals) "close_ghost_goals" : tactic

@[tactic closeGhostGoals]
meta def evalCloseGhostGoals : Tactic := fun _ => do
  let closeWith (pred : MVarId → MetaM Bool) (tac : TacticM Unit) : TacticM Unit := do
    let mut rest : Array MVarId := #[]
    for g in ← getGoals do
      if ← g.isAssigned then continue
      if ← pred g then
        setGoals [g]
        try tac catch _ => pure ()
        rest := rest ++ (← getGoals).toArray
      else rest := rest.push g
    setGoals rest.toList
  let targetHasMVars (g : MVarId) : MetaM Bool := do
    return (← instantiateMVars (← g.getType)).hasExprMVar
  let ctxHasMVars (g : MVarId) : MetaM Bool := g.withContext do
    for d in ← getLCtx do
      if (← instantiateMVars d.type).hasExprMVar then return true
    return false
  closeWith targetHasMVars <| evalTactic (← `(tactic| first
    | assumption
    | (simp_ground_hyps; done)
    | (simp_ground_hyps; rfl)
    | rfl))
  closeWith ctxHasMVars <| evalTactic (← `(tactic| assumption))

/-- Discharge tactic for `Std.WP.spec` theorems. Fails at once on other preconditions. -/
public meta def specPreconditionDischarge : DischargeTactic := do
  unless (← getOptions).getBool `aeneas.step.specPreconditions true do
    throwError "disabled (option `aeneas.step.specPreconditions`)"
  let g ← getMainGoal
  -- An unknown postcondition is inferred by `step*` instead
  let some spec ← g.withContext do specUnderBinders? (← instantiateMVars (← g.getType))
    | throwError "not a specification"
  unless spec.name == ``Std.WP.spec && !spec.postUnknown do
    throwError "not a specification with a known post-condition"
  -- The precondition may already be a hypothesis
  try evalTactic (← `(tactic| assumption)); return
  catch _ => pure ()
  -- Prove a copy, to mark the proof for `step*?`
  let copy ← g.withContext do mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
  setGoals [copy.mvarId!]
  let ghosts ← getMVars (← instantiateMVars (← g.getType))
  let ghosts ← ghosts.filterM fun m => return (← m.getKind).isNatural
  for m in ghosts do m.setKind .syntheticOpaque
  try
    -- `step_simps` also unfolds methods without calls (e.g. `ok 0#u32`)
    evalTactic (← `(tactic| (intros; try simp only [step_simps]; repeat' step)))
  finally
    for m in ghosts do m.setKind .natural
  evalTactic (← `(tactic| (
    close_ghost_goals
    all_goals (first
      | scalar_tac
      | agrind
      | (simp only [global_simps] at *; scalar_tac)
      | simp_all))))
  unless (← getUnsolvedGoals).isEmpty do throwError "could not prove the precondition"
  g.assign (.mdata (KVMap.empty.insert specPreconditionKey (.ofBool true)) copy)

end Aeneas.Step

/- `Std.WP.spec` is registered before `step` exists: add the discharge tactic now. -/
open Lean Elab Command in
run_cmd do
  let some info ← liftTermElabM (Aeneas.specInfoLookup ``Aeneas.Std.WP.spec)
    | throwError "`Aeneas.Std.WP.spec` is not registered"
  Aeneas.specAttr.add { info with discharge_tactic := some ``Aeneas.Step.specPreconditionDischarge }
