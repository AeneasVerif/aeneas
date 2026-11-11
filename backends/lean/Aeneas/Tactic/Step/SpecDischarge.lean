module
public import Aeneas.Tactic.Step.Step
public section
open Lean Meta Elab Tactic

/-!
# Preconditions which are specifications

A specification theorem may take as precondition a specification of another program, typically
of a method of a trait instance:
```lean
theorem Shape.double_area.default_spec (inst : Shape Self) (f : Self → Nat)
    (harea : ∀ x, f x ≤ U32.max → inst.area x ⦃ a => a.val = f x ⦄) (x : Self)
    (h : 2 * f x ≤ U32.max) :
    Shape.double_area.default inst x ⦃ r => r.val = 2 * f x ⦄
```
When `step` applies such a theorem to a concrete instance, `f` is a ghost variable: nothing in the
call determines it. The discharge tactic below proves the precondition `harea` by stepping through
the instance's `area` (recursively: the inner `step`s use the same discharge tactic), and
instantiates `f` from the post-conditions it obtains. This lets the specification theorems of a
library (for instance of the default methods of its traits, or of its generic functions) be used
with the instances defined by its users, with `step*` alone.

The ghost variables are *frozen* while stepping through the program: otherwise an intermediate
precondition (e.g. `x.side * x.side ≤ U32.max`) could instantiate them by matching a hypothesis
(e.g. `f x ≤ U32.max`) too early, and wrongly. They are then instantiated by closing the goals
whose target mentions them (the post-condition) first.
-/

namespace Aeneas.Step

/-- Simplify the target with `global_simps`, `WP.spec_ok` and the hypotheses which do not mention
meta-variables. Hypotheses which mention a ghost variable (e.g. `?f x ≤ U32.max`) are excluded:
used as rewrite rules, they could instantiate it wrongly. -/
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

/-- Close the goals which mention meta-variables (ghost variables of an enclosing specification),
instantiating them:
- first the goals whose target mentions them (the post-condition), by unifying the target with a
  hypothesis, or by rewriting with the hypotheses then unifying;
- then the goals whose hypotheses mention them (a ghost variable which only constrains the
  preconditions), by unifying a hypothesis with the target.

The other goals are kept. -/
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

/-- The discharge tactic for the preconditions of `Std.WP.spec` theorems (see the module
documentation). It fails immediately on a precondition which is not a specification, so that
`step` then proceeds as usual. -/
public meta def specPreconditionDischarge : DischargeTactic := do
  -- Disabled by `step -specPreconditions` or `set_option aeneas.step.specPreconditions false`
  unless (← getOptions).getBool `aeneas.step.specPreconditions true do
    throwError "disabled (option `aeneas.step.specPreconditions`)"
  let g ← getMainGoal
  /- An unknown post-condition is inferred by `step*` (`processPreconditions`) instead -/
  let spec? ← g.withContext do getSpecUnderBinders? (← instantiateMVars (← g.getType))
  unless spec? == some (``Std.WP.spec, false) do
    throwError "not a specification with a known post-condition"
  -- The precondition may already be a hypothesis
  try evalTactic (← `(tactic| assumption)); return
  catch _ => pure ()
  /- Prove a copy of the precondition, so that we can mark the proof (for `step*?`) -/
  let copy ← g.withContext do mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
  setGoals [copy.mvarId!]
  -- Freeze the ghost variables while stepping through the program
  let ghosts ← getMVars (← instantiateMVars (← g.getType))
  let ghosts ← ghosts.filterM fun m => return (← m.getKind).isNatural
  for m in ghosts do m.setKind .syntheticOpaque
  try
    evalTactic (← `(tactic| (intros; try simp only; repeat' step)))
  finally
    for m in ghosts do m.setKind .natural
  -- Instantiate the ghost variables, then close the remaining goals
  evalTactic (← `(tactic| (
    close_ghost_goals
    all_goals (first
      | scalar_tac
      | agrind
      | (simp only [global_simps] at *; scalar_tac)
      | simp_all))))
  unless (← getUnsolvedGoals).isEmpty do throwError "could not prove the precondition"
  g.assign (.mdata (KVMap.empty.insert specDischargeKey (.ofBool true)) copy)

end Aeneas.Step

/- Register the discharge tactic for `Std.WP.spec`, by updating its registration (made in
`Aeneas.Tactic.Step.SpecInfo`, before `step` is defined, which the discharge tactic needs). -/
open Lean Elab Command in
run_cmd do
  let some info ← liftTermElabM (Aeneas.specInfoLookup ``Aeneas.Std.WP.spec)
    | throwError "`Aeneas.Std.WP.spec` is not registered"
  Aeneas.specAttr.add { info with discharge_tactic := some ``Aeneas.Step.specPreconditionDischarge }
