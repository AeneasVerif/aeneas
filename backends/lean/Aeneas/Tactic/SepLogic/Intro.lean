import Aeneas.Tactic.SepLogic.Frame

/-!
# `iintro` and `isimpl`

Moving the existentials and pure facts of a precondition into the local context,
and the entailment-facing names of `iframe`.

The triple lemmas these tactics apply (`triple_exists`, `triple_ipure`, …) are
resolved by name at elaboration time, so this module does not depend on the
module that defines them.
-/

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

/-- One step of `iintro`: peel a quantifier or a pure fact off the precondition
of a triple.  Fails when the precondition is purely spatial.

The precondition is unfolded (`wellFormed`, `isList`, …) only as far as needed to
expose its head connective: applying `triple_exists` or `triple_ipure` blindly
would let the unifier see through `sep`/`ipure` down to the raw heap predicate
and peel a quantifier of the *model* instead. -/
elab "iintro_step" : tactic => withMainContext do
  /- Float the existentials out of the separating conjunctions and drop the
     `emp`s left behind by previous steps, so that the head connective of the
     precondition is the one we want to peel. -/
  let _ ← Aeneas.Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { addSimpThms :=
        #[``sep_exists_l_eq, ``sep_exists_r_eq,
          ``sep_emp_l_eq, ``sep_emp_r_eq] }
    (.targets #[] true)
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf `Aeneas.SepLogic.triple && args.size = 4 do
    throwError "iintro_step: the goal is not a separation-logic triple"
  let precondition ← IFrame.exposeConnective args[1]!
  let head := precondition.consumeMData.getAppFn
  let leadingPure ←
    if precondition.consumeMData.isAppOfArity ``sep 2 then
      pure ((← IFrame.exposeConnective precondition.consumeMData.appFn!.appArg!)
        |>.consumeMData.isAppOfArity ``ipure 1)
    else pure false
  let lemmaName ←
    if head.isConstOf ``iexists then pure `Aeneas.SepLogic.triple_exists
    else if head.isConstOf ``ipure then pure `Aeneas.SepLogic.triple_ipure'
    else if leadingPure then pure `Aeneas.SepLogic.triple_ipure
    else
      throwError "iintro_step: the precondition has no quantifier or pure fact \
        left to extract:\n{precondition}"
  let goal ← goal.change
    (← mkAppOptM `Aeneas.SepLogic.triple #[args[0]!, precondition, args[2]!, args[3]!])
  replaceMainGoal (← goal.apply (← mkConstWithFreshMVarLevels lemmaName))

/-- Move the existentials and pure facts of a triple's precondition into the
local context.

`iintro` peels as many of them as it can, using inaccessible names.
`iintro p₁ ... pₙ` peels exactly `n` of them, destructuring the `i`-th one with
the `rintro` pattern `pᵢ`, e.g. `iintro l rfl` or `iintro ⟨hhead, htail⟩`.

Pure facts are *removed* from the precondition, which is often not what a
subsequent `step` needs; use `iintro_keep` when only the local hypothesis is
wanted. -/
syntax (name := iIntro) "iintro" (ppSpace colGt rintroPat)* : tactic

macro_rules
  | `(tactic| iintro $ps:rintroPat*) => do
    if ps.isEmpty then
      `(tactic| repeat (iintro_step; rintro _))
    else
      let steps ← ps.mapM fun p => `(tactic| (iintro_step; rintro $p:rintroPat))
      `(tactic| ($[$steps]*))

/-- Whether a quantifier or a pure fact can be peeled off `pre` without unfolding it: an opened
representation predicate is one the frame inference of a later `step` can no longer match. -/
private def isPullable (pre : Expr) : Bool :=
  let pre := pre.consumeMData
  if pre.isAppOfArity ``iexists 2 || pre.isAppOfArity ``ipure 1 then true
  else if pre.isAppOfArity ``sep 2 then
    pre.appFn!.appArg!.consumeMData.isAppOfArity ``ipure 1
  else false

private partial def pullPrecondition (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity `Aeneas.SepLogic.triple 4 &&
      isPullable target.getAppArgs[1]! do return goal
  setGoals [goal]
  let state ← saveState
  try
    evalTactic (← `(tactic| iintro_step))
  catch _ =>
    state.restore
    return goal
  let (_, goal) ← (← getMainGoal).intro1P
  pullPrecondition goal

/-- `iintro` restricted to what the precondition exposes without being unfolded; see
`isPullable`. -/
elab "iintro_shallow" : tactic => withMainContext do
  setGoals [← pullPrecondition (← getMainGoal)]

/-- One step of `iintro_keep`: copy the leading pure fact of the precondition of
a triple into the local context, *without* removing it from the precondition.

`iintro_step` consumes the fact, but that is often the wrong thing here: the
assertion has to keep it for the framing of the later
steps (this is why `iintro` before a `step` can turn a working proof into a
failing one).  Copying is always sound, and it is what makes the pointer of a
callee's precondition (`s.head.get!`, say) reducible to the one the assertion
owns.

Fails when the fact is already in the context, so that `repeat` terminates. -/
elab "iintro_keep_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf `Aeneas.SepLogic.triple && args.size = 4 do
    throwError "iintro_keep_step: the goal is not a separation-logic triple"
  let precondition ← IFrame.exposeConnective args[1]!
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
  let goal ← goal.change
    (← mkAppOptM `Aeneas.SepLogic.triple #[args[0]!, exposed, args[2]!, args[3]!])
  let [next] ← goal.apply
    (← mkConstWithFreshMVarLevels `Aeneas.SepLogic.triple_ipure_keep)
    | throwError "iintro_keep_step: unexpected number of goals"
  let (_, next) ← next.intro1P
  /- Put the precondition back in its original, folded form: only the local
     context should record that the step happened. -/
  replaceMainGoal
    [← next.change
      (← mkAppOptM `Aeneas.SepLogic.triple #[args[0]!, args[1]!, args[2]!, args[3]!])]

/-- Copy the pure facts of the precondition of a triple into the local context,
leaving the precondition untouched.  See `iintro_keep_step`. -/
macro "iintro_keep" : tactic => `(tactic| repeat (iintro_keep_step; rename_i _))

/-- `iframe` under the name used for entailment simplification. -/
syntax "isimpl" (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| isimpl) => `(tactic| iframe)
  | `(tactic| isimpl by $tac) => `(tactic| iframe by $tac)

/-- On an entailment `H₁ ⊢ H₂` or `Q₁ ⊢+ Q₂`, introduce the existentials of
the left-hand side and move its pure facts into the local context, leaving the
right-hand side alone.

Use it when the witness the right-hand side needs depends on a variable bound on
the left: `isimpl` would otherwise pick the metavariable for the right-hand
side *before* that variable exists. -/
elab "iintro_entail" : tactic => Tactic.focus do withMainContext do
  replaceMainGoal [← IFrame.pullGoal (← getMainGoal)]

end Aeneas.SepLogic
