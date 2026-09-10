import Aeneas.Tactic.SepLogic.Frame

/-!
# `iintro` and `isimpl`

Moving the existentials and pure facts of a precondition into the local context,
and the entailment-facing names of `iframe`.

The ispec lemmas these tactics apply (`ispec_exists`, `ispec_ipure`, …) are
resolved by name at elaboration time, so this module does not depend on the
module that defines them.
-/

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

/-- Marker used while `step` introduces a callee postcondition. It keeps
`iintro_shallow` from traversing into the inferred frame. -/
def introFrame (F : IProp) : IProp := F

theorem introFrame_eq (F : IProp) : introFrame F = F := by
  rfl

/-- Find a directly exposed pure assertion in a separating-conjunction tree and
return its proposition together with the tree with that assertion removed.
Opaque representation predicates are not unfolded. -/
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

/-- One step of `iintro`: peel a quantifier or a pure fact off the precondition
of a total or partial ispec. Fails when the precondition is purely spatial.

The precondition is unfolded (`wellFormed`, `isList`, …) only as far as needed to
expose its head connective: applying `ispec_exists` or `ispec_ipure` blindly
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
  let isISpec := fn.isConstOf `Aeneas.SepLogic.ispec
  let isDispec := fn.isConstOf `Aeneas.SepLogic.dispec
  unless (isISpec || isDispec) && args.size = 4 do
    throwError "iintro_step: the goal is not a separation-logic ispec"
  let precondition ← IFrame.exposeConnective args[1]!
  let head := precondition.consumeMData.getAppFn
  let leadingPure ←
    if precondition.consumeMData.isAppOfArity ``sep 2 then
      pure ((← IFrame.exposeConnective precondition.consumeMData.appFn!.appArg!)
        |>.consumeMData.isAppOfArity ``ipure 1)
    else pure false
  let specName :=
    if isDispec then `Aeneas.SepLogic.dispec
    else `Aeneas.SepLogic.ispec
  let goal ← goal.change
    (← mkAppOptM specName #[args[0]!, precondition, args[2]!, args[3]!])
  if head.isConstOf ``iexists then
    let lemmaName :=
      if isDispec then `Aeneas.SepLogic.dispec_exists
      else `Aeneas.SepLogic.ispec_exists
    replaceMainGoal (← goal.apply (← mkConstWithFreshMVarLevels lemmaName))
  else if head.isConstOf ``ipure then
    let lemmaName :=
      if isDispec then `Aeneas.SepLogic.dispec_ipure'
      else `Aeneas.SepLogic.ispec_ipure'
    replaceMainGoal (← goal.apply (← mkConstWithFreshMVarLevels lemmaName))
  else if leadingPure then
    let lemmaName :=
      if isDispec then `Aeneas.SepLogic.dispec_ipure
      else `Aeneas.SepLogic.ispec_ipure
    replaceMainGoal (← goal.apply (← mkConstWithFreshMVarLevels lemmaName))
  else if let some (proposition, rest) := extractPure? precondition then
    let lemmaName :=
      if isDispec then `Aeneas.SepLogic.dispec_ipure_anywhere
      else `Aeneas.SepLogic.ispec_ipure_anywhere
    let normalized := mkApp2 (mkConst ``sep)
      (mkApp (mkConst ``ipure) proposition) rest
    let hExtract ← IFrame.proveEqAC precondition normalized
    let thm := mkAppN (← mkConstWithFreshMVarLevels lemmaName)
      #[args[0]!, proposition, rest, precondition, args[2]!, args[3]!, hExtract]
    replaceMainGoal (← goal.apply thm)
  else
    throwError "iintro_step: the precondition has no quantifier or pure fact \
      left to extract:\n{precondition}"

/-- Move the existentials and pure facts of a ispec's precondition into the
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
private partial def isPullable (pre : Expr) : Bool :=
  let pre := pre.consumeMData
  if pre.isAppOfArity ``iexists 2 || pre.isAppOfArity ``ipure 1 then true
  else if pre.isAppOfArity ``sep 2 then
    isPullable pre.appFn!.appArg! || isPullable pre.appArg!
  else false

private partial def pullPrecondition (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless (target.isAppOfArity `Aeneas.SepLogic.ispec 4 ||
      target.isAppOfArity `Aeneas.SepLogic.dispec 4) &&
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

/-- Run `iintro_shallow` on the left side of the top-level separating
conjunction while treating its right side as an opaque frame. This is the
variant used by `step` on continuation ispecs of the shape `Qm value ∗ F`. -/
elab "iintro_shallow_post" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let isISpec := target.isAppOfArity `Aeneas.SepLogic.ispec 4
  let isDispec := target.isAppOfArity `Aeneas.SepLogic.dispec 4
  unless isISpec || isDispec do
    evalTactic (← `(tactic| isimp))
    return
  let args := target.getAppArgs
  let precondition := args[1]!.consumeMData
  unless precondition.isAppOfArity ``sep 2 do
    evalTactic (← `(tactic| (isimp; iintro_shallow)))
    return
  let preArgs := precondition.getAppArgs
  let lemmaName :=
    if isDispec then `Aeneas.SepLogic.dispec_introFrame
    else `Aeneas.SepLogic.ispec_introFrame
  let thm := mkApp3 (← mkConstWithFreshMVarLevels lemmaName)
    args[0]! preArgs[0]! preArgs[1]!
  replaceMainGoal (← goal.apply thm)
  evalTactic (← `(tactic| (isimp; iintro_shallow)))
  unless (← getUnsolvedGoals).isEmpty do
    evalTactic (← `(tactic| (simp only [introFrame_eq]; isimp)))

/-- One step of `iintro_keep`: copy the leading pure fact of the precondition of
a ispec into the local context, *without* removing it from the precondition.

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
  unless fn.isConstOf `Aeneas.SepLogic.ispec && args.size = 4 do
    throwError "iintro_keep_step: the goal is not a separation-logic ispec"
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
    (← mkAppOptM `Aeneas.SepLogic.ispec #[args[0]!, exposed, args[2]!, args[3]!])
  let [next] ← goal.apply
    (← mkConstWithFreshMVarLevels `Aeneas.SepLogic.ispec_ipure_keep)
    | throwError "iintro_keep_step: unexpected number of goals"
  let (_, next) ← next.intro1P
  /- Put the precondition back in its original, folded form: only the local
     context should record that the step happened. -/
  replaceMainGoal
    [← next.change
      (← mkAppOptM `Aeneas.SepLogic.ispec #[args[0]!, args[1]!, args[2]!, args[3]!])]

/-- Copy the pure facts of the precondition of a ispec into the local context,
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
