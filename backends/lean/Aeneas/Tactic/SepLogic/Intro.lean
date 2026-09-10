import Aeneas.Tactic.SepLogic.Frame

/-!
# `iintro` and `isimpl`

Moving the existentials and pure facts of a precondition into the local context,
and the entailment-facing names of `iframe`.
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

/-- Copy a pure fact from an entailment's source into the local context without
removing it from the source. -/
theorem entails_pure_keep {P : Prop} {H H' H₀ : IProp}
    (hExtract : H₀ ⊢ ⌜P⌝ ∗ H) (h : P → H₀ ⊢ H') : H₀ ⊢ H' := by
  intro heap hH₀
  have ⟨hP, _⟩ := (sep_pure_l P H heap).mp (hExtract heap hH₀)
  exact h hP heap hH₀

/-- One step of `iintro`: peel a quantifier or a pure fact off the precondition
of an entailment. Fails when the precondition is purely spatial.

The precondition is unfolded (`wellFormed`, `isList`, …) only as far as needed to
expose its head connective; this avoids peeling a quantifier of the underlying
heap model instead. -/
elab "iintro_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← IFrame.exposeEntailment? target
    | throwError "iintro_step: the goal is not a separation-logic entailment"
  let args := entailment.getAppArgs
  let source := args[0]!
  let destination := args[1]!
  /- Float the existentials out of the separating conjunctions and drop the
     `emp`s left behind by previous steps, so that the head connective of the
     precondition is the one we want to peel. -/
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

/-- Move the existentials and pure facts of an entailment's precondition into the
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
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← IFrame.exposeEntailment? target | return goal
  unless isPullable entailment.getAppArgs[0]! do return goal
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
variant used by `step` on continuation preconditions of the shape
`Qm value ∗ F`. -/
elab "iintro_shallow_post" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← IFrame.exposeEntailment? target
    | evalTactic (← `(tactic| isimp))
      return
  let args := entailment.getAppArgs
  let source := args[0]!.consumeMData
  unless source.isAppOfArity ``sep 2 do
    evalTactic (← `(tactic| (isimp; iintro_shallow)))
    return
  let sourceArgs := source.getAppArgs
  let markedSource := mkApp2 (mkConst ``sep) sourceArgs[0]!
    (mkApp (mkConst ``introFrame) sourceArgs[1]!)
  let markedTarget ← IFrame.mkEntailmentLike target args[0]! args[1]! markedSource
  let goal ← goal.change markedTarget
  replaceMainGoal [goal]
  evalTactic (← `(tactic| (isimp; iintro_shallow)))
  unless (← getUnsolvedGoals).isEmpty do
    evalTactic (← `(tactic| (simp only [introFrame_eq]; isimp)))

/-- One step of `iintro_keep`: copy the leading pure fact of an entailment's
precondition into the local context, *without* removing it from the
precondition.

`iintro_step` consumes the fact, but that is often the wrong thing here: the
assertion has to keep it for the framing of later steps. Copying is always
sound, and it is what makes a term mentioned by a callee's precondition
reducible to the one the assertion owns.

Fails when the fact is already in the context, so that `repeat` terminates. -/
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

/-- Copy the pure facts of an entailment's precondition into the local context,
leaving the precondition untouched. See `iintro_keep_step`. -/
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
