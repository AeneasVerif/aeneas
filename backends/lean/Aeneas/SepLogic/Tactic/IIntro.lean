module
public import Aeneas.SepLogic.Tactic.IFrame
public meta import Lean
public meta import AeneasMeta.Simp
public section

namespace Aeneas.SepLogic

theorem entails_pure_keep {P : Prop} {H H' H₀ : IProp}
    (hExtract : H₀ ⊢ ⌜P⌝ ∗ H) (h : P → H₀ ⊢ H') : H₀ ⊢ H' := by
  intro heap hH₀
  have ⟨hP, _⟩ := (sep_pure_l P H heap).mp (hExtract heap hH₀)
  exact h hP heap hH₀

end Aeneas.SepLogic

end

public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Normalize

/-- Move the existentials and pure facts of an entailment's precondition into the context,
leaving the rest of the precondition as it is. The existentials come first, wherever they are
(an `∃` is opened before any pure fact, even one to its left), then the pure facts, from left to
right. Without patterns, moves all of them, with inaccessible names; with patterns, moves one for
each pattern. -/
syntax (name := iIntro) "iintro" (ppSpace colGt rintroPat)* : tactic

elab_rules : tactic
  | `(tactic| iintro $ps:rintroPat*) => withMainContext do
    let limit := if ps.isEmpty then none else some ps.size
    let (goal, new) ← pullLeftFVars (← getMainGoal) (limit := limit)
    if ps.isEmpty then
      replaceMainGoal [goal]
      return
    if new.size < ps.size then
      throwError "iintro: the precondition has only {new.size} quantifiers or pure facts to \
        extract, for {ps.size} patterns"
    let (_, goal) ← goal.revert new
    replaceMainGoal [goal]
    evalTactic (← `(tactic| rintro $ps:rintroPat*))

/-- `iintro`, but without unfolding definitions (so that the predicates a later `step` must match
are never opened), and naming the facts `h`. -/
elab "iintro_shallow" : tactic => withMainContext do
  replaceMainGoal [← pullLeft (← getMainGoal) (unfold := false) (names := true)]

/-- `iintro_shallow` after `step`: the frame it inferred, the right operand of the precondition,
is left untouched. Then normalizes the assertions. -/
elab "iintro_shallow_post" : tactic => withMainContext do
  let goal ← getMainGoal
  if let some entailment ← exposeEntailment? (← instantiateMVars (← goal.getType)) then
    let source := (← reducePostApplication entailment.appFn!.appArg!).consumeMData
    let frame ← if source.isAppOfArity ``sep 2 then
        pure (some (← reducePostApplication source.appArg!).consumeMData)
      else pure none
    replaceMainGoal [← pullLeft goal (unfold := false) (frame := frame) (names := true)]
  normalizeSep

/-- The proof of `source ⊢ destination` from `next : P₁ → … → Pₖ → source ⊢ destination`, given
for each `Pᵢ` the rest `Tᵢ` and `extractᵢ : source ⊢ ⌜Pᵢ⌝ ∗ Tᵢ`. -/
private def keepPures (source destination next : Expr) (hyps : Array Expr) :
    List (Expr × Expr × Expr) → MetaM Expr
  | [] => return mkAppN next hyps
  | (P, T, extract) :: more => do
    let body ← withLocalDeclD (← mkFreshUserName `h) P fun h => do
      mkLambdaFVars #[h] (← keepPures source destination next (hyps.push h) more)
    return mkAppN (mkConst ``entails_pure_keep) #[P, T, destination, source, extract, body]

/-- Copy the pure facts of the precondition that are not in the context yet into the context,
without consuming them. -/
elab "iintro_keep" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some entailment ← exposeEntailment? target
    | throwError "iintro_keep: the goal is not a separation-logic entailment"
  let source := entailment.appFn!.appArg!
  let destination := entailment.appArg!
  let lctx ← getLCtx
  let known (proposition : Expr) (hyp : Expr) : MetaM Bool :=
    withNewMCtxDepth (withReducible (isDefEq hyp proposition))
  -- also skip the copies of a fact selected earlier in the precondition
  let selected ← IO.mkRef (#[] : Array Expr)
  let select (proposition : Expr) : MetaM Bool := do
    if ← lctx.anyM fun decl => pure !decl.isImplementationDetail <&&> known proposition decl.type
    then return false
    if ← (← selected.get).anyM (known proposition) then return false
    selected.modify (·.push proposition)
    return true
  let some (props, _, eq) ← splitPures (← exposeConnective source) (select := select)
    | return
  -- `reordered = A₁ ∗ T₁` and `Tᵢ = Aᵢ₊₁ ∗ Tᵢ₊₁`, where `Aᵢ` unfolds to `⌜Pᵢ⌝`
  let reordered := (← inferType eq).appArg!
  let mut extract := mkApp3 (mkConst ``entails_of_eq) source reordered eq
  let mut current := reordered
  let mut steps := #[]
  for P in props do
    let atom := current.appFn!.appArg!
    let rest := current.appArg!
    steps := steps.push (P, rest, extract)
    extract := mkApp5 (mkConst ``entails_trans) source current rest extract
      (mkApp2 (mkConst ``sep_elim_left) rest atom)
    current := rest
  let newType ← props.foldrM (init := target)
    fun P acc => return mkForall (← mkFreshUserName `h) .default P acc
  let next ← mkFreshExprSyntheticOpaqueMVar newType
  goal.assign (← keepPures source destination next #[] steps.toList)
  replaceMainGoal [(← next.mvarId!.introNP props.size).2]

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
