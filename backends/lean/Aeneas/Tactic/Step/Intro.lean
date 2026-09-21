import Lean
import AeneasMeta.Utils

/-!
# The shared part of an `intro_tactic`

`step` hands the mono/bind premise left by a step theorem to the tactic the specification
statement registers as its `intro_tactic`, which has to bring it to the
`∀ outputs, facts → …` shape `step` introduces the outputs from.

What the judgments have in common there is the treatment of the facts: the markers the
postcondition notation leaves behind have to be reduced, and a fact standing for several
of them has to be split. `intro_split` does exactly that and nothing else, which is all a
judgment whose premise already *is* `∀ x, P x → …` needs; a separation-logic judgment
extracts its facts from an assertion first, and then reuses these same helpers.
-/

namespace Aeneas.Step.Intro

open Lean Meta Elab Tactic

theorem forall_unit {p : Prop} : (Unit → p) ↔ p :=
  ⟨fun h => h (), fun h _ => h⟩

/-- Record the output binder index. -/
def markOutputIndex (goal : MVarId) (index : Nat) : MetaM MVarId := do
  if index == 0 then return goal
  goal.replaceTargetDefEq
    (.mdata (KVMap.empty.setNat `aeneas.step.outputIndex index) (← goal.getType))

def takeOutputIndex (goal : MVarId) : MetaM (Option Nat × MVarId) := do
  if let .mdata data body := ← goal.getType then
    if let some (.ofNat index) := data.find `aeneas.step.outputIndex then
      let data := data.erase `aeneas.step.outputIndex
      let body := if data.isEmpty then body else mkMData data body
      return (some index, ← goal.replaceTargetDefEq body)
  return (none, goal)

/-- Whether `e` consists only of outputs, projections, and constructors. -/
partial def isOutputLike (e : Expr) : MetaM Bool := do
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

/-- Reduce an application which is stuck on a definition that destructures its argument:
this is the shape of the markers a multi-binder postcondition is built from, which apply
the body of the postcondition to the result tuple.

The definition is unfolded once, and the reduction is kept only when it fires a match with
a *single* alternative, i.e. an irrefutable destructuring. A definition which merely
abbreviates its body is left alone, and so is a genuine case analysis — for a separation
logic, opening a representation predicate would leave an assertion the frame inference can
no longer match. -/
def reduceMarker? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  unless e.getAppFn.isConst && e.getAppNumArgs > 0 do return none
  let some unfolded ← unfoldDefinition? e | return none
  let some matcher ← matchMatcherApp? unfolded | return none
  unless matcher.alts.size == 1 do return none
  /- Do not evaluate program computations or the marker body. -/
  for discr in matcher.discrs do
    unless ← isOutputLike discr do return none
  match ← Lean.Meta.reduceMatcher? unfolded with
  | .reduced reduced => return some reduced
  | _ => return none

/-- Reduce up to `fuel` markers at the head of `e`. -/
partial def reduceMarkers (e : Expr) (fuel : Nat := 16) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    match ← reduceMarker? e with
    | some e' => reduceMarkers e' fuel
    | none => return e

/-- Normalize the type of a fact in place, reducing the markers at its head. -/
def normalizeFact (goal : MVarId) (fvarId : FVarId) : MetaM MVarId := do
  goal.withContext do
    let type ← instantiateMVars (← fvarId.getType)
    let type' ← reduceMarkers type
    if type' == type.consumeMData then pure goal else goal.replaceLocalDeclDefEq fvarId type'

/-- Prove trivial assumptions without evaluating program terms. -/
def trivialProof? (type : Expr) : MetaM (Option Expr) := do
  let type := type.consumeMData
  if type.isConstOf ``True then return some (mkConst ``True.intro)
  if type.isConstOf ``Unit then return some (mkConst ``Unit.unit)
  match_expr type with
  | Eq _ lhs rhs =>
    if lhs == rhs then return some (← mkEqRefl lhs) else return none
  | _ => return none

/-- Normalize defining existentials before splitting facts. -/
def normalizeExists (goal : MVarId) (fvarId : FVarId) : MetaM (MVarId × FVarId) := do
  let goal ← normalizeFact goal fvarId
  goal.withContext do
    let type ← instantiateMVars (← fvarId.getType)
    unless ← isProp type do return (goal, fvarId)
    if (type.find? (·.isAppOfArity ``Exists 2)).isNone then return (goal, fvarId)
    let thms ← #[``exists_eq_left, ``exists_eq_left', ``exists_eq_right, ``exists_eq_right']
      |>.foldlM (fun thms name => thms.addConst name (post := false)) ({} : SimpTheorems)
    let ctx ← Simp.mkContext { iota := false, zeta := false, dsimp := false }
      (simpTheorems := #[thms])
    let pre : Simp.Simproc := fun e => do
      if e.isForall || e.isLambda || e.isLet ||
          e.isAppOf ``And || e.isAppOf ``Or || e.isAppOf ``Exists ||
          e.isAppOf ``ite || e.isAppOf ``dite then
        return ← Simp.preDefault #[] e
      if let .const name _ := e.getAppFn then
        if ← isMatcher name then
          return ← Simp.preDefault #[] e
      return .done { expr := e }
    let (result, _) ← Simp.main type ctx (methods := { Simp.mkDefaultMethodsCore #[] with pre })
    let some proof := result.proof?
      | return (← goal.replaceLocalDeclDefEq fvarId result.expr, fvarId)
    let result ← goal.assertAfter fvarId (← fvarId.getUserName) result.expr
      (← mkEqMP proof (.fvar fvarId))
    return (← result.mvarId.tryClear fvarId, result.fvarId)

/-- Collect conjuncts and discharge vacuous assumptions. -/
partial def collectFacts (type proof : Expr) (name : Name) : MetaM (Array Hypothesis) := do
  let type ← reduceMarkers type
  if type.isConstOf ``True then return #[]
  if let .forallE _ domain body _ := type then
    unless body.hasLooseBVars do
      if let some witness ← trivialProof? domain then
        return ← collectFacts body (mkApp proof witness) name
  match_expr type with
  | And p q =>
    let left ← collectFacts p (mkApp3 (mkConst ``And.left) p q proof) name
    let right ← collectFacts q (mkApp3 (mkConst ``And.right) p q proof) name
    return left ++ right
  | _ => return #[{ userName := name, type, value := proof }]

private def witnessNames : Array AltVarNames := #[{ varNames := [`x] }]

/-- Eliminate existentials without wrapping nondependent continuations in `casesOn`. -/
def elimExists (goal : MVarId) (fvarId : FVarId) : MetaM (Array FVarId × MVarId) :=
  goal.withContext do
    let target ← goal.getType
    if ← exprDependsOn target fvarId then
      let #[subgoal] ← goal.cases fvarId witnessNames |
        throwError "intro_split: expected a single existential constructor"
      return (subgoal.fields.map Expr.fvarId!, subgoal.mvarId)
    let type ← instantiateMVars (← fvarId.getType)
    let_expr Exists α p := type |
      throwError "intro_split: expected an existential"
    let contType ← withLocalDeclD `x α fun x => do
      mkForallFVars #[x] (← mkArrow (mkApp p x).headBeta target)
    let cont ← mkFreshExprSyntheticOpaqueMVar contType (← goal.getTag)
    goal.assign (mkApp5 (mkConst ``Exists.elim [← getLevel α]) α p target (.fvar fvarId) cont)
    let (fields, goal) ← cont.mvarId!.introNP 2
    return (fields, ← goal.tryClear fvarId)

/-- Normalize and recursively split a fact into witnesses and conjuncts. -/
partial def splitHypothesis (goal : MVarId) (fvarId : FVarId) : MetaM MVarId := do
  let goal ← normalizeFact goal fvarId
  let type ← goal.withContext do instantiateMVars (← fvarId.getType)
  unless ← goal.withContext (isProp type) do return goal
  if type.consumeMData.isConstOf ``True then
    return (← goal.tryClear fvarId)
  let facts ← goal.withContext do collectFacts type (.fvar fvarId) (← fvarId.getUserName)
  let isExists := type.consumeMData.isAppOfArity ``Exists 2
  unless isExists do
    if let #[fact] := facts then
      if fact.type == type then return goal
  let (reverted, goal) ← goal.revertAfter fvarId
  let dependent ← goal.withContext do exprDependsOn (← goal.getType) fvarId
  let (fields, goal) ←
    if isExists then
      elimExists goal fvarId
    else if dependent && type.consumeMData.isAppOfArity ``And 2 then do
      let subgoals ← goal.cases fvarId witnessNames
      let #[subgoal] := subgoals |
        throwError "intro_split: expected a single constructor"
      pure (subgoal.fields.map Expr.fvarId!, subgoal.mvarId)
    else do
      let (fields, goal) ← goal.assertHypotheses facts
      pure (fields, ← goal.tryClear fvarId)
  let mut goal := goal
  /- Each edit invalidates later hypotheses. -/
  for field in fields.reverse do
    goal ← splitHypothesis goal field
  return (← goal.introNP reverted.size).2

/-- Peel leading existentials while preserving witness order. -/
partial def peelLeadingExists (goal : MVarId) (fvarId : FVarId)
    (witnesses : Array FVarId := #[]) : MetaM (MVarId × Array FVarId × Option FVarId) := do
  let goal ← normalizeFact goal fvarId
  let type ← goal.withContext do instantiateMVars (← fvarId.getType)
  unless type.consumeMData.isAppOfArity ``Exists 2 do return (goal, witnesses, some fvarId)
  let (fields, goal) ← elimExists goal fvarId
  let #[witness, rest] := fields |
    throwError "intro_split: expected an existential witness and its fact"
  peelLeadingExists goal rest (witnesses.push witness)

/-- The hypotheses of the main goal, to be compared with the context a later step reaches. -/
def localHypotheses : TacticM (Std.HashSet FVarId) := do
  (← getMainGoal).withContext do
    pure <| (← getLCtx).foldl (init := ∅) fun acc decl => acc.insert decl.fvarId

/-- Normalize and split the hypotheses which appeared since `before` was taken. -/
def splitNewHypotheses (before : Std.HashSet FVarId) : TacticM Unit := do
  let goal ← getMainGoal
  let introduced ← goal.withContext do
    pure <| (← getLCtx).foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail || before.contains decl.fvarId then acc
      else acc.push decl.fvarId
  let mut goal := goal
  for fvarId in introduced.reverse do
    let (goal', fvarId) ← normalizeExists goal fvarId
    goal := goal'
    goal ← splitHypothesis goal fvarId
  replaceMainGoal [goal]

private def leadingBinders : Expr → Nat
  | .forallE _ _ body _ => leadingBinders body + 1
  | .letE _ _ _ body _ => leadingBinders body + 1
  | .mdata _ body => leadingBinders body
  | _ => 0

/-- Introduce leading binders without replacing their user names. -/
def introsPreservingNames (goal : MVarId) : MetaM (Array FVarId × MVarId) := do
  goal.introNP (leadingBinders (← instantiateMVars (← goal.getType)).consumeMData)

/-- Introduce a premise and split its facts while preserving binder order. -/
elab (name := introSplit) "intro_split" : tactic => do
  let before ← localHypotheses
  let (introduced, goal) ← introsPreservingNames (← getMainGoal)
  let factIdx? ← goal.withContext do
    let mut idx? := none
    for h : i in [0 : introduced.size] do
      if ← isProp (← introduced[i].getType) then
        idx? := some i
        break
    pure idx?
  let some factIdx := factIdx? |
      replaceMainGoal [goal]
      return
  let fact := introduced[factIdx]!
  let hoistExists ← goal.withContext do
    return (← instantiateMVars (← fact.getType)).consumeMData.headBeta.isAppOfArity ``Exists 2
  let (_, goal) ← goal.revertAfter fact
  let (goal, fact) ← normalizeExists goal fact
  let (goal, witnesses, rest?) ←
    if hoistExists then peelLeadingExists goal fact
    else pure (goal, #[], some fact)
  let goal ← match rest? with
    | some rest => splitHypothesis goal rest
    | none => pure goal
  /- Restore the premise's binder order. -/
  let newFVars ← goal.withContext do
    pure <| (← getLCtx).foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail || before.contains decl.fvarId then acc
      else acc.push decl.fvarId
  let ordered := witnesses ++ newFVars.filter (!witnesses.contains ·)
  let dependsOnOutput ← goal.withContext do
    witnesses.anyM fun witness => do
      let type ← witness.getType
      (newFVars.filter (!witnesses.contains ·)).anyM (exprDependsOn type ·)
  if ordered == newFVars || dependsOnOutput then
    replaceMainGoal [goal]
    return
  let (reverted, goal) ← goal.revert ordered (preserveOrder := true)
  let goal := (← goal.introNP reverted.size).2
  let outputIndex := if factIdx > 0 then reverted.idxOf introduced[0]! else 0
  replaceMainGoal [← markOutputIndex goal outputIndex]

end Aeneas.Step.Intro
