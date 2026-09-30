module
public import Lean
public import Mathlib.Logic.Basic
public section

/-! This module provides building blocks to write a prepare_intro_outputs tactic. -/

namespace Aeneas.Step.PrepareIntroOutputs

open Lean Meta Elab Tactic

/-- Whether `e` consists only of outputs, projections, and constructors. -/
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

/-- Reduce `e` if it is an application of one of the `markers` by unfolding the marker. -/
meta def reduceMarker? (markers : Array Name) (e : Expr) : MetaM (Option Expr) := do
  let .const name _ := e.getAppFn | return none
  unless markers.contains name do return none
  let some unfolded ← unfoldDefinition? e | return none
  let some matcher ← matchMatcherApp? unfolded | return none
  unless matcher.alts.size == 1 do return none
  for discr in matcher.discrs do
    unless ← isOutputLike discr do return none
  match ← Lean.Meta.reduceMatcher? unfolded with
  | .reduced reduced => return some reduced.headBeta
  | _ => return none

/-- Whether `e` consists of logical connectives,
and matches (which are entered, but not split). -/
private meta def isLogical (e : Expr) : MetaM Bool := do
  if e.isForall || e.isLambda || e.isLet then return true
  if [``And, ``Or, ``Exists, ``Not, ``Eq, ``Iff, ``ite, ``dite].any e.isAppOf then return true
  if let .const name _ := e.getAppFn then return ← isMatcher name
  return false

/-- Unfold `e` if it is an application of reducible definitions (e.g., `abbrev`s) standing
for a conjunction or an existential. Matches are not unfolded. -/
meta partial def unfoldReducibleHyp? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  let .const name _ := e.getAppFn | return none
  if ← isMatcher name then return none
  unless (← getReducibilityStatus name) == .reducible do return none
  let some e' ← unfoldDefinition? e | return none
  let e' := e'.headBeta.consumeMData
  if e'.isAppOfArity ``And 2 || e'.isAppOfArity ``Exists 2 then return some e'
  unfoldReducibleHyp? e'

/-- Reduce the markers and unfold the reducible definitions standing for a conjunction or an
existential, anywhere in the logical structure of `e` (see `isLogical`). The result is
definitionally equal to `e`. -/
meta def reduceHyp (markers : Array Name) (e : Expr) : MetaM Expr := do
  let pre (e : Expr) : MetaM TransformStep := do
    if e.isMData then return .continue
    if let some e' ← reduceMarker? markers e then return .visit e'
    if ← isLogical e then return .continue
    if let some e' ← unfoldReducibleHyp? e then return .visit e'
    return .done e
  withTransparency .default <| Meta.transform (← instantiateMVars e) (pre := pre)

theorem forall_unit {p : Prop} : (Unit → p) ↔ p :=
  ⟨fun h => h (), fun h _ => h⟩

/-- Simplify a hypothesis, in its logical structure: eliminate defining
existentials, and drop trivial conjuncts and premises. -/
meta def simpHyp (type : Expr) : MetaM Simp.Result := do
  let names := #[
    /- Defining existentials: `∃ y, y = e ∧ P y` becomes `P e`. -/
    ``exists_eq_left, ``exists_eq_left', ``exists_eq_right, ``exists_eq_right',
    ``exists_eq, ``exists_eq',
    /- Trivial conjuncts and premises. -/
    ``and_true, ``true_and, ``eq_self_iff_true, ``true_imp_iff, ``forall_unit]
  let thms ← names.foldlM (init := ({} : SimpTheorems)) fun thms name => do
    (← thms.addConst name (post := false)).addConst name
  let ctx ← Simp.mkContext { iota := false, zeta := false, dsimp := false }
    (simpTheorems := #[thms])
  let pre : Simp.Simproc := fun e => do
    if ← isLogical e then return ← Simp.preDefault #[] e
    return .done { expr := e }
  let (result, _) ← Simp.main type ctx (methods := { Simp.mkDefaultMethodsCore #[] with pre })
  return result

/-- Split the hypothesis of `∀ h : hyp, body h` into the witnesses and conjuncts `hyp` stands
for:
- `∀ h : True, body h` becomes `body trivial`;
- `∀ h : a ∧ b, body h` becomes `∀ (ha : a) (hb : b), body ⟨ha, hb⟩`, and `a` and `b` are
  split in turn;
- `∀ h : ∃ x, p x, body h` becomes `∀ x (h : p x), body ⟨x, h⟩`, and `p x` is split in turn;
  the witness keeps the name of the existential binder;
- a reducible definition standing for one of the above is unfolded first;
- any other hypothesis is left alone.

`body` is a function of the proof of the hypothesis. Returns `newTarget`, and a proof of
`(∀ h : hyp, body h) ↔ newTarget`. -/
meta partial def splitHypAux (name : Name) (hyp body : Expr) : MetaM (Expr × Expr) := do
  let hyp := (← unfoldReducibleHyp? hyp).getD hyp.consumeMData
  if hyp.isConstOf ``True then
    return ((mkApp body (mkConst ``True.intro)).headBeta,
      mkApp3 (mkConst ``forall_prop_of_true) hyp body (mkConst ``True.intro))
  match_expr hyp with
  | And a b =>
    /- (∀ h : a ∧ b, body h)
         ↔ ∀ (ha : a) (hb : b), body ⟨ha, hb⟩     -- `forall_and_index`
         ↔ ∀ (ha : a), splitB ha                   -- split `b`, under `ha`
         ↔ newTarget                               -- split `a` -/
    let step₁ ← mkAppOptM ``forall_and_index #[a, b, body]
    let (splitB, step₂) ← withLocalDeclD name a fun ha => do
      let bodyB ← withLocalDeclD name b fun hb => do
        mkLambdaFVars #[hb] (mkApp body (mkApp4 (mkConst ``And.intro) a b ha hb)).headBeta
      let (splitB, proofB) ← splitHypAux name b bodyB
      return (← mkLambdaFVars #[ha] splitB,
        ← mkAppM ``forall_congr' #[← mkLambdaFVars #[ha] proofB])
    let (newTarget, step₃) ← splitHypAux name a splitB
    return (newTarget, ← mkAppM ``Iff.trans #[step₁, ← mkAppM ``Iff.trans #[step₂, step₃]])
  | Exists α p =>
    /- (∀ h : ∃ x, p x, body h)
         ↔ ∀ x (h : p x), body ⟨x, h⟩     -- `forall_exists_index`
         ↔ ∀ x, splitP x                   -- split `p x`, under `x` -/
    let step₁ ← mkAppOptM ``forall_exists_index #[α, p, body]
    let witness := if let .lam n .. := p then n else `x
    withLocalDeclD witness α fun x => do
      let px := (mkApp p x).headBeta
      let bodyX ← withLocalDeclD name px fun h => do
        mkLambdaFVars #[h]
          (mkApp body (mkApp4 (mkConst ``Exists.intro [← getLevel α]) α p x h)).headBeta
      let (splitP, proofP) ← splitHypAux name px bodyX
      let step₂ ← mkAppM ``forall_congr' #[← mkLambdaFVars #[x] proofP]
      return (← mkForallFVars #[x] splitP, ← mkAppM ``Iff.trans #[step₁, step₂])
  | _ =>
    let newTarget ← withLocalDeclD name hyp fun h => do
      mkForallFVars #[h] (mkApp body h).headBeta
    return (newTarget, ← mkAppM ``Iff.refl #[newTarget])

/-- Split the hypothesis of `∀ h : hyp, body h` into binders (see `splitHypAux`).

Returns `newTarget`, and a proof of `(∀ h : hyp, body h) ↔ newTarget`. -/
meta def splitHyp (body : Expr) (hyp' : Simp.Result) : MetaM (Expr × Expr) := do
  let .lam name _ b bi := body | throwError "splitHyp: expected a function, got {body}"
  let (newTarget, splitProof) ← splitHypAux name hyp'.expr (.lam name hyp'.expr b bi)
  let some eq := hyp'.proof? | return (newTarget, splitProof)
  if body.bindingBody!.hasLooseBVars then
    throwError "splitHyp: the hypothesis can not be rewritten, as the body uses it"
  /- `(∀ h : hyp, body h) ↔ (∀ h : hyp'.expr, body h)` -/
  let congr ← mkAppOptM ``imp_congr_left
    #[none, none, some b, some (← mkAppM ``Iff.of_eq #[eq])]
  return (newTarget, ← mkAppM ``Iff.trans #[congr, splitProof])

/-- Introduce the outputs, i.e. the leading binders of `e` which are not propositions, and
pass them to `k` together with the remainder of `e`. -/
private meta partial def withOutputs {α} (e : Expr) (k : Array Expr → Expr → MetaM α)
    (xs : Array Expr := #[]) : MetaM α := do
  if let .forallE name dom body bi := e.consumeMData then
    unless ← isProp dom do
      return ← withLocalDecl name bi dom fun x =>
        withOutputs (body.instantiate1 x) k (xs.push x)
  k xs e.consumeMData

/-- Rewrite the goal `∀ xs, target` into `∀ xs, newTarget`, given `target ↔ newTarget` -/
meta def rewriteUnderOutputs (goal : MVarId) (xs : Array Expr) (newTarget proof : Expr) :
    MetaM MVarId := do
  let result : Simp.Result :=
    { expr := newTarget, proof? := some (← mkAppM ``propext #[proof]) }
  applySimpResultToTarget goal (← instantiateMVars (← goal.getType)) (← result.addForalls xs)

/-- Rewrite specialized for rewriting only post in goals like `forall xs. post -> _` -/
meta def rewritePost (goal : MVarId) (rewrite : Expr → Expr → MetaM (Expr × Expr)) :
    MetaM (Option MVarId) := goal.withContext do
  withOutputs (← instantiateMVars (← goal.getType)) fun xs target => do
    let .forallE name post b bi := target | return none
    let (newTarget, proof) ← rewrite post (.lam name post b bi)
    if newTarget == target then return none
    return some (← rewriteUnderOutputs goal xs newTarget proof)

end Aeneas.Step.PrepareIntroOutputs
