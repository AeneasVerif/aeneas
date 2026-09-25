module
public import Lean
public import AeneasMeta.Utils
public import Aeneas.Std.Spec
public section

/-!
# Normalizing the premise of a step theorem

After applying a step theorem, `step` is left with a target `∀ outputs, fact → k outputs`,
which the `intro_tactic` of the judgment has to bring to the shape `step` introduces: one
binder per fact. `normalizeTarget` does so for judgments whose premise is a plain
implication, such as `Std.WP.spec` (see `Std.WP.introTactic`). For instance, it rewrites
```
∀ x, uncurry' (fun a b => ∃ y, P a b ∧ Q a b y) x → k x ⦃ r => R r ⦄
```
to
```
∀ x y, P x.1 x.2 → Q x.1 x.2 y → k x ⦃ r => R r ⦄
```
in three steps, one per section below: reduce the `uncurry'` marker, simplify the fact, and
split its `∧`s and `∃`s into binders. The outputs stay the leading binders: the existential
witnesses always come after them, including for a postcondition with a single binder such as
`⦃ r => ∃ y, P r y ⦄`.

`normalizeTarget` rewrites the goal; it does not introduce the fact as a hypothesis and then
simplify that hypothesis. This matters for recursive specifications: `decreasing_by` sees
the hypotheses that the proof term binds around the recursive call. If we introduced
`h : uncurry' (…) x` and simplified it afterwards, the proof term would still bind `h` with
its original, unsplit type, and that is what the termination proof would get. Rewriting the
goal first makes the proof term bind the split facts directly
(see `Tests/IntroRecursion.lean`).
-/

namespace Aeneas.Step.Intro

open Lean Meta Elab Tactic

/-! ## Step 1: markers -/

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

/-- Reduce `e` if it is an application of one of the `markers`, the definitions the
postcondition notation of the judgment wraps its body in: `uncurry' p x` reduces to
`p x.1 x.2`.

A marker is only reduced if it unfolds to a match with a single alternative on outputs
(see `isOutputLike`), so that program computations are never evaluated. -/
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

/-- Reduce up to `fuel` markers at the head of `e`. -/
meta partial def reduceMarkers (markers : Array Name) (e : Expr) (fuel : Nat := 16) :
    MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    match ← reduceMarker? markers e with
    | some e' => reduceMarkers markers e' fuel
    | none => return e

/-! ## Step 2: simplification -/

theorem forall_unit {p : Prop} : (Unit → p) ↔ p :=
  ⟨fun h => h (), fun h _ => h⟩

/-- Whether `normalizeFact` looks inside `e`: logical connectives, and matches (which are
entered, but not split). -/
private meta def isLogical (e : Expr) : MetaM Bool := do
  if e.isForall || e.isLambda || e.isLet then return true
  if [``And, ``Or, ``Exists, ``Not, ``Eq, ``Iff, ``ite, ``dite].any e.isAppOf then return true
  if let .const name _ := e.getAppFn then return ← isMatcher name
  return false

/-- Unfold `e` if it is an application of reducible definitions (e.g., `abbrev`s) standing
for a conjunction or an existential, which `splitFact` then splits. Matches are not
unfolded, so that postconditions destructuring a value stay bundled. -/
meta partial def unfoldReducibleFact? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  let .const name _ := e.getAppFn | return none
  if ← isMatcher name then return none
  unless (← getReducibilityStatus name) == .reducible do return none
  let some e' ← unfoldDefinition? e | return none
  let e' := e'.headBeta.consumeMData
  if e'.isAppOfArity ``And 2 || e'.isAppOfArity ``Exists 2 then return some e'
  unfoldReducibleFact? e'

/-- Normalize a fact: reduce the markers anywhere in its logical structure (see
`isLogical`), unfold the reducible definitions standing for a conjunction or an existential,
eliminate defining existentials, and drop trivial conjuncts and premises. Other program
terms are left alone, so that bundled postconditions stay bundled. -/
meta def normalizeFact (markers : Array Name) (type : Expr) : MetaM Simp.Result := do
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
    /- Simp runs with reducible transparency, which would not unfold the markers. -/
    if let some e' ← withTransparency .default (reduceMarker? markers e) then
      return .visit { expr := e'.headBeta }
    if ← isLogical e then return ← Simp.preDefault #[] e
    if let some e' ← unfoldReducibleFact? e then return .visit { expr := e' }
    return .done { expr := e }
  let (result, _) ← Simp.main type ctx (methods := { Simp.mkDefaultMethodsCore #[] with pre })
  return result

/-! ## Step 3: splitting -/

theorem forall_and_index {a b : Prop} {p : a ∧ b → Prop} :
    (∀ h, p h) ↔ ∀ (ha : a) (hb : b), p ⟨ha, hb⟩ :=
  ⟨fun h ha hb => h ⟨ha, hb⟩, fun h ⟨ha, hb⟩ => h ha hb⟩

/-- Split the premise `∀ h : fact, rest h` into the witnesses and conjuncts `fact` stands for:
- `∀ h : True, rest h` becomes `rest trivial`;
- `∀ h : a ∧ b, rest h` becomes `∀ (ha : a) (hb : b), rest ⟨ha, hb⟩`, and `a` and `b` are
  split in turn;
- `∀ h : ∃ x, p x, rest h` becomes `∀ x (h : p x), rest ⟨x, h⟩`, and `p x` is split in turn;
- a reducible definition standing for one of the above is unfolded first;
- any other fact is left alone.

`rest` is a function of the proof of the fact. Returns the new premise, and a proof that it
is equivalent to `∀ h : fact, rest h`. -/
meta partial def splitFact (name : Name) (fact rest : Expr) : MetaM (Expr × Expr) := do
  let fact := (← unfoldReducibleFact? fact).getD fact.consumeMData
  if fact.isConstOf ``True then
    return ((mkApp rest (mkConst ``True.intro)).headBeta,
      mkApp3 (mkConst ``forall_prop_of_true) fact rest (mkConst ``True.intro))
  match_expr fact with
  | And a b =>
    /- (∀ h : a ∧ b, rest h)
         ↔ ∀ (ha : a) (hb : b), rest ⟨ha, hb⟩     -- `forall_and_index`
         ↔ ∀ (ha : a), splitB ha                   -- split `b`, under `ha`
         ↔ premise                                 -- split `a` -/
    let step₁ ← mkAppOptM ``forall_and_index #[a, b, rest]
    let (splitB, step₂) ← withLocalDeclD name a fun ha => do
      let restB ← withLocalDeclD name b fun hb => do
        mkLambdaFVars #[hb] (mkApp rest (mkApp4 (mkConst ``And.intro) a b ha hb)).headBeta
      let (splitB, proofB) ← splitFact name b restB
      return (← mkLambdaFVars #[ha] splitB,
        ← mkAppM ``forall_congr' #[← mkLambdaFVars #[ha] proofB])
    let (premise, step₃) ← splitFact name a splitB
    return (premise, ← mkAppM ``Iff.trans #[step₁, ← mkAppM ``Iff.trans #[step₂, step₃]])
  | Exists α p =>
    /- (∀ h : ∃ x, p x, rest h)
         ↔ ∀ x (h : p x), rest ⟨x, h⟩     -- `forall_exists_index`
         ↔ ∀ x, splitP x                   -- split `p x`, under `x` -/
    let step₁ ← mkAppOptM ``forall_exists_index #[α, p, rest]
    withLocalDeclD `x α fun x => do
      let px := (mkApp p x).headBeta
      let restX ← withLocalDeclD name px fun h => do
        mkLambdaFVars #[h]
          (mkApp rest (mkApp4 (mkConst ``Exists.intro [← getLevel α]) α p x h)).headBeta
      let (splitP, proofP) ← splitFact name px restX
      let step₂ ← mkAppM ``forall_congr' #[← mkLambdaFVars #[x] proofP]
      return (← mkForallFVars #[x] splitP, ← mkAppM ``Iff.trans #[step₁, step₂])
  | _ =>
    let premise ← withLocalDeclD name fact fun h => do
      mkForallFVars #[h] (mkApp rest h).headBeta
    return (premise, ← mkAppM ``Iff.refl #[premise])

/-! ## Putting it together -/

/-- Introduce the outputs, i.e. the leading binders of `e` which are not propositions, and
pass them to `k` together with the remainder of `e`. -/
private meta partial def withOutputs {α} (e : Expr) (k : Array Expr → Expr → MetaM α)
    (xs : Array Expr := #[]) : MetaM α := do
  if let .forallE name dom body bi := e.consumeMData then
    unless ← isProp dom do
      return ← withLocalDecl name bi dom fun x =>
        withOutputs (body.instantiate1 x) k (xs.push x)
  k xs e.consumeMData

/-- Normalize the first fact of the target, as described in the module doc. `markers` are
the definitions to reduce in step 1.

Returns the new goal, or `none` if the target is already normalized. The outputs remain the
leading binders of the new goal.

The `Example:` comments follow the example of the module doc. -/
meta def normalizeTarget (markers : Array Name) (goal : MVarId) :
    MetaM (Option MVarId) := goal.withContext do
  /- The new goal lives in the context of the original one, not under the outputs. -/
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  /- Introduce the outputs `xs`, and split the rest of the target into the fact `dom` and
     the continuation `body`. -/
  withOutputs (← instantiateMVars (← goal.getType)) fun xs original => do
    let .forallE name dom body bi := original | return none
    /- Example: `xs = #[x]`, `dom = uncurry' (fun a b => ∃ y, P a b ∧ Q a b y) x`, and
       `body = k x ⦃ r => R r ⦄`. -/

    /- Steps 1–2: reduce the markers and simplify the fact, with `factEq? : dom = fact`.
       When the continuation depends on the proof of the fact, the fact can only be changed
       up to definitional equality: we then only reduce the markers at its head. -/
    let (fact, factEq?) ←
      if body.hasLooseBVars then pure (← reduceMarkers markers dom, none)
      else
        let result ← normalizeFact markers dom
        pure (result.expr, result.proof?)
    /- Example: `fact = ∃ y, P x.1 x.2 ∧ Q x.1 x.2 y`. -/

    /- Step 3: split `fact` into binders, with `proof : original ↔ premise`. -/
    let (premise, splitProof) ← splitFact name fact (.lam name fact body bi)
    let proof ← match factEq? with
      | none => pure splitProof
      | some eq =>
        let congr ← mkAppOptM ``imp_congr_left
          #[none, none, some body, some (← mkAppM ``Iff.of_eq #[eq])]
        mkAppM ``Iff.trans #[congr, splitProof]
    /- Example: `premise = ∀ y, P x.1 x.2 → Q x.1 x.2 y → k x ⦃ r => R r ⦄`. -/

    if premise == original then return none

    /- Replace `goal : ∀ xs, original` by `newGoal : ∀ xs, premise`, with
       `goal := fun xs => proof.mpr (newGoal xs)`. -/
    let newTarget ← mkForallFVars xs premise
    let newGoal ← withLCtx lctx localInsts do
      mkFreshExprSyntheticOpaqueMVar newTarget (← goal.getTag)
    /- Example: `newTarget = ∀ x y, P x.1 x.2 → Q x.1 x.2 y → k x ⦃ r => R r ⦄`. -/
    goal.assign (← mkLambdaFVars xs (← mkAppM ``Iff.mpr #[proof, mkAppN newGoal xs]))
    return some newGoal.mvarId!

end Aeneas.Step.Intro
