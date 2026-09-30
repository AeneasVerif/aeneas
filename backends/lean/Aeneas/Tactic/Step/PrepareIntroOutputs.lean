module
public import Aeneas.Std.WP
public meta import AeneasMeta.Simp.Simp
public import Aeneas.Tactic.Step.Simp
public import Aeneas.Tactic.Step.Trace
public section

namespace Aeneas.Step

open Lean Elab Term Meta Tactic
open Utils

/-- Note that `forall_const` is too general: it can eliminate unused outputs that we actually
want to introduce in the context -/
theorem forall_unit {p : Prop} : (Unit → p) ↔ p := by simp

theorem forall_punit (p : PUnit.{u} → Prop) : (∀ x, p x) ↔ p PUnit.unit :=
  ⟨fun h => h _, fun h _ => h⟩

simproc_decl existsImpNamed ((∃ _, _) → _) := fun e => do
  let .forallE _ d b _ := e | return .continue
  if b.hasLooseBVars then return .continue
  let_expr Exists α p := d | return .continue
  let n := match p with
    | .lam n .. => n
    | _ => `x
  let e' ← withLocalDeclD n α fun x => do
    mkForallFVars #[x] (← mkArrow (p.beta #[x]) b)
  let proof ← mkPropExt (← mkAppOptM ``exists_imp #[α, p, b])
  return .visit { expr := e', proof? := proof }

/-- Names introduced by the `do` elaborator's `mkPatContinuation` as a
    fallback (`_xN`) when no leaf name is available — e.g. all leaves are
    `_`. These get filtered out so we fall back to spec post-condition names. -/
meta def Name.isElabSynthesized : Name → Bool
  | .str .anonymous s => s.startsWith "_x" && s.length > 2 && (s.drop 2).all Char.isDigit
  | _ => false

/-- Convert an fvar's user name into the `Option Name` slot used by `step*`.
    Returns `none` for macro-scoped names and `_xN` placeholders. -/
meta def fvarNameSlot (fv : Expr) : MetaM (Option Name) := do
  let n ← fv.fvarId!.getUserName
  pure (if n.hasMacroScopes ∨ Name.isElabSynthesized n then none else some n)

meta section
/-- A generic binary tree with data at the leaves. Underlies `FVarTree` and `NameTree`. -/
inductive BTree (α : Type) where
  | leaf (val : α)
  | pair (left right : BTree α)
deriving Inhabited, Repr
end

/-- Flatten a `BTree` into a left-to-right array of leaf values. -/
meta def BTree.flatten {α} : BTree α → Array α
  | .leaf v => #[v]
  | .pair l r => l.flatten ++ r.flatten

/-- Monadic map over the leaf values of a `BTree`. -/
meta def BTree.mapM {m} [Monad m] {α β} (f : α → m β) : BTree α → m (BTree β)
  | .leaf v => return .leaf (← f v)
  | .pair l r => return .pair (← l.mapM f) (← r.mapM f)

/-- A tree of fvars reflecting the decomposition structure of a continuation's input.
See `uncurryTelescope`. -/
abbrev FVarTree := BTree Expr

/-- A tree of binder names, obtained from an `FVarTree`. -/
abbrev NameTree := BTree (Option Name)

/-- Peel `uncurry`/`uncurry'`/lambda wrappers from a continuation expression,
introducing fvars into the local context, and call `k` with the resulting
`FVarTree` and remaining body. `k` receives `none` when no binder structure
is found.

See the examples and state descriptions below for the full specification.

## States

- **A** (`uncurryTelescope`): entry — dispatch on `uncurry`/`uncurry'`/lambda/other
- **B** (`intoUncurry`): inside uncurry — peel up to 2 lambdas from `f`
- **C** (`decomposeFVar`): check if an fvar is destructured by applied `uncurry` in body -/
meta partial def uncurryTelescope (e : Expr) (k : Option FVarTree → Expr → MetaM α) : MetaM α := do
  /- ## State A: Entry
     - `e = uncurry f` or `e = uncurry' f`: go to B(f, ...).
     - `e = fun x => body`: plain lambda, introduce fvar, call k.
     - Otherwise: call k none e. -/
  let e := e.consumeMData
  match_expr e with
  | Std.WP.uncurry' _ _ _ f =>
    intoUncurry f.consumeMData (fun tree body => k (some tree) body)
  | Std.uncurry _ _ _ f =>
    intoUncurry f.consumeMData (fun tree body => k (some tree) body)
  | _ =>
    if e.isLambda then
      Meta.lambdaBoundedTelescope e 1 fun args body => do
        if args.size == 0 then return ← k none e
        let x := args[0]!
        let ty ← x.fvarId!.getType
        if ty.isConstOf ``Unit || ty.isConstOf ``PUnit then
          k none body
        else
          k (some (.leaf x)) body
    else
      k none e
where
  /- ## State B: Peel uncurry — enter the lambda telescope
     Input: `f` is the function inside `uncurry`/`uncurry'`. After stripping,
     `f` is one of:
       | 2 | `fun a b => body`
       | 3 | `fun x => uncurry' (fun y z => body)`
       | 4 | `uncurry (fun a b c => body)`
       | 5 | `fun a => uncurry (fun b c => body)`
       | 6 | `fun _p c => (uncurry (fun a b => body)) _p`
       | 7 | `fun _p₀ _p₁ => (uncurry (fun a b => (uncurry (fun c d => body)) _p₁)) _p₀`
       | 8 | `fun _p d => (uncurry (fun _q c => (uncurry (fun a b => body)) _q)) _p`
  -/
  intoUncurry (f : Expr) (k : FVarTree → Expr → MetaM α) : MetaM α := do
    let f := f.consumeMData
    if f.isLambda then
      Meta.lambdaBoundedTelescope f 2 fun args body => do
        if args.size == 2 then
          /- 2 lambdas (cases 2, 6, 7, 8): resolve each fvar via C. -/
          decomposeFVar args[0]! body fun left body' =>
            decomposeFVar args[1]! body' fun right body'' =>
              k (.pair left right) body''
        else if args.size == 1 then
          /- 1 lambda (cases 3, 5): x₀ is the first element. The body starts
             with uncurry'/uncurry (Lean didn't eta-expand). Go to A on body
             to get the second subtree. -/
          let x₀ := args[0]!
          uncurryTelescope body fun optRight body' =>
            match optRight with
            | some right => k (.pair (.leaf x₀) right) body'
            | none => k (.leaf x₀) body'
        else
          do k (.leaf (.fvar (← Lean.mkFreshFVarId))) f
    else
      /- No lambdas — must be a nested uncurry (case 4: `f = uncurry g`).
         Go to A(f) to decompose the first element, then A(rest) for the
         second element. -/
      uncurryTelescope f fun optLeft rest =>
        uncurryTelescope rest fun optRight body' =>
          match optLeft, optRight with
          | some left, some right => k (.pair left right) body'
          | some left, none => k left body'
          | none, some right => k right body'
          | none, none => k (.leaf (.fvar default)) body'
  /- ## State C: Decompose one fvar
     Check if `x` is destructured by `uncurry g x` (5-arg applied uncurry)
     in `body`. If so, strip `x`, go to A(uncurry g) to decompose it.
     Otherwise return `leaf x`. -/
  decomposeFVar (x : Expr) (body : Expr) (k : FVarTree → Expr → MetaM α) : MetaM α := do
    let body := body.consumeMData
    match_expr body with
    | Std.uncurry _ _ _ _f arg =>
      let arg := arg.consumeMData
      if arg.isFVar && arg == x then
        /- `body = uncurry g x`: strip x to get `uncurry g` (4-arg app).
           Go to A to fully decompose. -/
        let uncurryG := body.appFn!
        uncurryTelescope uncurryG fun optTree body' =>
          match optTree with
          | some tree => k tree body'
          | none => k (.leaf x) body'
      else
        k (.leaf x) body
    | _ =>
      k (.leaf x) body

/-- Analyze a continuation expression to compute a `NameTree`.
Wrapper around `uncurryTelescope` that extracts names from the `FVarTree`. -/
meta def getContInput (e : Expr) : MetaM NameTree := do
  uncurryTelescope e fun optTree _body => do
    match optTree with
    | some tree => tree.mapM fvarNameSlot
    | none => return .leaf none

/-- Introduce one free variable per slot that has not the type unit, then pass the variables and their
tuple to `k`. For type `(A × B) × C` and pattern `((a, b), c)`, call
`k #[a, b, c] ((a, b), c)`. Slots of type unit become `()`. -/
meta partial def withOutputTuple {α β} (ty : Expr) (tree : BTree α)
    (k : Array Expr → Expr → MetaM β) : MetaM β := do
  let reducedTy ← withReducible <| whnf ty
  match tree with
  | .leaf _ =>
    if reducedTy.isConstOf ``PUnit then
      k #[] (mkConst ``PUnit.unit reducedTy.constLevels!)
    else
      withLocalDeclD `x ty fun x => k #[x] x
  | .pair l r =>
    match_expr reducedTy with
    | Prod a b =>
      withOutputTuple a l fun xs x =>
      withOutputTuple b r fun ys y => do
        k (xs ++ ys) (← mkAppM ``Prod.mk #[x, y])
    | _ => throwError "Expected a product for the output pattern, got {ty}"

/-- Normalize the applied spec's postcondition before constructing the equivalence goal.
For example, turn `∀ n, (∃ s, s = compute n ∧ P s) → Q n` into
`∀ n, P (compute n) → Q n`. Otherwise those existentials, or redundant `True`
conjuncts, would survive in the hypotheses introduced by `step`.

Skip explicit output binders, then simplify only the first premise with `step_simps`.
Do not unfold continuation wrappers or simplify output binders and the conclusion:
the latter may contain the caller's own quantifiers. Preserve dependent premises,
e.g. `∀ h : True ∧ True, h.1 = h.2`, because simplifying their type would require
transporting the proof used in the conclusion. -/
meta partial def simpOutputPost (type : Expr) : MetaM Expr := do
  let simpPost (post : Expr) := do
    let (ctx, simprocs) ← Simp.mkSimpCtx true { iota := false } .simp
      { simpThms := #[← stepSimpExt.getTheorems] }
    return (← Lean.Meta.simp post ctx simprocs).1.expr
  match type.consumeMData with
  | .forallE .. =>
    forallBoundedTelescope type (some 1) fun xs body => do
      let x := xs[0]!
      let ty ← inferType x
      if ← isProp ty then
        if body.containsFVar x.fvarId! then return type
        return ← mkArrow (← simpPost ty) body
      mkForallFVars xs (← simpOutputPost body)
  | _ => return type

/-- Replace the first output quantifier with binders matching `tree`.
A leading Prop binder is left for postcondition introduction.
For `∀ p : (A × B) × C, R p` and pattern `((a, b), c)`, return
`(∀ a b c, R ((a, b), c), 3)`. Unit outputs are replaced with `()`. -/
meta def mkOutputTarget (type : Expr) (tree : NameTree) : MetaM (Expr × Nat) := do
  let type ← withReducible <| whnf type
  unless type.isForall do
    throwError "Expected an output quantifier:\n{type}"
  let .forallE _ ty body _ := type | return (type, 0)
  if ← isProp ty then return (← simpOutputPost type, 0)
  withOutputTuple ty tree fun xs tuple => do
    let body ← simpOutputPost (body.instantiate1 tuple)
    return (← mkForallFVars xs body, xs.size)

/-- Use the supplied tactic to prove that the generated output target is equivalent
to the step goal. For example, the `spec` tactic proves
`(∀ p, P p → Q p) ↔ ∀ a b, P (a, b) → Q (a, b)` with one `simp` call. -/
meta def proveOutputEquiv (goalTy target : Expr) (prove : TacticM Unit) : TacticM Expr := do
  let equiv ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Iff #[goalTy, target])
  let remaining ← Tactic.run equiv.mvarId! do
    withoutRecover prove
  unless remaining.isEmpty do
    throwError "Could not prove the output target equivalent to the step goal:\n{remaining}"
  return ← instantiateMVars equiv

/-- Shared implementation for goal-preparation callbacks. Given a quantified
`type` and a call-site pattern, build the target, prove its equivalence using `prove`,
then replace the goal without introducing variables. For example, with
`type = ∀ p, P p → Q p` and pattern `(a, b)`, the target is
`∀ a b, P (a, b) → Q (a, b)`. -/
meta def prepareIntroOutputsWith (type : Expr) (tree : NameTree) (prove : TacticM Unit) :
    TacticM Nat := do
  withTraceNode `Step (fun _ => pure m!"prepareIntroOutputs") do
  withMainContext do
  Utils.traceGoalWithNode `Step "Initial goal"
  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)
  let (target, prefixLength) ← mkOutputTarget type tree
  trace[Step] "Output target: {target}"
  let equiv ← proveOutputEquiv goalTy target prove
  let next ← mkFreshExprSyntheticOpaqueMVar target (← goal.getTag)
  goal.assign (← mkAppM ``Iff.mpr #[equiv, next])
  setGoals [next.mvarId!]
  return prefixLength

/-- Goal preparation shared by `spec` and `dspec`. The goal produced by the mono and bind
rules has the shape `∀ x, P x → Q x`, where `Q x` is either the caller's postcondition or
`spec (k x) Q'`. The output pattern is read from `Q` (or from the continuation `k`).
For `∀ p, P p → spec (k p) Q'` with pattern `((a, b), c)`, construct
`∀ a b c, P ((a, b), c) → spec (k ((a, b), c)) Q'`,
then prove equivalence with one `simp` call. -/
meta def prepareIntroOutputs : PrepareIntroOutputs := do
  withMainContext do
  let goalTy ← instantiateMVars (← getMainTarget)
  let tree ← forallBoundedTelescope goalTy (some 2) fun xs body => do
    unless xs.size == 2 do
      throwError "Expected a goal of the shape `∀ x, P x → Q x`, got:\n{goalTy}"
    let x := xs[0]!
    if (← isProp (← inferType x)) || !(← isProp (← inferType xs[1]!)) then
      throwError "Expected a goal of the shape `∀ x, P x → Q x`, got:\n{goalTy}"
    let cont := match_expr body with
      | Std.WP.spec _ m _ => m
      | Std.WP.dspec _ m _ => m
      | _ => body
    getContInput (← mkLambdaFVars #[x] cont).eta
  prepareIntroOutputsWith goalTy tree do
    let _ ← Simp.simpAt true { failIfUnchanged := false, iota := false }
      { simpThms := #[← stepSimpExt.getTheorems],
        addSimpThms := #[``Std.uncurry_apply_pair,
          ``Std.WP.uncurry'_eq, ``Std.WP.uncurry'_pair,
          ``Std.WP.forall_unit, ``true_imp_iff, ``Prod.forall, ``forall_punit,
          ``and_imp, ``exists_imp] }
      (.targets #[] true)

end Aeneas.Step
