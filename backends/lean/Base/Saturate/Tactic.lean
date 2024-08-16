import Base.Saturate.Attribute

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
open Utils Extensions

namespace Saturate

/-- Find all the lemmas which match an expression.

    - `dtrees`: the discrimination trees (the sets of rules in which to match)
    - `boundVars`: if an instantiation of a theorem contains a bound variable, we ignore
      it (because we couldn't introduce the instantiated theorem it in the environment)
    - `matched`: the theorems to apply (the set of theorem name and list of arguments)

    We return the set of: (theroem name, list of arguments)
 -/
def matchExpr (dtrees : Array (DiscrTree (Nat × Expr × Name)))
  (boundVars : HashSet FVarId)
  (matched : HashSet (Name × List Expr)) (e : Expr) :
  MetaM (HashSet (Name × List Expr)) := do
  trace[Saturate] "Matching: {e}"
  dtrees.foldlM (fun matched dtree => do
    let config : WhnfCoreConfig := {}
    let exprs ← dtree.getMatch e config
    trace[Saturate] "Potential matches: {exprs}"
    -- Check each expression
    (exprs.foldlM fun matched (numBinders, pat, thName) => do
      -- Introduce meta-variables for the universes
      let info ← getConstInfo thName
      let mvarLevels ← mkFreshLevelMVarsFor info
      let pat := pat.instantiateLevelParams info.levelParams mvarLevels
      -- Strip the binders, introduce meta-variables at the same time, and match
      let (mvars, _, pat) ← lambdaMetaTelescope pat (some numBinders)
      if ← isDefEq pat e then
        -- It matched! Check the variables which appear in the arguments
        let (args, allFVars) ← mvars.foldrM (fun arg (args, hs) => do
            let arg ← instantiateMVars arg
            let hs ← getFVarIds arg hs
            pure (arg :: args, hs)
          ) ([], HashSet.empty)
        if boundVars.all (fun fvar => ¬ allFVars.contains fvar) then
          -- Ok: save the theorem
          trace[Saturate] "Matched with: {thName} {args}"
          pure (matched.insert (thName, args))
        else
          -- Ignore
          trace[Saturate] "Didn't match"
          pure matched
      else
        -- Didn't match, leave the set of matches unchanged
        trace[Saturate] "Didn't match"
        pure matched) matched
  ) matched

/- Recursively explore a term -/
private partial def visit (dtrees : Array (DiscrTree (Nat × Expr × Name)))
  (boundVars : HashSet FVarId)
  (matched : HashSet (Name × List Expr))
  (e : Expr) : MetaM (HashSet (Name × List Expr)) := do
  -- Match
  let matched ← matchExpr dtrees boundVars matched e
  -- Recurse
  let visitBinders
    (boundVars : HashSet FVarId) (matched : HashSet (Name × List Expr)) (xs: Array Expr) :
    MetaM (HashSet FVarId × (HashSet (Name × List Expr))) := do
    -- Visit the type of the binders, as well as the bodies
    xs.foldlM (fun (boundVars, matched) x => do
      let fvarId := x.fvarId!
      let localDecl ← fvarId.getDecl
      let boundVars := boundVars.insert fvarId
      let matched ← visit dtrees boundVars matched localDecl.type
      let matched ←
        match localDecl.value? with
        | none => pure matched
        | some v => visit dtrees boundVars matched v
      pure (boundVars, matched)
      ) (boundVars, matched)
  match e.consumeMData with
  | .bvar _
  | .fvar _
  | .mvar _
  | .sort _
  | .lit _
  | .const _ _ => pure matched
  | .app .. => do e.withApp fun f args => do
    -- Visit the args
    let matched ← args.foldlM (fun matched arg => visit dtrees boundVars matched arg) matched
    -- Visit the app
    visit dtrees boundVars matched f
  | .lam .. =>
    lambdaLetTelescope e fun xs b => do
      let (boundVars, matched) ← visitBinders boundVars matched xs
      visit dtrees boundVars matched b
  | .forallE .. => do
    forallTelescope e fun xs b => do
      let (boundVars, matched) ← visitBinders boundVars matched xs
      visit dtrees boundVars matched b
  | .letE .. => do
    lambdaLetTelescope e fun xs b => do
      let (boundVars, matched) ← visitBinders boundVars matched xs
      visit dtrees boundVars matched b
  | .mdata _ b => do
    visit dtrees boundVars matched b
  | .proj _ _ b => do
    visit dtrees boundVars matched b

/- The saturation tactic itself -/
def evalSaturate (sets : List Name) : TacticM Unit := do
  Tactic.withMainContext do
  -- Retrieve the rule sets
  let s := Saturate.Attribute.saturateAttr.ext.getState (← getEnv)
  let dtrees := Array.mk (sets.filterMap (fun set => s.find? set))
  trace[Saturate] "dtrees: {dtrees}"
  -- Get the local context
  let ctx ← Lean.MonadLCtx.getLCtx
  -- Explore the declarations
  let decls ← ctx.getDecls
  let matched ← decls.foldlM (fun matched (decl : LocalDecl) => do
    /- We explore both the type, the expresion and the body (if there is) -/
    let matched ← visit dtrees HashSet.empty matched decl.type
    let matched ← visit dtrees HashSet.empty matched decl.toExpr
    match decl.value? with
    | none => pure matched
    | some value => visit dtrees HashSet.empty matched value) HashSet.empty
  -- Explore the goal
  let matched ← visit dtrees HashSet.empty matched (← Tactic.getMainTarget)
  -- Introduce the theorems in the context
  for (thName, args) in matched do
    let th ← mkAppOptM thName (args.map some).toArray
    let thTy ← inferType th
    let _ ← Utils.addDeclTac (.str .anonymous "_") th thTy (asLet := false)

elab "aeneas_saturate" : tactic =>
  evalSaturate [`Aeneas.ScalarTac]

section Test
  set_option trace.Saturate false
  @[aeneas_saturate (set := Aeneas.Test) (pattern := l.length)]
  theorem test1 (α : Type u) (l : List α) : l.length ≥ 0 := by simp

  set_option trace.Saturate false

  theorem test {α : Type v} (l0 l1 l2 l3 l4 l5 : List α)
    (_ : ∀ (l : List α), l.length ≤ l3.length) :
    let _k := l4.length
    let _g := fun (l : List α) => l.length + l5.length
    (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length := by
    aeneas_saturate
    simp [Nat.add_assoc]
end Test

end Saturate
