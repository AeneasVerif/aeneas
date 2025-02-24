import Aeneas.Saturate.Attribute

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic

namespace Aeneas

open Utils Extensions

namespace Saturate

open Attribute

/-- Find all the lemmas which match an expression.

    - `dtrees`: the discrimination trees (the sets of rules in which to match)
    - `boundVars`: if an instantiation of a theorem contains a bound variable, we ignore
      it (because we couldn't introduce the instantiated theorem it in the environment)
    - `matched`: the theorems to apply (the set of theorem name and list of arguments)

    We return the set of: (theroem name, list of arguments)
 -/
def matchExpr (nameToRule : NameMap Rule) (dtrees : Array (DiscrTree Rule))
  (boundVars : Std.HashSet FVarId)
  (matched : Std.HashSet (Name × List Expr)) (e : Expr) :
  MetaM (Std.HashSet (Name × List Expr)) := do
  trace[Saturate] "Matching: {e}"
  dtrees.foldlM (fun matched dtree => do
    let exprs ← dtree.getMatch e
    trace[Saturate] "Potential matches: {exprs}"
    -- Check each expression
    (exprs.foldlM fun matched rule => do
      trace[Saturate] "Checking potential match: {rule}"
      -- Check if the theorem is still active
      if let some activeRule := nameToRule.find? rule.thName then do
        -- Check that the patterns are the same
        if activeRule.numBinders = rule.numBinders ∧ (← isDefEq activeRule.pattern rule.pattern) then
          -- Introduce meta-variables for the universes
          let info ← getConstInfo rule.thName
          let mvarLevels ← mkFreshLevelMVarsFor info
          let pat := rule.pattern.instantiateLevelParams info.levelParams mvarLevels
          -- Strip the binders, introduce meta-variables at the same time, and match
          let (mvars, _, pat) ← lambdaMetaTelescope pat (some rule.numBinders)
          trace[Saturate] "Checking if defEq:\n- pat: {pat}\n- expression: {e}"
          let pat_ty ← inferType pat
          let e_ty ← inferType e
          /- Small issue here: we use big integer constants and we have several patterns which
             are just a variable (for instance: `UScalar.bounds`). Because `isDefEq` first
             starts by unifying the expressions themselves (without looking at their type) we
             often end up attempting to unify every expression in the context with variables
             of type, e.g., `UScalar _`. The issue is that, if we attempt to unify an expression
             like `1000` with `?x : UScalar ?ty`, Lean will lanch a "max recursion depth" exception
             when attempting to reduce `1000` to `succ succ ...`. The current workaround is to
             first check whether the types are definitionally equal, then compare the expressions
             themselves. This way, in the case above we would not even compare `1000` with `?x`
             because `ℕ` wouldn't match `UScalar ?ty`.

             TODO: it would probably be more efficient to have a specific treatment of degenerate
             patterns, for instance by using the types as the keys in the discrimination trees.
           -/
          if ← isDefEq pat_ty e_ty then
            if ← isDefEq pat e then
              trace[Saturate] "defEq"
              -- It matched! Check the variables which appear in the arguments
              let (args, allFVars) ← mvars.foldrM (fun arg (args, hs) => do
                  let arg ← instantiateMVars arg
                  let hs ← getFVarIds arg hs
                  pure (arg :: args, hs)
                ) ([], Std.HashSet.empty)
              if boundVars.all (fun fvar => ¬ allFVars.contains fvar) then
                -- Ok: save the theorem
                trace[Saturate] "Matched with: {rule.thName} {args}"
                pure (matched.insert (rule.thName, args))
              else
                -- Ignore
                trace[Saturate] "Didn't match"
                pure matched
            else
              -- Didn't match, leave the set of matches unchanged
              trace[Saturate] "Didn't match"
              pure matched
          else
            -- Didn't match, leave the set of matches unchanged
              trace[Saturate] "Types didn't match"
              pure matched
        else
          -- The rule is not active
          trace[Saturate] "The rule is not active"
          pure matched
      else
        -- The rule is not active
        trace[Saturate] "The rule is not active"
        pure matched) matched
  ) matched

/- Recursively explore a term -/
private partial def visit (depth : Nat) (nameToRule : NameMap Rule)
  (dtrees : Array (DiscrTree Rule))
  (boundVars : Std.HashSet FVarId)
  (matched : Std.HashSet (Name × List Expr))
  (e : Expr) : MetaM (Std.HashSet (Name × List Expr)) := do
  trace[Saturate] "Visiting {e}"
  -- Match
  let matched ← matchExpr nameToRule dtrees boundVars matched e
  -- Recurse
  let visitBinders
    (depth : Nat)
    (boundVars : Std.HashSet FVarId) (matched : Std.HashSet (Name × List Expr)) (xs: Array Expr) :
    MetaM (Std.HashSet FVarId × (Std.HashSet (Name × List Expr))) := do
    -- Visit the type of the binders, as well as the bodies
    xs.foldlM (fun (boundVars, matched) x => do
      let fvarId := x.fvarId!
      let localDecl ← fvarId.getDecl
      let boundVars := boundVars.insert fvarId
      let matched ← visit (depth + 1) nameToRule dtrees boundVars matched localDecl.type
      let matched ←
        match localDecl.value? with
        | none => pure matched
        | some v => visit (depth + 1) nameToRule dtrees boundVars matched v
      pure (boundVars, matched)
      ) (boundVars, matched)
  let e := e.consumeMData
  match e with
  | .bvar _
  | .fvar _
  | .mvar _
  | .sort _
  | .lit _
  | .const _ _ =>
    trace[Saturate] "Stop: bvar, fvar, etc."
    pure matched
  | .app .. => do e.withApp fun f args => do
    trace[Saturate] ".app"
    -- Visit the args
    let matched ← args.foldlM (fun matched arg => visit (depth + 1) nameToRule dtrees boundVars matched arg) matched
    -- Visit the app
    visit (depth + 1) nameToRule dtrees boundVars matched f
  | .lam .. =>
    trace[Saturate] ".lam"
    lambdaLetTelescope e fun xs b => do
      let (boundVars, matched) ← visitBinders (depth + 1) boundVars matched xs
      visit (depth + 1) nameToRule dtrees boundVars matched b
  | .forallE .. => do
    trace[Saturate] ".forallE"
    forallTelescope e fun xs b => do
      let (boundVars, matched) ← visitBinders (depth + 1) boundVars matched xs
      visit (depth + 1) nameToRule dtrees boundVars matched b
  | .letE .. => do
    trace[Saturate] ".letE"
    lambdaLetTelescope e fun xs b => do
      let (boundVars, matched) ← visitBinders (depth + 1) boundVars matched xs
      visit (depth + 1) nameToRule dtrees boundVars matched b
  | .mdata _ b => do
    trace[Saturate] ".mdata"
    visit (depth + 1) nameToRule dtrees boundVars matched b
  | .proj _ _ b => do
    trace[Saturate] ".proj"
    visit (depth + 1) nameToRule dtrees boundVars matched b

def binaryConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``And, ``Or
]

def arithConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge
]

/- Fast version of `visit`: we do not explore everything. -/
private partial def fastVisit (depth : Nat) (nameToRule : NameMap Rule)
  (dtrees : Array (DiscrTree Rule))
  (matched : Std.HashSet (Name × List Expr))
  (e : Expr) : MetaM (Std.HashSet (Name × List Expr)) := do
  trace[Saturate] "Visiting {e}"
  -- Match
  let matched ← matchExpr nameToRule dtrees Std.HashSet.empty matched e
  -- Recurse
  let e := e.consumeMData
  match e with
  | .bvar _
  | .fvar _
  | .mvar _
  | .sort _
  | .lit _
  | .const _ _ =>
    trace[Saturate] "Stop: bvar, fvar, etc."
    pure matched
  | .app .. => do e.withApp fun f args => do
    trace[Saturate] ".app"
    let visitRec := fastVisit (depth + 1) nameToRule dtrees
    if f.isConst then
      --
      let constName := f.constName!
      if constName == ``Eq ∧ args.size == 3 then
        trace[Saturate] "Found `=`"
        let matched ← visitRec matched args[1]!
        let matched ← visitRec matched args[2]!
        pure matched
      else if constName ∈ binaryConsts ∧ args.size == 2 then
        trace[Saturate] "Found binary const: {f}"
        let matched ← visitRec matched args[0]!
        let matched ← visitRec matched args[1]!
        pure matched
      else if constName ∈ arithConsts ∧ args.size == 4 then
        trace[Saturate] "Found arith const: {f}"
        let matched ← visitRec matched args[2]!
        let matched ← visitRec matched args[3]!
        pure matched
      else
        -- Stop there
        pure matched
    else
      -- Stop there
      pure matched
  | .lam ..
  | .forallE ..
  | .letE .. => do
    -- Do not go inside the foralls, the lambdas and the let expressions
    pure matched
  | .mdata _ b => do
    trace[Saturate] ".mdata"
    fastVisit (depth + 1) nameToRule dtrees matched b
  | .proj _ _ _ => do
    trace[Saturate] ".proj"
    pure matched

/- The saturation tactic itself -/
def evalSaturate (fast : Bool) (sets : List Name) : TacticM Unit := do
  Tactic.withMainContext do
  trace[Saturate] "sets: {sets}"
  -- Retrieve the rule sets
  let s := Saturate.Attribute.saturateAttr.ext.getState (← getEnv)
  let dtrees := Array.mk (sets.filterMap (fun set => s.rules.find? set))
  -- Get the local context
  let ctx ← Lean.MonadLCtx.getLCtx
  -- Explore the declarations
  let decls ← ctx.getDecls
  let visit := if fast then fastVisit 0 s.nameToRule dtrees else visit 0 s.nameToRule dtrees Std.HashSet.empty

  let matched ← decls.foldlM (fun matched (decl : LocalDecl) => do
    trace[Saturate] "Exploring local decl: {decl.userName}"
    /- We explore both the type, the expresion and the body (if there is) -/
    let matched ← visit matched decl.type
    let matched ← visit matched decl.toExpr
    match decl.value? with
    | none => pure matched
    | some value => visit matched value) Std.HashSet.empty
  -- Explore the goal
  trace[Saturate] "Exploring the goal"
  let matched ← visit matched (← Tactic.getMainTarget)
  -- Introduce the theorems in the context
  for (thName, args) in matched do
    let th ← mkAppOptM thName (args.map some).toArray
    let thTy ← inferType th
    let _ ← Utils.addDeclTac (.str .anonymous "_") th thTy (asLet := false)

elab "aeneas_saturate" : tactic =>
  evalSaturate false [`Aeneas.ScalarTac]

section Test
  local elab "aeneas_saturate_test" : tactic =>
    evalSaturate false [`Aeneas.Test]

  set_option trace.Saturate.attribute false
  @[aeneas_saturate (set := Aeneas.Test) (pattern := l.length)]
  theorem rule1 (α : Type u) (l : List α) : l.length ≥ 0 := by simp

  set_option trace.Saturate false

  theorem test1 {α : Type v} (l0 l1 l2 l3 l4 l5 : List α)
    (_ : ∀ (l : List α), l.length ≤ l3.length) :
    let _k := l4.length
    let _g := fun (l : List α) => l.length + l5.length
    (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length := by
    aeneas_saturate_test
    simp [Nat.add_assoc]

  namespace Test
    set_option trace.Saturate.attribute false
    @[local aeneas_saturate (set := Aeneas.Test) (pattern := l.length)]
    theorem rule2 (α : Type u) (l : List α) : 0 ≤ l.length := by simp

    theorem test1 {α : Type v} (l0 l1 l2 l3 l4 l5 : List α)
      (_ : ∀ (l : List α), l.length ≤ l3.length) :
      let _k := l4.length
      let _g := fun (l : List α) => l.length + l5.length
      (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length := by
      aeneas_saturate_test
      simp [Nat.add_assoc]

    attribute [- aeneas_saturate] rule2

    theorem test2 {α : Type v} (l0 l1 l2 l3 l4 l5 : List α)
      (_ : ∀ (l : List α), l.length ≤ l3.length) :
      let _k := l4.length
      let _g := fun (l : List α) => l.length + l5.length
      (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length := by
      aeneas_saturate_test
      simp [Nat.add_assoc]
  end Test

  theorem test3 {α : Type v} (l0 l1 l2 l3 l4 l5 : List α)
    (_ : ∀ (l : List α), l.length ≤ l3.length) :
    let _k := l4.length
    let _g := fun (l : List α) => l.length + l5.length
    (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length := by
    aeneas_saturate_test
    simp [Nat.add_assoc]

end Test

end Saturate

end Aeneas
