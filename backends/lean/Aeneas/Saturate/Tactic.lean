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
def matchExpr
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (nameToRule : NameMap Rule) (dtrees : Array (DiscrTree Rule))
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
          match preprocessThm with | none => pure () | some preprocessThm => preprocessThm mvars pat
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
private partial def visit (depth : Nat) (preprocessThm : Option (Array Expr → Expr → MetaM Unit)) (nameToRule : NameMap Rule)
  (dtrees : Array (DiscrTree Rule))
  (boundVars : Std.HashSet FVarId)
  (matched : Std.HashSet (Name × List Expr))
  (e : Expr) : MetaM (Std.HashSet (Name × List Expr)) := do
  trace[Saturate] "Visiting {e}"
  -- Match
  let matched ← matchExpr preprocessThm nameToRule dtrees boundVars matched e
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
      let matched ← visit (depth + 1) preprocessThm nameToRule dtrees boundVars matched localDecl.type
      let matched ←
        match localDecl.value? with
        | none => pure matched
        | some v => visit (depth + 1) preprocessThm nameToRule dtrees boundVars matched v
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
    let matched ← args.foldlM (fun matched arg => visit (depth + 1) preprocessThm nameToRule dtrees boundVars matched arg) matched
    -- Visit the app
    visit (depth + 1) preprocessThm nameToRule dtrees boundVars matched f
  | .lam .. =>
    trace[Saturate] ".lam"
    lambdaLetTelescope e fun xs b => do
      let (boundVars, matched) ← visitBinders (depth + 1) boundVars matched xs
      visit (depth + 1) preprocessThm nameToRule dtrees boundVars matched b
  | .forallE .. => do
    trace[Saturate] ".forallE"
    forallTelescope e fun xs b => do
      let (boundVars, matched) ← visitBinders (depth + 1) boundVars matched xs
      visit (depth + 1) preprocessThm nameToRule dtrees boundVars matched b
  | .letE .. => do
    trace[Saturate] ".letE"
    lambdaLetTelescope e fun xs b => do
      let (boundVars, matched) ← visitBinders (depth + 1) boundVars matched xs
      visit (depth + 1) preprocessThm nameToRule dtrees boundVars matched b
  | .mdata _ b => do
    trace[Saturate] ".mdata"
    visit (depth + 1) preprocessThm nameToRule dtrees boundVars matched b
  | .proj _ _ b => do
    trace[Saturate] ".proj"
    visit (depth + 1) preprocessThm nameToRule dtrees boundVars matched b

def propConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``Iff, ``And, ``Or
]

def arithComparisonConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge
]

def exploreArithSubterms (f : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  if ¬ f.isConst then return #[]
  let constName := f.constName!
  if constName == ``Eq ∧ args.size == 3 then
    trace[Saturate] "Found `=`"
    pure #[args[1]!, args[2]!]
  else if constName ∈ propConsts ∧ args.size == 2 then
    trace[Saturate] "Found prop const: {f}"
    pure #[args[0]!, args[1]!]
  else if constName ∈ arithComparisonConsts ∧ args.size == 4 then
    trace[Saturate] "Found arith comparison: {f}"
    pure #[args[2]!, args[3]!]
  else
    pure #[]

/- Fast version of `visit`: we do not explore everything. -/
private partial def fastVisit
  (exploreSubterms : Expr → Array Expr → MetaM (Array Expr))
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (depth : Nat)
  (nameToRule : NameMap Rule)
  (dtrees : Array (DiscrTree Rule))
  (matched : Std.HashSet (Name × List Expr))
  (e : Expr) : MetaM (Std.HashSet (Name × List Expr)) := do
  trace[Saturate] "Visiting {e}"
  -- Match
  let matched ← matchExpr preprocessThm nameToRule dtrees Std.HashSet.empty matched e
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
    let visitRec := fastVisit exploreSubterms preprocessThm (depth + 1) nameToRule dtrees
    let subterms ← exploreSubterms f args
    subterms.foldlM visitRec matched
  | .lam ..
  | .forallE ..
  | .letE .. => do
    -- Do not go inside the foralls, the lambdas and the let expressions
    pure matched
  | .mdata _ b => do
    trace[Saturate] ".mdata"
    fastVisit exploreSubterms preprocessThm (depth + 1) nameToRule dtrees matched b
  | .proj _ _ _ => do
    trace[Saturate] ".proj"
    pure matched

/- The saturation tactic itself -/
def evalSaturate
  (sets : List Name)
  (exploreSubterms : Option (Expr → Array Expr → MetaM (Array Expr)) := none)
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (declsToExplore : Option (Array FVarId) := none)
  (exploreGoal : Bool := true) : TacticM (Array FVarId) := do
  Tactic.withMainContext do
  trace[Saturate] "sets: {sets}"
  -- Retrieve the rule sets
  let s := Saturate.Attribute.saturateAttr.ext.getState (← getEnv)
  let dtrees := Array.mk (sets.filterMap (fun set => s.rules.find? set))
  -- Get the local context
  let ctx ← Lean.MonadLCtx.getLCtx
  -- Explore the declarations
  let visit :=
    match exploreSubterms with
    | none => visit 0 preprocessThm s.nameToRule dtrees Std.HashSet.empty
    | some exploreSubterms => fastVisit exploreSubterms preprocessThm 0 s.nameToRule dtrees

  let decls ←
    match declsToExplore with
    | none => do pure (← ctx.getDecls).toArray
    | some decls => decls.mapM fun d => d.getDecl

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
  let matched ← do
    if exploreGoal then do pure (← visit matched (← Tactic.getMainTarget)).toArray else do pure matched.toArray
  -- Introduce the theorems in the context
  matched.mapIdxM fun i (thName, args) => do
    let th ← mkAppOptM thName (args.map some).toArray
    let thTy ← inferType th
    pure (← Utils.addDeclTac (.num (.str .anonymous "_h") i) th thTy (asLet := false)).fvarId!

elab "aeneas_saturate" : tactic => do
  let _ ← evalSaturate [`Aeneas.ScalarTac] none none

section Test
  local elab "aeneas_saturate_test" : tactic => do
    let _ ← evalSaturate [`Aeneas.Test] none none

  set_option trace.Saturate.attribute false
  @[aeneas_saturate (set := Aeneas.Test) (pattern := l.length)]
  theorem rule1 (α : Type u) (l : List α) : l.length ≥ 0 := by simp

  set_option trace.Saturate false

  /--
info: example
  (α : Type v)
  (l0 : List α)
  (l1 : List α)
  (l2 : List α)
  (l3 : List α)
  (l4 : List α)
  (l5 : List α)
  (x✝ : ∀ (l : List α), l.length ≤ l3.length)
  (_h.0 : l2.length ≥ 0)
  (_h.1 : l1.length ≥ 0)
  (_h.2 : (l0 ++ l1 ++ l2).length ≥ 0)
  (_h.3 : l0.length ≥ 0)
  (_h.4 : l4.length ≥ 0)
  (_h.5 : l5.length ≥ 0)
  (_h.6 : l3.length ≥ 0) :
  let _k := l4.length;
let _g := fun l => l.length + l5.length;
(l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length
  := by sorry
  -/
  #guard_msgs in
  set_option linter.unusedTactic false in
  theorem test1 {α : Type v} (l0 l1 l2 l3 l4 l5 : List α)
    (_ : ∀ (l : List α), l.length ≤ l3.length) :
    let _k := l4.length
    let _g := fun (l : List α) => l.length + l5.length
    (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length := by
    aeneas_saturate_test
    extract_goal1
    simp [Nat.add_assoc]

  namespace Test
    set_option trace.Saturate.attribute false
    @[local aeneas_saturate (set := Aeneas.Test) (pattern := l.length)]
    theorem rule2 (α : Type u) (l : List α) : 0 ≤ l.length := by simp

    /--
info: example
  (α : Type v)
  (l0 : List α)
  (l1 : List α)
  (l2 : List α)
  (l3 : List α)
  (l4 : List α)
  (l5 : List α)
  (x✝ : ∀ (l : List α), l.length ≤ l3.length)
  (_h.0 : (l0 ++ l1 ++ l2).length ≥ 0)
  (_h.1 : 0 ≤ l0.length)
  (_h.2 : l1.length ≥ 0)
  (_h.3 : 0 ≤ l3.length)
  (_h.4 : 0 ≤ l4.length)
  (_h.5 : l4.length ≥ 0)
  (_h.6 : 0 ≤ l2.length)
  (_h.7 : l3.length ≥ 0)
  (_h.8 : 0 ≤ (l0 ++ l1 ++ l2).length)
  (_h.9 : 0 ≤ l1.length)
  (_h.10 : l2.length ≥ 0)
  (_h.11 : 0 ≤ l5.length)
  (_h.12 : l5.length ≥ 0)
  (_h.13 : l0.length ≥ 0) :
  let _k := l4.length;
let _g := fun l => l.length + l5.length;
(l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length
  := by sorry
  -/
  #guard_msgs in
    set_option linter.unusedTactic false in
    theorem test1 {α : Type v} (l0 l1 l2 l3 l4 l5 : List α)
      (_ : ∀ (l : List α), l.length ≤ l3.length) :
      let _k := l4.length
      let _g := fun (l : List α) => l.length + l5.length
      (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length := by
      aeneas_saturate_test
      extract_goal1
      simp [Nat.add_assoc]

    attribute [- aeneas_saturate] rule2

    /--
info: example
  (α : Type v)
  (l0 : List α)
  (l1 : List α)
  (l2 : List α)
  (l3 : List α)
  (l4 : List α)
  (l5 : List α)
  (x✝ : ∀ (l : List α), l.length ≤ l3.length)
  (_h.0 : l2.length ≥ 0)
  (_h.1 : l3.length ≥ 0)
  (_h.2 : l1.length ≥ 0)
  (_h.3 : (l0 ++ l1 ++ l2).length ≥ 0)
  (_h.4 : l5.length ≥ 0)
  (_h.5 : l0.length ≥ 0)
  (_h.6 : l4.length ≥ 0) :
  let _k := l4.length;
let _g := fun l => l.length + l5.length;
(l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length
  := by sorry
  -/
  #guard_msgs in
    set_option linter.unusedTactic false in
    theorem test2 {α : Type v} (l0 l1 l2 l3 l4 l5 : List α)
      (_ : ∀ (l : List α), l.length ≤ l3.length) :
      let _k := l4.length
      let _g := fun (l : List α) => l.length + l5.length
      (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length := by
      aeneas_saturate_test
      extract_goal1
      simp [Nat.add_assoc]
  end Test

  /--
info: example
  (α : Type v)
  (l0 : List α)
  (l1 : List α)
  (l2 : List α)
  (l3 : List α)
  (l4 : List α)
  (l5 : List α)
  (x✝ : ∀ (l : List α), l.length ≤ l3.length)
  (_h.0 : l2.length ≥ 0)
  (_h.1 : l4.length ≥ 0)
  (_h.2 : (l0 ++ l1 ++ l2).length ≥ 0)
  (_h.3 : l0.length ≥ 0)
  (_h.4 : l5.length ≥ 0)
  (_h.5 : l1.length ≥ 0)
  (_h.6 : l3.length ≥ 0) :
  let _k := l4.length;
let _g := fun l => l.length + l5.length;
(l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length
  := by sorry
  -/
  #guard_msgs in
  set_option linter.unusedTactic false in
  theorem test3 {α : Type v} (l0 l1 l2 l3 l4 l5 : List α)
    (_ : ∀ (l : List α), l.length ≤ l3.length) :
    let _k := l4.length
    let _g := fun (l : List α) => l.length + l5.length
    (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length := by
    aeneas_saturate_test
    extract_goal1
    simp [Nat.add_assoc]

  /- Testing patterns which are propositions -/
  @[aeneas_saturate (set := Aeneas.Test) (pattern := x < y)]
  theorem rule2 (x y : Nat) : x < y ↔ y > x := by omega

end Test

end Saturate

end Aeneas
