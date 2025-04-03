import Aeneas.Saturate.Attribute

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic

namespace Aeneas

open Utils Extensions

namespace Saturate

open Attribute

structure DiagnosticsInfo where
  hits : Std.HashMap Name (Nat × Nat)

def DiagnosticsInfo.empty : DiagnosticsInfo := ⟨ Std.HashMap.empty ⟩

def DiagnosticsInfo.insertHit (info : DiagnosticsInfo) (name : Name) : DiagnosticsInfo :=
  match info.hits[name]? with
  | none => ⟨ info.hits.insert name (1, 0) ⟩
  | some (hit, used) => ⟨ info.hits.insert name (hit + 1, used) ⟩

def DiagnosticsInfo.insertUsed (info : DiagnosticsInfo) (name : Name) : DiagnosticsInfo :=
  match info.hits[name]? with
  | none => ⟨ info.hits.insert name (0, 1) ⟩
  | some (hit, used) => ⟨ info.hits.insert name (hit, used + 1) ⟩

def DiagnosticsInfo.insertHitRules (info : DiagnosticsInfo) (rules : Array Rule) : DiagnosticsInfo :=
  rules.foldl (fun info rule => info.insertHit rule.thName) info

def DiagnosticsInfo.toArray (info : DiagnosticsInfo) : Array String :=
  let hits := info.hits.toList
  let hits := (hits.mergeSort (fun (_, hit0, used0) (_, hit1, used1) => hit0 + used0 ≤ hit1 + used1)).reverse
  let hits := hits.toArray
  hits.map (fun (name, (hit, used)) => s!"{name}: {hit} hits, {used} uses")

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
  (dinfo : DiagnosticsInfo)
  (matched : Std.HashSet (Name × List Expr)) (e : Expr) :
  MetaM (DiagnosticsInfo × Std.HashSet (Name × List Expr)) := do
  trace[Saturate] "Matching: {e}"
  dtrees.foldlM (fun (dinfo, matched) dtree => do
    let exprs ← dtree.getMatch e
    let dinfo := dinfo.insertHitRules exprs
    trace[Saturate] "Potential matches: {exprs}"
    -- Check each expression
    (exprs.foldlM fun (dinfo, matched) rule => do
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
              let dinfo := dinfo.insertUsed rule.thName
              let (args, allFVars) ← mvars.foldrM (fun arg (args, hs) => do
                  let arg ← instantiateMVars arg
                  let hs ← getFVarIds arg hs
                  pure (arg :: args, hs)
                ) ([], Std.HashSet.empty)
              if boundVars.all (fun fvar => ¬ allFVars.contains fvar) then
                -- Ok: save the theorem
                trace[Saturate] "Matched with: {rule.thName} {args}"
                pure (dinfo, matched.insert (rule.thName, args))
              else
                -- Ignore
                trace[Saturate] "Didn't match"
                pure (dinfo, matched)
            else
              -- Didn't match, leave the set of matches unchanged
              trace[Saturate] "Didn't match"
              pure (dinfo, matched)
          else
            -- Didn't match, leave the set of matches unchanged
              trace[Saturate] "Types didn't match"
              pure (dinfo, matched)
        else
          -- The rule is not active
          trace[Saturate] "The rule is not active"
          pure (dinfo, matched)
      else
        -- The rule is not active
        trace[Saturate] "The rule is not active"
        pure (dinfo, matched)) (dinfo, matched)
  ) (dinfo, matched)

/- Recursively explore a term -/
private partial def visit (depth : Nat) (preprocessThm : Option (Array Expr → Expr → MetaM Unit)) (nameToRule : NameMap Rule)
  (dtrees : Array (DiscrTree Rule))
  (boundVars : Std.HashSet FVarId)
  (dinfo : DiagnosticsInfo)
  (matched : Std.HashSet (Name × List Expr))
  (e : Expr) : MetaM (DiagnosticsInfo × Std.HashSet (Name × List Expr)) := do
  trace[Saturate] "Visiting {e}"
  -- Match
  let (dinfo, matched) ← matchExpr preprocessThm nameToRule dtrees boundVars dinfo matched e
  -- Recurse
  let visitBinders
    (depth : Nat)
    (boundVars : Std.HashSet FVarId)
    (dinfo : DiagnosticsInfo)
    (matched : Std.HashSet (Name × List Expr)) (xs: Array Expr) :
    MetaM (Std.HashSet FVarId × DiagnosticsInfo × (Std.HashSet (Name × List Expr))) := do
    -- Visit the type of the binders, as well as the bodies
    xs.foldlM (fun (boundVars, dinfo, matched) x => do
      let fvarId := x.fvarId!
      let localDecl ← fvarId.getDecl
      let boundVars := boundVars.insert fvarId
      let (dinfo, matched) ← visit (depth + 1) preprocessThm nameToRule dtrees boundVars dinfo matched localDecl.type
      let (dinfo, matched) ←
        match localDecl.value? with
        | none => pure (dinfo, matched)
        | some v => visit (depth + 1) preprocessThm nameToRule dtrees boundVars dinfo matched v
      pure (boundVars, dinfo, matched)
      ) (boundVars, dinfo, matched)
  let e := e.consumeMData
  match e with
  | .bvar _
  | .fvar _
  | .mvar _
  | .sort _
  | .lit _
  | .const _ _ =>
    trace[Saturate] "Stop: bvar, fvar, etc."
    pure (dinfo, matched)
  | .app .. => do e.withApp fun f args => do
    trace[Saturate] ".app"
    -- Visit the args
    let (dinfo, matched) ← args.foldlM (fun (dinfo, matched) arg =>
      visit (depth + 1) preprocessThm nameToRule dtrees boundVars dinfo matched arg) (dinfo, matched)
    -- Visit the app
    visit (depth + 1) preprocessThm nameToRule dtrees boundVars dinfo matched f
  | .lam .. =>
    trace[Saturate] ".lam"
    lambdaLetTelescope e fun xs b => do
      let (boundVars, dinfo, matched) ← visitBinders (depth + 1) boundVars dinfo matched xs
      visit (depth + 1) preprocessThm nameToRule dtrees boundVars dinfo matched b
  | .forallE .. => do
    trace[Saturate] ".forallE"
    forallTelescope e fun xs b => do
      let (boundVars, dinfo, matched) ← visitBinders (depth + 1) boundVars dinfo matched xs
      visit (depth + 1) preprocessThm nameToRule dtrees boundVars dinfo matched b
  | .letE .. => do
    trace[Saturate] ".letE"
    lambdaLetTelescope e fun xs b => do
      let (boundVars, dinfo, matched) ← visitBinders (depth + 1) boundVars dinfo matched xs
      visit (depth + 1) preprocessThm nameToRule dtrees boundVars dinfo matched b
  | .mdata _ b => do
    trace[Saturate] ".mdata"
    visit (depth + 1) preprocessThm nameToRule dtrees boundVars dinfo matched b
  | .proj _ _ b => do
    trace[Saturate] ".proj"
    visit (depth + 1) preprocessThm nameToRule dtrees boundVars dinfo matched b

def propConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``Iff, ``And, ``Or
]

def arithComparisonConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge
]

def arithOpArity6 : Std.HashSet Name := Std.HashSet.ofList [
  ``HShiftRight.hShiftRight, ``HShiftLeft.hShiftLeft, ``HPow.hPow
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
  else if constName ∈ arithOpArity6 ∧ args.size == 6 then
    trace[Saturate] "Found arith op of arity 6: {f}"
    pure #[args[4]!, args[5]!]
  else
    pure #[]

/- Fast version of `visit`: we do not explore everything. -/
private partial def fastVisit
  (exploreSubterms : Expr → Array Expr → MetaM (Array Expr))
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (depth : Nat)
  (nameToRule : NameMap Rule)
  (dtrees : Array (DiscrTree Rule))
  (dinfo : DiagnosticsInfo)
  (matched : Std.HashSet (Name × List Expr))
  (e : Expr) : MetaM (DiagnosticsInfo × Std.HashSet (Name × List Expr)) := do
  trace[Saturate] "Visiting {e}"
  -- Match
  let (dinfo, matched) ← matchExpr preprocessThm nameToRule dtrees Std.HashSet.empty dinfo matched e
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
    pure (dinfo, matched)
  | .app .. => do e.withApp fun f args => do
    trace[Saturate] ".app"
    let visitRec := fastVisit exploreSubterms preprocessThm (depth + 1) nameToRule dtrees
    let subterms ← exploreSubterms f args
    subterms.foldlM (fun (dinfo, matched) => visitRec dinfo matched) (dinfo, matched)
  | .lam ..
  | .forallE ..
  | .letE .. => do
    -- Do not go inside the foralls, the lambdas and the let expressions
    pure (dinfo, matched)
  | .mdata _ b => do
    trace[Saturate] ".mdata"
    fastVisit exploreSubterms preprocessThm (depth + 1) nameToRule dtrees dinfo matched b
  | .proj _ _ _ => do
    trace[Saturate] ".proj"
    pure (dinfo, matched)

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

  let (dinfo, matched) ← decls.foldlM (fun (dinfo, matched) (decl : LocalDecl) => do
    trace[Saturate] "Exploring local decl: {decl.userName}"
    /- We explore both the type, the expresion and the body (if there is) -/
    let (dinfo, matched) ← visit dinfo matched decl.type
    let (dinfo, matched) ← visit dinfo matched decl.toExpr
    match decl.value? with
    | none => pure (dinfo, matched)
    | some value => visit dinfo matched value) (DiagnosticsInfo.empty, Std.HashSet.empty)
  -- Explore the goal
  trace[Saturate] "Exploring the goal"
  let (dinfo, matched) ← do
    if exploreGoal then do pure (← visit dinfo matched (← Tactic.getMainTarget)) else do pure (dinfo, matched)
  let matched := matched.toArray
  -- Introduce the theorems in the context
  let matched ← matched.mapIdxM fun i (thName, args) => do
    let th ← mkAppOptM thName (args.map some).toArray
    let thTy ← inferType th
    pure (← Utils.addDeclTac (.num (.str .anonymous "_h") i) th thTy (asLet := false)).fvarId!
  -- Display the diagnostics information
  trace[Saturate.diagnostics] "Saturate diagnostics info: {dinfo.toArray}"
  -- Return
  pure matched

elab "aeneas_saturate" : tactic => do
  let _ ← evalSaturate [`Aeneas.ScalarTac] none none

section Test
  local elab "aeneas_saturate_test" : tactic => do
    let _ ← evalSaturate [`Aeneas.Test] none none

  set_option trace.Saturate.attribute false
  @[local aeneas_saturate (set := Aeneas.Test) (pattern := l.length)]
  theorem rule1 (α : Type u) (l : List α) : l.length ≥ 0 := by simp

  set_option trace.Saturate false

/-
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
  set_option trace.Saturate.diagnostics true in
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
-/
end Test

end Saturate

end Aeneas
