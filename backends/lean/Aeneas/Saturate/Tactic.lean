import Aeneas.Saturate.Attribute

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic

namespace Aeneas

open Utils Extensions

namespace Saturate

open Attribute

structure Config where
  /- If `true` visit the proof terms.

     We consider as proof terms the expressions whose type's type is `Prop`.
     Ex.: `... : a + b ≤ 3`
  -/
  visitProofTerms : Bool := false

structure DiagnosticsInfo where
  hits : Std.HashMap Name (Nat × Nat)

def DiagnosticsInfo.empty : DiagnosticsInfo := ⟨ Std.HashMap.emptyWithCapacity ⟩

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

structure State where
  dinfo : DiagnosticsInfo
  matched : Std.HashSet (Name × List Expr)

def State.insertHitRules (s : State) (rules : Array Rule) : State :=
  { s with dinfo := s.dinfo.insertHitRules rules }

def State.insertUsed (s : State) (name : Name) : State :=
  { s with dinfo := s.dinfo.insertUsed name }

def State.insertMatch (s : State) (name : Name) (args : List Expr) : State :=
  { s with matched := s.matched.insert (name, args) }

def State.empty : State := ⟨ DiagnosticsInfo.empty, Std.HashSet.emptyWithCapacity ⟩

inductive LeftOrRight where
| left | right

inductive AssumPath where
| asm (asm : FVarId)
| conj (dir : LeftOrRight) (p : AssumPath)

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
  (state : State) (e : Expr) :
  MetaM State := do
  trace[Saturate.explore] "Matching: {e}"
  dtrees.foldlM (fun state dtree => do
    let exprs ← dtree.getMatch e
    let state := state.insertHitRules exprs
    trace[Saturate.explore] "Potential matches: {exprs}"
    -- Check each expression
    (exprs.foldlM fun state rule => do
      trace[Saturate.explore] "Checking potential match: {rule}"
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
          trace[Saturate.explore] "Checking if defEq:\n- pat: {pat}\n- expression: {e}"
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
              trace[Saturate.explore] "defEq"
              -- It matched! Check the variables which appear in the arguments
              let state := state.insertUsed rule.thName
              let (args, allFVars) ← mvars.foldrM (fun arg (args, hs) => do
                  let arg ← instantiateMVars arg
                  let hs ← getFVarIds arg hs
                  pure (arg :: args, hs)
                ) ([], Std.HashSet.emptyWithCapacity)
              if boundVars.all (fun fvar => ¬ allFVars.contains fvar) then
                -- Ok: save the theorem
                trace[Saturate.explore] "Matched with: {rule.thName} {args}"
                pure (state.insertMatch rule.thName args)
              else
                -- Ignore
                trace[Saturate.explore] "Didn't match"
                pure state
            else
              -- Didn't match, leave the set of matches unchanged
              trace[Saturate.explore] "Didn't match"
              pure state
          else
            -- Didn't match, leave the set of matches unchanged
              trace[Saturate.explore] "Types didn't match"
              pure state
        else
          -- The rule is not active
          trace[Saturate.explore] "The rule is not active"
          pure state
      else
        -- The rule is not active
        trace[Saturate.explore] "The rule is not active"
        pure state) state
  ) state

/- Recursively explore a term -/
private partial def visit (config : Config)
  (path : Option AssumPath)
  (depth : Nat)
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (nameToRule : NameMap Rule)
  (dtrees : Array (DiscrTree Rule))
  (boundVars : Std.HashSet FVarId)
  (state : State) (e : Expr)
  : MetaM State := do
  trace[Saturate.explore] "Visiting {e}"
  -- Match
  let state ← matchExpr preprocessThm nameToRule dtrees boundVars state e
  -- Recurse
  let visitBinders
    (depth : Nat)
    (boundVars : Std.HashSet FVarId)
    (state : State) (xs: Array Expr) :
    MetaM (Std.HashSet FVarId × State) := do
    -- Visit the type of the binders, as well as the bodies
    xs.foldlM (fun (boundVars, state) x => do
      let fvarId := x.fvarId!
      let localDecl ← fvarId.getDecl
      let boundVars := boundVars.insert fvarId
      let state ← visit config none (depth + 1) preprocessThm nameToRule dtrees boundVars state localDecl.type
      let state ←
        match localDecl.value? with
        | none => pure state
        | some v => visit config none (depth + 1) preprocessThm nameToRule dtrees boundVars state v
      pure (boundVars, state)
      ) (boundVars, state)
  let e := e.consumeMData
  match e with
  | .bvar _
  | .fvar _
  | .mvar _
  | .sort _
  | .lit _
  | .const _ _ =>
    trace[Saturate.explore] "Stop: bvar, fvar, etc."
    pure state
  | .app .. => do e.withApp fun f args => do
    trace[Saturate.explore] ".app"
    /- Check if this is a conjunction and we know the path to the current sub-expression (because it is a conjunct
       in an assumption) -/
    if path.isSome ∧ f.isConst ∧ f.constName! == ``And ∧ args.size == 2 then do
      -- This is a conjunction
      let some path := path
        | throwError "Unreachable"
      let state ← visit config (some (.conj .left path)) (depth + 1) preprocessThm nameToRule dtrees boundVars state (args[0]!)
      let state ← visit config (some (.conj .right path)) (depth + 1) preprocessThm nameToRule dtrees boundVars state (args[1]!)
      pure state
    else
      -- Filter the args to ignore proof terms
      let args ← args.filterM fun arg => do
        let ty ← inferType (← inferType arg)
        if ty.isProp then pure false
        else pure true
      -- Visit the args
      let state ← args.foldlM (fun state arg =>
        visit config none (depth + 1) preprocessThm nameToRule dtrees boundVars state arg) state
      -- Visit the app
      visit config none (depth + 1) preprocessThm nameToRule dtrees boundVars state f
  | .lam .. =>
    trace[Saturate.explore] ".lam"
    lambdaLetTelescope e fun xs b => do
      let (boundVars, state) ← visitBinders (depth + 1) boundVars state xs
      visit config none (depth + 1) preprocessThm nameToRule dtrees boundVars state b
  | .forallE .. => do
    trace[Saturate.explore] ".forallE"
    forallTelescope e fun xs b => do
      let (boundVars, state) ← visitBinders (depth + 1) boundVars state xs
      visit config none (depth + 1) preprocessThm nameToRule dtrees boundVars state b
  | .letE .. => do
    trace[Saturate.explore] ".letE"
    lambdaLetTelescope e fun xs b => do
      let (boundVars, state) ← visitBinders (depth + 1) boundVars state xs
      visit config path (depth + 1) preprocessThm nameToRule dtrees boundVars state b
  | .mdata _ b => do
    trace[Saturate.explore] ".mdata"
    visit config path (depth + 1) preprocessThm nameToRule dtrees boundVars state b
  | .proj _ _ b => do
    trace[Saturate.explore] ".proj"
    visit config none (depth + 1) preprocessThm nameToRule dtrees boundVars state b

def arithOpArity3 : Std.HashSet Name := Std.HashSet.ofList [
  ``Nat.cast, ``Int.cast
]

def propConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``Iff, ``And, ``Or
]

def arithComparisonConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge
]

def arithOpArity6 : Std.HashSet Name := Std.HashSet.ofList [
  ``HShiftRight.hShiftRight, ``HShiftLeft.hShiftLeft,
  ``HPow.hPow, ``HMod.hMod, ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv
]

def exploreArithSubterms (f : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  if ¬ f.isConst then return #[]
  let constName := f.constName!
  if constName == ``Eq ∧ args.size == 3 then
    trace[Saturate.explore] "Found `=`"
    pure #[args[1]!, args[2]!]
  else if constName ∈ arithOpArity3 ∧ args.size == 3 then
    pure #[args[2]!]
  else if constName ∈ propConsts ∧ args.size == 2 then
    trace[Saturate.explore] "Found prop const: {f}"
    pure #[args[0]!, args[1]!]
  else if constName ∈ arithComparisonConsts ∧ args.size == 4 then
    trace[Saturate.explore] "Found arith comparison: {f}"
    pure #[args[2]!, args[3]!]
  else if constName ∈ arithOpArity6 ∧ args.size == 6 then
    trace[Saturate.explore] "Found arith op of arity 6: {f}"
    pure #[args[4]!, args[5]!]
  else
    pure #[]

/- Fast version of `visit`: we do not explore everything. -/
private partial def fastVisit
  (path : Option AssumPath)
  (exploreSubterms : Expr → Array Expr → MetaM (Array Expr))
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (depth : Nat)
  (nameToRule : NameMap Rule)
  (dtrees : Array (DiscrTree Rule))
  (state : State)
  (e : Expr) : MetaM State := do
  trace[Saturate.explore] "Visiting {e}"
  -- Match
  let state ← matchExpr preprocessThm nameToRule dtrees Std.HashSet.emptyWithCapacity state e
  -- Recurse
  let e := e.consumeMData
  match e with
  | .bvar _
  | .fvar _
  | .mvar _
  | .sort _
  | .lit _
  | .const _ _ =>
    trace[Saturate.explore] "Stop: bvar, fvar, etc."
    pure state
  | .app .. => do e.withApp fun f args => do
    trace[Saturate.explore] ".app"
    let visitRec path := fastVisit path exploreSubterms preprocessThm (depth + 1) nameToRule dtrees
    let subterms ← exploreSubterms f args
    /- Check if this is a conjunction and we know the path to the current sub-expression (because it is a conjunct
       in an assumption) -/
    if path.isSome ∧ f.isConst ∧ f.constName! == ``And ∧ subterms.size == 2 then do
      -- This is a conjunction
      let some path := path
        | throwError "Unreachable"
      let state ← visitRec (some (.conj .left path)) state subterms[0]!
      let state ← visitRec (some (.conj .right path)) state subterms[1]!
      pure state
    else
      subterms.foldlM (fun state => visitRec none state) state
  | .lam ..
  | .forallE ..
  | .letE .. => do
    -- Do not go inside the foralls, the lambdas and the let expressions
    pure state
  | .mdata _ b => do
    trace[Saturate.explore] ".mdata"
    fastVisit path exploreSubterms preprocessThm (depth + 1) nameToRule dtrees state b
  | .proj _ _ _ => do
    trace[Saturate.explore] ".proj"
    pure state

/- The saturation tactic itself -/
partial def evalSaturate {α}
  (config : Config)
  (sets : List Name)
  (exploreSubterms : Option (Expr → Array Expr → MetaM (Array Expr)) := none)
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (declsToExplore : Option (Array FVarId) := none)
  (exploreAssumptions : Bool := true)
  (exploreTarget : Bool := true)
  (next : Array FVarId → TacticM α)
  : TacticM α
  := do
  Tactic.withMainContext do
  trace[Saturate] "sets: {sets}"
  -- Retrieve the rule sets
  let s := Saturate.Attribute.saturateAttr.ext.getState (← getEnv)
  let dtrees := Array.mk (sets.filterMap (fun set => s.rules.find? set))
  -- Get the local context
  let ctx ← Lean.MonadLCtx.getLCtx
  -- Explore
  let visit (path : Option AssumPath) state expr :=
    match exploreSubterms with
    | none => visit config path 0 preprocessThm s.nameToRule dtrees Std.HashSet.emptyWithCapacity state expr
    | some exploreSubterms => fastVisit path exploreSubterms preprocessThm 0 s.nameToRule dtrees state expr

  -- Explore the assumptions
  trace[Saturate] "Exploring the assumptions"
  let state := State.empty
  let state ← do
    if exploreAssumptions then do
      let decls ←
        match declsToExplore with
        | none => do pure (← ctx.getDecls).toArray
        | some decls => decls.mapM fun d => d.getDecl
      decls.foldlM (fun state (decl : LocalDecl) => do
        trace[Saturate] "Exploring local decl: {decl.userName}"
        /- We explore both the type, the expresion and the body (if there is) -/
        let state ← visit (some (.asm decl.fvarId)) state decl.type
        let state ← visit none state decl.toExpr
        match decl.value? with
        | none => pure state
        | some value => visit none state value) state
    else pure state

  -- Explore the target
  trace[Saturate] "Exploring the target"
  let state ← do
    if exploreTarget then do pure (← visit none state (← Tactic.getMainTarget)) else do pure state

  /- Introduce the theorems in the context. We wrote the function in CPS on purpose (this
     helps prevent bugs where the local context is not the one we expect) -/
  trace[Saturate] "Finished exploring the goal. Matched:\n{state.matched.toList}"
  let matched := state.matched.toArray
  let fvars : Array FVarId := #[]
  let rec add (i : Nat) (fvars : Array FVarId) (f : Array FVarId → TacticM α) :
    TacticM α := do
    if i < matched.size then do
      withMainContext do
      let (thName, args) := matched[i]!
      trace[Saturate] "Adding: {thName}({args}).\nGoal: {← getMainGoal}"
      let th : Option Expr ← do
        try
          /- It sometimes happens that the instantiation is invalid, so `mkAppOptM`
            may raise an exception, in which case we simply skip the pattern. -/
          pure (some (← mkAppOptM thName (args.map some).toArray))
        catch e =>
          trace[Saturate] "Error: {e.toMessageData}"
          pure none
      -- The application worked: introduce the assumption in the context
      if let some th := th then
        let thTy ← inferType th
        -- TODO: check that we don't add the same assumption twice
        Utils.addDeclTac (.num (.str .anonymous "_h") i) th thTy (asLet := false)
          fun x =>
          let fvars := fvars.push x.fvarId!
          add (i + 1) fvars f
      else
        -- Simply ignore the match
        add (i + 1) fvars f
    else f fvars

  --
  add 0 fvars fun matched => do
    trace[Saturate] "Introduced the assumptions in the context"

    -- Display the diagnostics information
    trace[Saturate.diagnostics] "Saturate diagnostics info: {state.dinfo.toArray}"
    -- Continue
    next matched

elab "aeneas_saturate" : tactic => do
  let _ ← evalSaturate {} [`Aeneas.ScalarTac] none none
    (declsToExplore := none)
    (exploreAssumptions := true)
    (exploreTarget := true) (fun _ => pure ())

section Test
  local elab "aeneas_saturate_test" : tactic => do
    let _ ← evalSaturate {} [`Aeneas.Test] none none
      (declsToExplore := none)
      (exploreAssumptions := true)
      (exploreTarget := true) (fun _ => pure ())

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
