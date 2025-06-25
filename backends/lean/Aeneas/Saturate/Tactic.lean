import Aeneas.Saturate.Attribute

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic

namespace Aeneas

open Utils Extensions

namespace Saturate

open Attribute

structure Config where
  /- The number of addiotional exploration passes we do to instantiate rules
     with several patterns (i.e., preconditions). Note that this doesn't count
     the initial pass we do through the whole context, meaning that if this
     parameter is equal to 0, `saturate` will still successfully instantiate
     rules which only have one pattern. -/
  saturationPasses : Nat := 3
  /- If `true` visit the proof terms.

    We consider as proof terms the expressions whose type's type is `Prop`.
    Ex.: `... : a + b ≤ 3`
  -/
  visitProofTerms : Bool := false
  /- If `true`, we dive into the binders (ex.: `∀ x, ...`)-/
  visitBoundExpressions : Bool := false

structure VisitConfig extends Config where
  matchWithRules : Bool
  matchWithPartialMatches : Bool

structure PartialMatch where
  numBinders : Nat
  -- The remaining patterns to match, including the current one
  patterns : List Pattern
  -- The substitution from free variable to expression
  subst : Array (Option Expr)
  thName : Name
  deriving Inhabited, BEq

instance : ToFormat PartialMatch where
  format x := f!"({x.numBinders}, {x.patterns}, {x.thName}, {x.subst})"

instance : ToMessageData PartialMatch where
  toMessageData x := m!"({x.numBinders}, {x.patterns}, {x.thName}, {x.subst})"

structure DiagnosticsInfo where
  hits: Nat
  used : Nat

structure Diagnostics where
  hits : Std.HashMap Name DiagnosticsInfo

def Diagnostics.empty : Diagnostics := ⟨ Std.HashMap.emptyWithCapacity ⟩

def Diagnostics.insertHit (diagnostics : Diagnostics) (name : Name) : Diagnostics :=
  match diagnostics.hits[name]? with
  | none => ⟨ diagnostics.hits.insert name { hits:= 1, used := 0 } ⟩
  | some info => ⟨ diagnostics.hits.insert name { info with hits := info.hits + 1 } ⟩

def Diagnostics.insertUsed (diagnostics : Diagnostics) (name : Name) : Diagnostics :=
  match diagnostics.hits[name]? with
  | none => ⟨ diagnostics.hits.insert name { hits:= 1, used := 0 } ⟩ -- This shouldn't happen
  | some info => ⟨ diagnostics.hits.insert name { info with used := info.used + 1} ⟩

def Diagnostics.insertHitRules (info : Diagnostics) (rules : Array Rule) : Diagnostics :=
  rules.foldl (fun info rule => info.insertHit rule.thName) info

def Diagnostics.toArray (info : Diagnostics) : Array String :=
  let hits := info.hits.toList
  let hits := (hits.mergeSort (fun (_, info0) (_, info1) => info0.hits + info0.used ≤ info1.hits + info1.used)).reverse
  let hits := hits.toArray
  hits.map (fun (name, info) => s!"{name}: {info.hits} hits, {info.used} uses")

inductive LeftOrRight where
| left | right

inductive AsmPath where
| asm (asm : FVarId)
| conj (dir : LeftOrRight) (p : AsmPath)

def AsmPath.format (p : AsmPath) : Format :=
  match p with
  | .asm fvarId => f!"{Expr.fvar fvarId}"
  | .conj .left p => f!"{p.format}.left"
  | .conj .right p => f!"{p.format}.right"

instance : ToFormat AsmPath where
  format x := AsmPath.format x

instance : ToMessageData AsmPath where
  toMessageData x := m!"({AsmPath.format x})"

structure State where
  /- The sets of rules -/
  rules : Array Rules
  /- The partial matches -/
  pmatches : DiscrTree PartialMatch
  /- Diagnostic information for debugging -/
  diagnostics : Diagnostics
  /- The fully matched rules: we directly store the instantiated theorems -/
  matched : Std.HashSet Expr
  /- The set of encountered assumptions.
     We store a map from expression to path because we may need to use those
     assumptions to instantiate some other theorems.
   -/
  assumptions : Std.HashMap Expr AsmPath
  /- Do not introduce a theorem if its conclusion is already in the set -/
  ignore : Std.HashSet Expr

def State.insertHitRules (s : State) (rules : Array Rule) : State :=
  { s with diagnostics := s.diagnostics.insertHitRules rules }

def State.insertUsed (s : State) (name : Name) : State :=
  { s with diagnostics := s.diagnostics.insertUsed name }

def State.insertMatch (s : State) (e : Expr) : State :=
  { s with matched := s.matched.insert e }

/- Note that we shouldn't insert assumptions which contain bound variables. This should
   be prevented by the fact that when diving into expressions containing binders, we
   set the path to `none`. -/
def State.insertAssumption (s : State) (path : Option AsmPath) (e : Expr) : State :=
  match path with
  | some path =>
    -- We insert assumptions only if they do not contain bound vars
    { s with assumptions := s.assumptions.insert e path }
  | none => s

def State.new
  (rules : Array Rules)
  (pmatches : DiscrTree PartialMatch := DiscrTree.empty)
  (diagnostics : Diagnostics := Diagnostics.empty)
  (matched : Std.HashSet Expr := Std.HashSet.emptyWithCapacity)
  (assumptions : Std.HashMap Expr AsmPath := Std.HashMap.emptyWithCapacity)
  (ignore : Std.HashSet Expr := Std.HashSet.emptyWithCapacity) : State :=
  { rules, pmatches, diagnostics, matched, assumptions, ignore }

def mkExprFromPath (path : AsmPath) : MetaM Expr := do
  match path with
  | .asm asm => pure (Expr.fvar asm)
  | .conj dir p =>
    let p ← mkExprFromPath p
    let dir :=
      match dir with
      | .left => ``And.left
      | .right => ``And.right
    mkAppOptM dir #[none, none, some p]

def State.insertPartialMatch (state : State)
  (boundVars : Std.HashSet FVarId)
  (pmatch : PartialMatch) : MetaM State := do
  withTraceNode `Saturate (fun _ => pure m!"insertPartialMatch") do
  trace[Saturate.insertPartialMatch] "insertPartialMatch: {pmatch}"
  let mut state := state
  /- Check if there remains patterns: if no then the match is total -/
  match pmatch.patterns with
  | [] =>
    trace[Saturate.insertPartialMatch] "Total match"
    -- This is a total match: retrieve the subst
    let subst ←
      try
        pmatch.subst.mapM fun e =>
          match e with | some e => pure e | none => throwError "Unexpected"
      catch _ =>
        trace[Saturate.insertPartialMatch] "Internal error: invalid total match"
        return state
    -- Check that no bound vars appear within the substitution (otherwise we abort)
    let allFVars ← subst.foldrM (fun arg hs => do
        getFVarIds arg hs
      ) Std.HashSet.emptyWithCapacity
    if ¬ boundVars.all (fun fvar => ¬ allFVars.contains fvar) then
      return state
    -- Instantiate the theorem
    trace[Saturate.insertPartialMatch] "Instantiating: {pmatch.thName}({subst})."
    let thm ←
      try
        /- It sometimes happens that the instantiation is invalid, so `mkAppOptM`
          may raise an exception, in which case we simply skip the pattern. -/
        mkAppOptM pmatch.thName (subst.map some)
      catch e =>
        trace[Saturate.insertPartialMatch] "Error: {e.toMessageData}"
        return state
    -- Register the theorem
    state := state.insertUsed pmatch.thName
    state := state.insertMatch thm
    pure state
  | pattern :: _ =>
    trace[Saturate.insertPartialMatch] "Partial match"
    -- This is a partial match: register it in the discr tree
    -- Introduce meta-variables for all the variables bound in the pattern
    let (mvars, _, patWithMetas) ← lambdaMetaTelescope pattern.pattern (some pattern.boundVars.size)
    -- Instantiate the meta-variables which are already known
    for (i, mvar) in mvars.mapIdx fun i mvar => (i, mvar) do
      let mvar := mvar.mvarId!
      let vid := pattern.boundVars[i]!
      match pmatch.subst[vid]! with
      | none => pure ()
      | some e => mvar.assign e
    -- Propagate the instantiation in the pattern
    let key ← instantiateMVars patWithMetas
    -- Store the partial match
    pure { state with pmatches := ← state.pmatches.insert key pmatch }

def checkIfPatDefEq (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (pat : Expr) (numBinders : Nat) (e : Expr) : MetaM (Option (Array Expr)) := do
  withTraceNode `Saturate (fun _ => pure m!"checkIfPatDefEq") do
  -- Strip the binders, introduce meta-variables at the same time, and match
  let (mvars, _, pat) ← lambdaMetaTelescope pat (some numBinders)
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
  if ¬ (← isDefEq pat_ty e_ty) then
    trace[Saturate.explore] "Types didn't match"; return none
  if ¬ (← isDefEq pat e) then
    trace[Saturate.explore] "Didn't match"
    return none
  return (some mvars)

def matchExprWithRules
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (path : Option AsmPath)
  (boundVars : Std.HashSet FVarId)
  (state : State) (e : Expr) :
  MetaM State := do
  withTraceNode `Saturate (fun _ => pure m!"matchExprWithRules") do
  let mut state := state
  for rules in state.rules do
    let exprs ← rules.rules.getMatch e
    state := state.insertHitRules exprs
    trace[Saturate.explore] "Potential matches: {exprs}"
    -- Check each expression
    for rule in exprs do
      trace[Saturate.explore] "Checking potential match: {rule}"
      -- Check if the theorem is still active
      if rules.deactivatedRules.contains rule.thName then
        trace[Saturate.explore] "The rule is not active"; continue
      -- Retrieve the first pattern
      let (pat, patterns) ← do
        match rule.patterns.toList with
        | [] => throwError "Unexpected: rules should have at least one pattern"
        | pat :: patterns => pure (pat, patterns)
      /- Quick check: if the pattern is for a precondition and the path is unknown, then we can abort:
          we wouldn't know how to instantiate the pre-condition -/
      unless pat.instVar.isNone ∨ path.isSome do continue
      -- Introduce meta-variables for the universes
      let info ← getConstInfo rule.thName
      let mvarLevels ← mkFreshLevelMVarsFor info
      let patExpr := pat.pattern.instantiateLevelParams info.levelParams mvarLevels
      -- Match (doing this also introduces meta-variables for the bound variables)
      let some mvars ← checkIfPatDefEq preprocessThm patExpr rule.numBinders e
        | continue
      trace[Saturate.explore] "defEq"
      /- It matched! Compute the substitution from free variables to expressions
        (for the variables which have been instantiated) -/
      let subst ← mvars.mapM fun mvar => do
        let arg ← instantiateMVars mvar
        if arg.isMVar then pure none
        else pure (some arg)
      /- Check if the pattern is for an assumption, and add it to the substitution -/
      let subst ← do
        match pat.instVar with
        | none => pure subst
        | some v =>
          if subst[v]!.isSome then
            logError "Internal error: assumption already instantiated"
            continue
          else
            let some path := path | throwError "Unreachable"
            pure (subst.set! v (← mkExprFromPath path))
      -- Create the partial match (we check whether it's actually a total match when registering it)
      let pmatch : PartialMatch := {
        numBinders := rule.numBinders,
        patterns,
        subst,
        thName := rule.thName
      }
      -- Register the partial match (this may introduce a theorem to instantiate if the match is actually total)
      state ← state.insertPartialMatch boundVars pmatch
  pure state

def matchExprWithPartialMatches
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (path : Option AsmPath)
  (boundVars : Std.HashSet FVarId)
  (state : State) (e : Expr) :
  MetaM State := do
  withTraceNode `Saturate (fun _ => pure m!"matchExprWithPartialMatches") do
  let mut state := state
  let exprs ← state.pmatches.getMatch e
  trace[Saturate.explore] "Potential matches: {exprs}"
  -- Check each expression
  for pmatch in exprs do
    trace[Saturate.explore] "Checking potential match: {pmatch}"
    -- Retrieve the first pattern
    let (pat, patterns) ← do
      match pmatch.patterns with
      | [] => throwError "Unexpected: rules should have at least one pattern"
      | pat :: patterns => pure (pat, patterns)
    /- Quick check: if the pattern is for a precondition and the path is unknown, then we can abort:
        we wouldn't know how to instantiate the pre-condition -/
    unless pat.instVar.isNone ∨ path.isSome do continue
    -- Match (doing this also introduces meta-variables for the bound variables)
    let some mvars ← checkIfPatDefEq preprocessThm pat.pattern pat.boundVars.size e
      | continue
    trace[Saturate.explore] "defEq"
    /- It matched! Update the substitution from free variables to expressions -/
    let mut subst := pmatch.subst
    for (i, mvar) in mvars.mapIdx fun i mvar => (i, mvar) do
      let arg ← instantiateMVars mvar
      if ¬ arg.isMVar then
        let vid := pat.boundVars[i]!
        if ¬ subst[vid]!.isSome then
          subst := subst.set! vid arg
    /- Check if the pattern is for an assumption, and add it to the substitution -/
    subst ← do
      match pat.instVar with
      | none => pure subst
      | some v =>
        if subst[v]!.isSome then
          logError "Internal error: assumption already instantiated"
          continue
        else
          let some path := path | throwError "Unreachable"
          pure (subst.set! v (← mkExprFromPath path))
    -- Update the partial match (we check whether it's actually a total match when registering it)
    let pmatch : PartialMatch := { pmatch with patterns, subst }
    -- Register the partial match (this may introduce a theorem to instantiate if the match is actually total)
    state ← state.insertPartialMatch boundVars pmatch
  pure state

/-- Find all the lemmas which match an expression.
    - `boundVars`: if an instantiation of a theorem contains a bound variable, we ignore
      it (because we couldn't introduce the instantiated theorem it in the environment)
 -/
def matchExpr
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (path : Option AsmPath)
  (boundVars : Std.HashSet FVarId)
  (state : State) (e : Expr) :
  MetaM State := do
  withTraceNode `Saturate (fun _ => pure m!"matchExpr") do
  trace[Saturate.explore] "Matching: {e}"
  /- First check if the expression contains bound vars: if it does, then we don't match it -/
  if ¬ boundVars.isEmpty then
    let allFVars ← getFVarIds e Std.HashSet.emptyWithCapacity
    if boundVars.any allFVars.contains then
      trace[Saturate.explore] "Not matching the expression because it contains bound variables"
      return state
  /- First match against the rules -/
  let state ← matchExprWithRules preprocessThm path boundVars state e
  /- Match again the partial matches -/
  let state ← matchExprWithPartialMatches preprocessThm path boundVars state e
  pure state

def filterProofTerms (config : Config) (exprs : Array Expr) : MetaM (Array Expr) :=
  if ¬ config.visitProofTerms then
    exprs.filterM fun arg => do
        let ty ← inferType arg
        if ← isProp ty then pure false
        else pure true
  else pure exprs

/- Recursively explore a term -/
private partial def visit
  (config : VisitConfig)
  (path : Option AsmPath)
  (depth : Nat)
  (exploreSubterms : Expr → Array Expr → MetaM (Array Expr))
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (boundVars : Std.HashSet FVarId)
  (state : State) (e : Expr)
  : MetaM State := do
  withTraceNode `Saturate (fun _ => pure m!"visit") do
  let e := e.consumeMData
  --
  trace[Saturate.explore] "Visiting {e}"
  -- Register the current assumption, if it is a conjunct inside an assumption
  let state := state.insertAssumption path e
  -- Match
  let state ← matchExpr preprocessThm path boundVars state e
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
      let state ← visit config none (depth + 1) exploreSubterms preprocessThm boundVars state localDecl.type
      let state ←
        match localDecl.value? with
        | none => pure state
        | some v => visit config none (depth + 1) exploreSubterms preprocessThm boundVars state v
      pure (boundVars, state)
      ) (boundVars, state)
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
      let state ← visit config (some (.conj .left path)) (depth + 1) exploreSubterms preprocessThm boundVars state (args[0]!)
      let state ← visit config (some (.conj .right path)) (depth + 1) exploreSubterms preprocessThm boundVars state (args[1]!)
      pure state
    else
      -- Explore the subterms
      let subterms ← exploreSubterms f args
      -- Optionally ignore the proof terms
      let subterms ← filterProofTerms config.toConfig subterms
      subterms.foldlM (fun state => visit config none (depth + 1) exploreSubterms preprocessThm boundVars state) state
  | .lam .. =>
    trace[Saturate.explore] ".lam"
    if config.visitBoundExpressions then
      lambdaLetTelescope e fun xs b => do
        let (boundVars, state) ← visitBinders (depth + 1) boundVars state xs
        visit config none (depth + 1) exploreSubterms preprocessThm boundVars state b
    else pure state
  | .forallE .. => do
    trace[Saturate.explore] ".forallE"
    if config.visitBoundExpressions then
      forallTelescope e fun xs b => do
        let (boundVars, state) ← visitBinders (depth + 1) boundVars state xs
        visit config none (depth + 1) exploreSubterms preprocessThm boundVars state b
    else pure state
  | .letE .. => do
    trace[Saturate.explore] ".letE"
    lambdaLetTelescope e fun xs b => do
      let (boundVars, state) ← visitBinders (depth + 1) boundVars state xs
      visit config path (depth + 1) exploreSubterms preprocessThm boundVars state b
  | .mdata _ b => do
    trace[Saturate.explore] ".mdata"
    visit config path (depth + 1) exploreSubterms preprocessThm boundVars state b
  | .proj _ _ b => do
    trace[Saturate.explore] ".proj"
    visit config none (depth + 1) exploreSubterms preprocessThm boundVars state b

/-- Recompute the set of assumptions.

    This is necessary if we want to saturate the goal in several steps and modify
    the assumptions in between (with a call to simp for example).
-/
private partial def visitRecomputeAssumptions
  (path : Option AsmPath)
  (depth : Nat)
  (exploreSubterms : Expr → Array Expr → MetaM (Array Expr))
  (state : State) (e : Expr)
  : MetaM State := do
  trace[Saturate.explore] "Visiting {e}"
  let e := e.consumeMData
  -- Register the current assumption, if it is a conjunct inside an assumption
  let state := state.insertAssumption path e
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
      let state ← visitRecomputeAssumptions (some (.conj .left path)) (depth + 1) exploreSubterms state (args[0]!)
      let state ← visitRecomputeAssumptions (some (.conj .right path)) (depth + 1) exploreSubterms state (args[1]!)
      pure state
    else
      pure state
  | .lam ..
  | .forallE ..
  | .letE .. => do pure state
  | .mdata _ b => do
    trace[Saturate.explore] ".mdata"
    visitRecomputeAssumptions path (depth + 1) exploreSubterms state b
  | .proj _ _ _ => do pure state

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

/- Exploration strategy: focus on the arithmetic expressions -/
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

/- The saturation tactic itself -/
partial def evalSaturateCore
  (config : Config)
  (state : State)
  (exploreSubterms : Option (Expr → Array Expr → MetaM (Array Expr)) := none)
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (declsToExplore : Array FVarId)
  (exploreTarget : Bool := true)
  : TacticM (State × Array FVarId)
  := do
  withTraceNode `Saturate (fun _ => pure m!"evalSaturateCore") do
  withMainContext do
  trace[Saturate] "Exploring goal: {← getMainGoal}"
  -- Explore
  let exploreSubterms :=
    match exploreSubterms with
    | none => fun f args => pure (#[f] ++ args)
    | some explore => explore
  let config : VisitConfig := {
    toConfig := config,
    matchWithRules := true,
    matchWithPartialMatches := true,
  }
  let visit config path state expr :=
    visit config path 0 exploreSubterms preprocessThm Std.HashSet.emptyWithCapacity state expr

  -- Explore the assumptions
  trace[Saturate] "Exploring the assumptions"

  let visitLocalDecl (state : State) (decl : LocalDecl) : TacticM State := do
    trace[Saturate] "Exploring local decl: {decl.userName}"
    /- We explore both the type, the expression and the body (if there is) -/
    /- Note that the path is used only when exploring the type of assumptions -/
    let path ←
      if ← isProp decl.type then pure (some (.asm decl.fvarId))
      else pure none
    let state ← visit config path state decl.type
    let state ← visit config none state decl.toExpr
    match decl.value? with
    | none => pure state
    | some value => visit config none state value

  let state ← do
    trace[Saturate] "declsToExplore: {declsToExplore.map Expr.fvar}"
    let decls ← declsToExplore.mapM fun d => d.getDecl
    decls.foldlM visitLocalDecl state

  -- Explore the target
  trace[Saturate] "Exploring the target"
  let state ← do
    if exploreTarget then do pure (← visit config none state (← Tactic.getMainTarget)) else do pure state

  /- Introduce the theorems in the context. We wrote the function in CPS on purpose (this
     helps prevent bugs where the local context is not the one we expect) -/
  trace[Saturate] "Finished exploring the goal. Matched:\n{state.matched.toList}"
  let addAssumptions (state : State) (allFVars : Array FVarId) :
    TacticM (Array FVarId × Array FVarId × Std.HashMap Expr AsmPath) := do
    withTraceNode `Saturate (fun _ => pure m!"addAssumptions") do
    withMainContext do
    let matched := state.matched.toArray
    let mut assumptions : Std.HashMap Expr AsmPath := state.assumptions
    let mut allFVars := allFVars
    let mut newFVars : Array FVarId := #[]
    for i in [0:matched.size] do
      let th := matched[i]!
      trace[Saturate] "Adding: {th}"
      -- The application worked: introduce the assumption in the context
      let thTy ← withMainContext do inferType th
      -- Check that we don't add the same assumption twice
      if assumptions.contains thTy || state.ignore.contains thTy then
        continue
      else
        let x ← Utils.addDeclTac (.num (.str .anonymous "_h") i) th thTy (asLet := false) fun x => pure x
        allFVars := allFVars.push x.fvarId!
        newFVars := newFVars.push x.fvarId!
        let path := AsmPath.asm x.fvarId!
        assumptions := assumptions.insert thTy path
    trace[Saturate] "Goal after introducing the assumptions: {← getMainGoal}"
    pure (allFVars, newFVars, assumptions)

  -- We do this in several passes: we add the assumptions, then explore the context again to saturate, etc.
  let saturateExtra
    (state : State)
    (allFVars newFVars : Array FVarId)
    (assumptions : Std.HashMap Expr AsmPath) :
    TacticM (State × Array FVarId × Array FVarId × Std.HashMap Expr AsmPath)
    := do
    withTraceNode `Saturate (fun _ => pure m!"saturateExtra") do
    withMainContext do
    trace[Saturate] "state.pmatches (num of partial matches: {state.pmatches.size}):\n{state.pmatches.toArray.map Prod.snd}"
    trace[Saturate] "state.assumptions: {state.assumptions.toArray}"
    let oldAssumptions := state.assumptions
    let mut state := { state with assumptions, matched := Std.HashSet.emptyWithCapacity }
    /- Explore the new assumptions by matching them against the rules and the partial matches.
        Note that we have to explore them recursively -/
    for fvarId in newFVars do
      let some ldecl ← fvarId.findDecl?
        | throwError "Internal error: could not find local declaration for an fvarId"
      state ← visitLocalDecl state ldecl
    /- Match the old assumptions, but only against the partially matched terms.
        As the patterns of the partial matches are not arbitrary patterns, but only
        patterns for preconditions, we do not need to explore them recursively.
      -/
    let empty := Std.HashSet.emptyWithCapacity 0
    for (assum, path) in Std.HashMap.toArray oldAssumptions do
      state ← matchExprWithPartialMatches preprocessThm path empty state assum
    -- Introduce the assumptions in the context and do another pass
    let (allFVars, newFVars, assumptions) ← addAssumptions state allFVars
    pure (state, allFVars, newFVars, assumptions)

  --
  let mut (allFVars, newFVars, assumptions) ← addAssumptions state #[]
  let mut state := state
  -- Repeatedly explore the context
  for _ in [0:config.saturationPasses] do
    (state, allFVars, newFVars, assumptions) ← saturateExtra state allFVars newFVars assumptions

  withMainContext do
  trace[Saturate] "Finished saturating"

  -- Display the diagnostics information
  trace[Saturate.diagnostics] "Saturate diagnostics info: {state.diagnostics.toArray}"
  -- Continue
  pure (state, allFVars)

/- Reexplore the context to recompute the set of assumptions -/
def recomputeAssumptions
  (state : State)
  (exploreSubterms : Option (Expr → Array Expr → MetaM (Array Expr)) := none)
  (declsToExplore : Array FVarId)
  : TacticM State
  := do
  withTraceNode `Saturate (fun _ => pure m!"recomputeAssumptions") do
  withMainContext do
  trace[Saturate] "Exploring goal: {← getMainGoal}"
  let ignore := state.assumptions.fold (fun ignore asm _ => ignore.insert asm) state.ignore
  let state : State := { state with ignore, assumptions := Std.HashMap.emptyWithCapacity }
  -- Explore
  let exploreSubterms :=
    match exploreSubterms with
    | none => fun f args => pure (#[f] ++ args)
    | some explore => explore
  let visit path (state : State) expr : MetaM State :=
    visitRecomputeAssumptions path 0 exploreSubterms state expr

  -- Explore the assumptions
  trace[Saturate] "Exploring the assumptions"

  let decls ← declsToExplore.mapM fun d => d.getDecl
  decls.foldlM (fun (state : State) (decl : LocalDecl) => do
    trace[Saturate] "Exploring local decl: {decl.userName}"
    if ← isProp decl.type then
      let path := some (.asm decl.fvarId)
      visit path state decl.type
    else pure state) state

partial def evalSaturate {α}
  (config : Config)
  (satAttr : Array SaturateAttribute)
  (exploreSubterms : Option (Expr → Array Expr → MetaM (Array Expr)) := none)
  (preprocessThm : Option (Array Expr → Expr → MetaM Unit))
  (declsToExplore : Array FVarId)
  (exploreTarget : Bool := true)
  (next : Array FVarId → TacticM α)
  : TacticM α
  := do
  withTraceNode `Saturate (fun _ => pure m!"evalSaturate") do
  -- Retrieve the rule sets
  let env ← getEnv
  let s := satAttr.map fun s => s.ext.getState env
  let state := State.new s
  let (_, fvarIds) ← evalSaturateCore config state exploreSubterms preprocessThm declsToExplore exploreTarget
  withMainContext do next fvarIds

elab "aeneas_saturate" : tactic => do
  let _ ← evalSaturate {} #[saturateAttr] none none
    (declsToExplore := ((← (← getLCtx).getDecls).map fun d => d.fvarId).toArray)
    (exploreTarget := true) (fun _ => pure ())

namespace Test
  set_option trace.Saturate.attribute false in
  @[aeneas_saturate l.length] -- TODO: local doesn't work here
  theorem rule1 (α : Type u) (l : List α) : l.length ≥ 0 := by simp

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
    aeneas_saturate
    extract_goal1
    simp [Nat.add_assoc]

  namespace Test
    set_option trace.Saturate.attribute false
    @[local aeneas_saturate l.length]
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
      aeneas_saturate
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
      aeneas_saturate
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
    aeneas_saturate
    extract_goal1
    simp [Nat.add_assoc]

  /- Testing patterns which are propositions -/
  @[aeneas_saturate x < y]
  theorem rule2 (x y : Nat) : x < y ↔ y > x := by omega

  set_option trace.Saturate.attribute true in
  @[aeneas_saturate (set := Aeneas.Test)] -- TODO: why does adding `local` make the saturation below fail?
  theorem rule2 (x : Nat) (h : 1 ≤ x) : 2 ≤ x + x := by omega

  example (x : Nat) (_h : 1 ≤ x) : 2 ≤ x + x := by
    aeneas_saturate
    assumption

  example (x : Nat) (_h : True ∧ 1 ≤ x ∧ True) : 2 ≤ x + x := by
    aeneas_saturate
    assumption

  set_option trace.Saturate.attribute true in
  @[aeneas_saturate x * y] -- TODO: why does adding `local` make the saturation below fail?
  theorem rule3 (x y a b : Nat) (h0 : a ≤ x) (h1 : b ≤ y) : a * b ≤ x * y := by
    exact Nat.mul_le_mul h0 h1

  /- Remark: this theorem is carefully written so that `rule3` gets instantiated
     *after one exploration pass* (in particular, the assumption `0 ≤ x * y`is useless). -/
  set_option trace.Saturate.insertPartialMatch true in
  example (x y : Nat) (_ : 0 ≤ x * y) (h : 3 ≤ y ∧ 2 ≤ x) : 6 ≤ x * y := by
    aeneas_saturate
    omega

  set_option trace.Saturate.insertPartialMatch true in
  example (x y z : Nat) (h : 2 ≤ x ∧ 3 ≤ y) (h1 : 8 ≤ z) : 32 ≤ x * y * z := by
    aeneas_saturate
    omega
-/
end Test

end Saturate

end Aeneas
