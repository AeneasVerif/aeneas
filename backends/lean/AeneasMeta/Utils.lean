import Lean
import AeneasMeta.UtilsCore

namespace Lean

namespace LocalContext

  open Lean Lean.Elab Command Term Lean.Meta

  -- Small utility: return the list of declarations in the context, from
  -- the last to the first.
  def getAllDecls (lctx : Lean.LocalContext) : MetaM (List Lean.LocalDecl) :=
    lctx.foldrM (fun d ls => do let d ← instantiateLocalDeclMVars d; pure (d :: ls)) []

  -- Return the list of declarations in the context, but filter the
  -- declarations which are considered as implementation details
  def getDecls (lctx : Lean.LocalContext) : MetaM (List Lean.LocalDecl) := do
    let ls ← lctx.getAllDecls
    pure (ls.filter (fun d => not d.isImplementationDetail))

  def getAssumptions (lctx : Lean.LocalContext) : MetaM (List Lean.LocalDecl) := do
    let ls ← lctx.getDecls
    ls.filterM (fun d => isProp d.type)

end LocalContext

end Lean

namespace Aeneas

namespace Utils

open Lean Elab Term Meta Tactic

-- Useful helper to explore definitions and figure out the variant
-- of their sub-expressions.
def explore_term (incr : String) (e : Expr) : MetaM Unit :=
  match e with
  | .bvar _ => do logInfo m!"{incr}bvar: {e}"; return ()
  | .fvar _ => do logInfo m!"{incr}fvar: {e}"; return ()
  | .mvar _ => do logInfo m!"{incr}mvar: {e}"; return ()
  | .sort _ => do logInfo m!"{incr}sort: {e}"; return ()
  | .const _ _ => do logInfo m!"{incr}const: {e}"; return ()
  | .app fn arg => do
    logInfo m!"{incr}app: {e}"
    explore_term (incr ++ "  ") fn
    explore_term (incr ++ "  ") arg
  | .lam _bName bTy body _binfo => do
    logInfo m!"{incr}lam: {e}"
    explore_term (incr ++ "  ") bTy
    explore_term (incr ++ "  ") body
  | .forallE _bName bTy body _bInfo => do
    logInfo m!"{incr}forallE: {e}"
    explore_term (incr ++ "  ") bTy
    explore_term (incr ++ "  ") body
  | .letE _dName ty val body _nonDep => do
    logInfo m!"{incr}letE: {e}"
    explore_term (incr ++ "  ") ty
    explore_term (incr ++ "  ") val
    explore_term (incr ++ "  ") body
  | .lit _ => do logInfo m!"{incr}lit: {e}"; return ()
  | .mdata _ e => do
    logInfo m!"{incr}mdata: {e}"
    explore_term (incr ++ "  ") e
  | .proj _ _ struct => do
    logInfo m!"{incr}proj: {e}"
    explore_term (incr ++ "  ") struct

def explore_decl (n : Name) : TermElabM Unit := do
  logInfo m!"Name: {n}"
  let env ← getEnv
  let decl := env.constants.find! n
  match decl with
  | .defnInfo val =>
     logInfo m!"About to explore defn: {decl.name}"
     logInfo m!"# Type:"
     explore_term "" val.type
     logInfo m!"# Value:"
     explore_term "" val.value
  | .axiomInfo _  => throwError m!"axiom: {n}"
  | .thmInfo _    => throwError m!"thm: {n}"
  | .opaqueInfo _ => throwError m!"opaque: {n}"
  | .quotInfo _   => throwError m!"quot: {n}"
  | .inductInfo _ => throwError m!"induct: {n}"
  | .ctorInfo _   => throwError m!"ctor: {n}"
  | .recInfo _    => throwError m!"rec: {n}"

syntax (name := printDecl) "print_decl " ident : command

open Lean.Elab.Command

@[command_elab printDecl] def elabPrintDecl : CommandElab := fun stx => do
  liftTermElabM do
    let id := stx[1]
    addCompletionInfo <| CompletionInfo.id id id.getId (danglingDot := false) {} none
    let some cs ← Term.resolveId? id | throwError m!"Unknown id: {id}"
    let name := cs.constName!
    explore_decl name

def printDecls (decls : List LocalDecl) : MetaM Unit := do
  let decls ← decls.foldrM (λ decl msg => do
    pure (m!"\n{decl.toExpr} : {← inferType decl.toExpr}" ++ msg)) m!""
  logInfo m!"# Ctx decls:{decls}"

-- Small utility: print all the declarations in the context (including the "implementation details")
elab "print_all_ctx_decls" : tactic => do
  let ctx ← Lean.MonadLCtx.getLCtx
  let decls ← ctx.getAllDecls
  printDecls decls

-- Small utility: print all declarations in the context
elab "print_ctx_decls" : tactic => do
  let ctx ← Lean.MonadLCtx.getLCtx
  let decls ← ctx.getDecls
  printDecls decls

-- A map-reduce visitor function for expressions (adapted from `AbstractNestedProofs.visit`)
-- The continuation takes as parameters:
-- - the current depth of the expression (useful for printing/debugging)
-- - the expression to explore
partial def mapreduceVisit {a : Type} (k : Nat → a → Expr → MetaM (a × Expr))
  (state : a) (e : Expr) : MetaM (a × Expr) := do
  let mapreduceVisitBinders (state : a) (xs : Array Expr) (k2 : a → MetaM (a × Expr)) :
    MetaM (a × Expr) := do
    let localInstances ← getLocalInstances
    -- Update the local declarations for the bindings in context `lctx`
    let rec visit_xs (lctx : LocalContext) (state : a) (xs : List Expr) : MetaM (LocalContext × a) := do
      match xs with
      | [] => pure (lctx, state)
      | x :: xs => do
        let xFVarId := x.fvarId!
        let localDecl ← xFVarId.getDecl
        let (state, type) ← mapreduceVisit k state localDecl.type
        let localDecl := localDecl.setType type
        let (state, localDecl) ← match localDecl.value? with
           | some value =>
             let (state, value) ← mapreduceVisit k state value
             pure (state, localDecl.setValue value)
           | none => pure (state, localDecl)
        let lctx := lctx.modifyLocalDecl xFVarId fun _ => localDecl
        -- Recursive call
        visit_xs lctx state xs
    let (lctx, state) ← visit_xs (← getLCtx) state xs.toList
    -- Call the continuation with the updated context
    withLCtx lctx localInstances (k2 state)
  -- TODO: use a cache? (Lean.checkCache)
  let rec visit (i : Nat) (state : a) (e : Expr) : MetaM (a × Expr) := do
    -- Explore
    let (state, e) ← k i state e
    match e with
    | .bvar _
    | .fvar _
    | .mvar _
    | .sort _
    | .lit _
    | .const _ _ => pure (state, e)
    | .app .. => do e.withApp fun f args => do
      let (state, args) ← args.foldlM (fun (state, args) arg => do let (state, arg) ← visit (i + 1) state arg; pure (state, arg :: args)) (state, [])
      let args := args.reverse
      let (state, f) ← visit (i + 1) state f
      let e' := mkAppN f (Array.mk args)
      return (state, e')
    | .lam .. =>
      lambdaLetTelescope e fun xs b =>
        mapreduceVisitBinders state xs fun state => do
        let (state, b) ← visit (i + 1) state b
        let e' ← mkLambdaFVars xs b (usedLetOnly := false) (generalizeNondepLet := false)
        return (state, e')
    | .forallE .. => do
      forallTelescope e fun xs b =>
         mapreduceVisitBinders state xs fun state => do
         let (state, b) ← visit (i + 1) state b
         let e' ← mkForallFVars xs b
         return (state, e')
    | .letE .. => do
      lambdaLetTelescope (preserveNondepLet := false) e fun xs b =>
        mapreduceVisitBinders state xs fun state => do
        let (state, b) ← visit (i + 1) state b
        let e' ← mkLambdaFVars xs b (usedLetOnly := false) (generalizeNondepLet := false)
        return (state, e')
    | .mdata _ b => do
      let (state, b) ← visit (i + 1) state b
      return (state, e.updateMData! b)
    | .proj _ _ b => do
      let (state, b) ← visit (i + 1) state b
      return (state, e.updateProj! b)
  visit 0 state e

-- A map visitor function for expressions (adapted from `AbstractNestedProofs.visit`)
-- The continuation takes as parameters:
-- - the current depth of the expression (useful for printing/debugging)
-- - the expression to explore
partial def mapVisit (k : Nat → Expr → MetaM Expr) (e : Expr) : MetaM Expr := do
  let k' i (_ : Unit) e := do
    let e ← k i e
    pure ((), e)
  let (_, e) ← mapreduceVisit k' () e
  pure e

-- A reduce visitor
partial def reduceVisit {a : Type} (k : Nat → a → Expr → MetaM a) (s : a) (e : Expr) : MetaM a := do
  let k' i (s : a) e := do
    let s ← k i s e
    pure (s, e)
  let (s, _) ← mapreduceVisit k' s e
  pure s

-- Generate a fresh user name for an anonymous proposition to introduce in the
-- assumptions
def mkFreshAnonPropUserName := mkFreshUserName `_

section Methods
  variable [MonadLiftT MetaM m] [MonadControlT MetaM m] [Monad m] [MonadError m]
  variable {a : Type}

  /- Like `lambdaTelescopeN` but only destructs a fixed number of lambdas -/
  def lambdaTelescopeN (e : Expr) (n : Nat) (k : Array Expr → Expr → m a) : m a :=
    lambdaTelescope e fun xs body => do
    if xs.size < n then throwError "lambdaTelescopeN: not enough lambdas"
    let xs := xs.extract 0 n
    let ys := xs.extract n xs.size
    let body ← liftMetaM (mkLambdaFVars ys body)
    k xs body

  /- Like `lambdaTelescope`, but only destructs one lambda
     TODO: is there an equivalent of this function somewhere in the
     standard library? -/
  def lambdaOne (e : Expr) (k : Expr → Expr → m a) : m a :=
    lambdaTelescopeN e 1 λ xs b => k (xs[0]!) b

  def isExists (e : Expr) : Bool := e.getAppFn.isConstOf ``Exists ∧ e.getAppNumArgs = 2

  -- Remark: Lean doesn't find the inhabited and nonempty instances if we don'
  -- put them explicitely in the signature
  partial def existsTelescopeProcess [Inhabited (m a)] [Nonempty (m a)]
    (fvars : Array Expr) (e : Expr) (k : Array Expr → Expr → m a) : m a := do
    -- Attempt to deconstruct an existential
    if isExists e then do
      let p := e.appArg!
      lambdaOne p fun x ne =>
      existsTelescopeProcess (fvars.push x) ne k
    else
      -- No existential: call the continuation
      k fvars e

  def existsTelescope [Inhabited (m a)] [Nonempty (m a)] (e : Expr) (k : Array Expr → Expr → m a) : m a := do
    existsTelescopeProcess #[] e k

end Methods

inductive Location where
  /-- Apply the tactic everywhere. Same as `Location.wildcard` -/
  | wildcard
  /-- Same as Location -/
  | targets (hypotheses : Array FVarId) (type : Bool)

def addDeclTac {α} (name : Name) (val : Expr) (type : Expr) (asLet : Bool) (m : Expr → TacticM α) :
  TacticM α :=
  -- I don't think we need that
  withMainContext do
  -- Insert the new declaration
  let withDecl := if asLet then withLetDecl name type val else withLocalDeclD name type
  withDecl fun nval => do
    -- Tranform the main goal `?m0` to `let x = nval in ?m1`
    let mvarId ← getMainGoal
    let newMVar ← mkFreshExprSyntheticOpaqueMVar (← mvarId.getType)
    let newVal ← mkLetFVars #[nval] newMVar
    /- There are two cases:
     - asLet is true: newVal is `let $name := $val in $newMVar`
     - asLet is false: ewVal is `λ $name => $newMVar`
       We need to apply it to `val` -/
    let newVal := if asLet then newVal else mkAppN newVal #[val]
    -- Assign the main goal and update the current goal
    mvarId.assign newVal
    let goals ← getUnsolvedGoals
    setGoals (newMVar.mvarId! :: goals)
    -- Return the new value - note: we are in the *new* context, created
    -- after the declaration was added, so it will persist
    m nval

def addDeclTacSyntax (name : Name) (val : Syntax) (asLet : Bool) : TacticM Unit :=
  -- I don't think we need that
  withMainContext do
  --
  let val ← Term.elabTerm val .none
  let type ← inferType val
  -- In some situations, the type will be left as a metavariable (for instance,
  -- if the term is `3`, Lean has the choice between `Nat` and `Int` and will
  -- not choose): we force the instantiation of the meta-variable
  synthesizeSyntheticMVarsUsingDefault
  --
  addDeclTac name val type asLet (fun _ => pure ())

elab "custom_let " n:ident " := " v:term : tactic => do
  addDeclTacSyntax n.getId v (asLet := true)

elab "custom_have " n:ident " := " v:term : tactic =>
  addDeclTacSyntax n.getId v (asLet := false)

example : Nat := by
  custom_let x := 4
  custom_have y := 4
  apply y

example (x : Bool) : Nat := by
  cases x <;> custom_let x := 3 <;> apply x

-- Attempt to apply a tactic
def tryTac (tac : TacticM Unit) : TacticM Unit := do
  let _ ← tryTactic tac

/-- Copy/pasted from Mathlib because we do not want to add it as a dependency for this module
    as it gets compiled. -/
def allGoals (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
  setGoals mvarIdsNew.toList

/-- Adapted from `Lean.Elab.Tactic.allGoals`

    We sometimes use this rather than `allGoals`, because when the tactic throws
    an exception that we attempt to catch outside, the behavior can be quite surprising.
 -/
def allGoalsNoRecover (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      tac
      mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
  setGoals mvarIdsNew.toList

-- Repeatedly apply a tactic
partial def repeatTac (tac : TacticM Unit) : TacticM Unit := do
  try
    tac
    allGoalsNoRecover (focus (repeatTac tac))
  -- TODO: does this restore the state?
  catch _ => pure ()

def firstTacSolve (tacl : List (TacticM Unit)) : TacticM Unit := do
  match tacl with
  | [] => throwError "no tactic succeeded"
  | tac :: tacl =>
    try do
      tac
      -- Check that there are no remaining goals
      let gl ← Tactic.getUnsolvedGoals
      if ¬ gl.isEmpty then throwError "tactic failed"
    catch _ => firstTacSolve tacl

def isConj (e : Expr) : MetaM Bool :=
  e.consumeMData.withApp fun f args => pure (f.isConstOf ``And ∧ args.size = 2)

-- Return the first conjunct if the expression is a conjunction, or the
-- expression itself otherwise. Also return the second conjunct if it is a
-- conjunction.
def optSplitConj (e : Expr) : Expr × Option Expr :=
  e.consumeMData.withApp fun f args =>
  if f.isConstOf ``And ∧ args.size = 2 then (args[0]!, some (args[1]!))
  else (e, none)

-- Tactic to split on a conjunction.
partial def splitConjs (e : Expr) : List Expr :=
  let (e, optE) := optSplitConj e.consumeMData
  match optE with
  | none => [e]
  | some e' =>
    e :: splitConjs e'

-- Split the goal if it is a conjunction
def splitConjTarget : TacticM Unit := do
  withMainContext do
  let g ← getMainTarget
  trace[Utils] "splitConjTarget: goal: {g}"
  -- The tactic was initially implemened with `_root_.Lean.MVarId.apply`
  -- but it tended to mess the goal by unfolding terms, even when it failed
  let (l, r) := optSplitConj g
  match r with
  | none => do throwError "The goal is not a conjunction"
  | some r => do
    let lmvar ← mkFreshExprSyntheticOpaqueMVar l
    let rmvar ← mkFreshExprSyntheticOpaqueMVar r
    let and_intro ← mkAppM ``And.intro #[lmvar, rmvar]
    let g ← getMainGoal
    g.assign and_intro
    let goals ← getUnsolvedGoals
    setGoals (lmvar.mvarId! :: rmvar.mvarId! :: goals)

partial
def numOfConjuncts(e: Expr): Nat := e.withApp fun
  | .const ``And _, #[op1, op2] => numOfConjuncts op1 + numOfConjuncts op2
  | _ , _ => 1

-- Destruct an equaliy and return the two sides
def destEqOpt (e : Expr) : MetaM (Option (Expr × Expr)) := do
  e.consumeMData.withApp fun f args =>
  if f.isConstOf ``Eq ∧ args.size = 3 then pure (some (args[1]!, args[2]!))
  else pure none

-- Destruct an equaliy and return the two sides
def destEq (e : Expr) : MetaM (Expr × Expr) := do
  match ← destEqOpt e with
  | none => throwError "Not an equality: {e}"
  | some e => pure e

def destProdTypeOpt (ty : Expr) : Option (Expr × Expr) := do
  ty.consumeMData.withApp fun fn args =>
  if fn.isConst ∧ fn.constName == ``Prod ∧ args.size = 2 then
    some (args[0]!, args[1]!)
  else none

partial def destProdsType (ty : Expr) : List Expr :=
  match destProdTypeOpt ty with
  | none => [ty]
  | some (ty0, ty1) => ty0 :: destProdsType ty1

def destProdValOpt (x : Expr) : Option (Expr × Expr) := do
  x.consumeMData.withApp fun f args =>
  if f.isConst ∧ f.constName = ``Prod.mk ∧ args.size = 4 then
    some (args[2]!, args[3]!)
  else none

partial def destProdsVal (x : Expr) : List Expr :=
  match destProdValOpt x with
  | none => [x]
  | some (x0, x1) => x0 :: destProdsVal x1

-- Return the set of FVarIds in the expression
-- TODO: this collects fvars introduced in the inner bindings
partial def getFVarIds (e : Expr) (hs : Std.HashSet FVarId := Std.HashSet.emptyWithCapacity) : MetaM (Std.HashSet FVarId) := do
  reduceVisit (fun _ (hs : Std.HashSet FVarId) e =>
    if e.isFVar then pure (hs.insert e.fvarId!) else pure hs)
    hs e

-- Return the set of MVarIds in the expression
partial def getMVarIds (e : Expr) (hs : Std.HashSet MVarId := Std.HashSet.emptyWithCapacity) : MetaM (Std.HashSet MVarId) := do
  reduceVisit (fun _ (hs : Std.HashSet MVarId) e =>
    if e.isMVar then pure (hs.insert e.mvarId!) else pure hs)
    hs e

-- Taken from Lean.Elab.evalAssumption
def assumptionTac : TacticM Unit :=
  liftMetaTactic fun mvarId => do mvarId.assumption; pure []

def filterAssumptionTacPreprocess : TacticM (DiscrTree FVarId) := do
  let mut dtree := DiscrTree.empty
  for decl in (← (← getLCtx).getDecls) do
    dtree ← dtree.insert decl.type decl.fvarId
  pure dtree

/-- Return `true` if managed to close goal `mvarId` using an assumption. -/
def filterAssumptionTacCore (dtree : DiscrTree FVarId) : TacticM Bool := do
  withMainContext do
  let g ← getMainGoal
  let type ← instantiateMVars (← g.getType)
  let candidates ← dtree.getMatch type
  trace[Utils] "Candidates: {candidates.map Expr.fvar}"
  let asm : Option FVarId ← candidates.findM? fun fvar => do
    let localDecl ← fvar.getDecl
    isDefEq type localDecl.type
  match asm with
  | none => return false
  | some fvarId => g.assign (mkFVar fvarId); return true

/-- Same as `assumptionTac` but we use a discrimination tree to filter the assumptions we try.

    This means that the tactic is less powerful than `assumptionTac`, as we might miss an assumption
    which actually reduces to the goal, but it allows doing a preprocessing step, which makes it
    faster when we need to solve several goals while having the same context (this happens when
    solving preconditions in the tactic `progress`) and also it is safer to use, as unifying terms
    easily triggers "maximum recursion reached" errors when there are big integer constants in the
    context.
-/
def filterAssumptionTac : TacticM Bool := do
  let dtree ← filterAssumptionTacPreprocess
  filterAssumptionTacCore dtree

elab "fassumption " : tactic => do let _ ← filterAssumptionTac

-- `assumption` fails with "maximum recursion depth reached" below because it first attempts to
-- unify `x * 3000 ≤ 1` with the goal
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x y : Nat) (_ : y * 3000 ≤ 1) (_ : x * 3000 ≤ 1) : y * 3000 ≤ 1 := by
  assumption

-- Contrary to `assumption`, `fassumption` succeeds because it first filters the
-- assumptions
example (x y : Nat) (_ : y * 3000 ≤ 1) (_ : x * 3000 ≤ 1) : y * 3000 ≤ 1 := by
  fassumption

-- List all the local declarations matching the goal
def getMatchingAssumptions (type : Expr) : MetaM (List (LocalDecl × Name)) := do
  let typeType ← inferType type
  let decls ← (← getLCtx).getDecls
  decls.filterMapM fun localDecl => do
    -- Make sure we revert the meta-variables instantiations by saving the state and restoring it
    let s ← saveState
    let x ← do
        /- First check if the type can be matched (some assumptions are actually *variables*)-/
        if (← isDefEq typeType (← inferType localDecl.type)) then
          if (← isDefEq type localDecl.type) then
            pure (some (localDecl, localDecl.userName))
          else pure none
        else pure none
    restoreState s
    pure x

def singleAssumptionTacPreprocess := filterAssumptionTacPreprocess

def singleAssumptionTacCore (dtree : DiscrTree FVarId) : TacticM Unit := do
  withMainContext do
  let mvarId ← getMainGoal
  mvarId.checkNotAssigned `sassumption
  let goal ← instantiateMVars (← mvarId.getType)
  let goalMVars ← getMVarIds goal
  if goalMVars.isEmpty then
    -- No meta-variables: we can safely use the assumption tactic
    trace[Utils] "The goal does not contain meta-variables"
    unless ← filterAssumptionTacCore dtree do
      throwTacticEx `sassumption mvarId
  else
    trace[Utils] "The goal contains meta-variables"
    /- There are meta-variables that we need to instantiate

       Remark: at some point I tried using a discrimination tree to filter the assumptions,
       in particular inside the `progress` tactic as may need to call the `singleAssumptionTac`
       several times, but discrimination trees don't work if the expression we match over
       contains meta-variables.
     -/
    match ← (getMatchingAssumptions goal) with
    | [(localDecl, _)] =>
      /- There is a single assumption which matches the goal: use it
         Note that we need to call isDefEq again to properly instantiate the meta-variables -/
      let _ ← isDefEq goal localDecl.type
      mvarId.assign (mkFVar localDecl.fvarId)
    | [] =>
      -- No assumption
      throwError "Could not find an assumption matching the goal"
    | fvars =>
      -- Several assumptions
      let fvars := fvars.map Prod.snd
      throwError "Several assumptions match the goal: {fvars}"

/- Like the assumption tactic, but if the goal contains meta-variables it applies an assumption only
   if there is a single assumption matching the goal. Aborts if several assumptions match the goal.

   We implement this behaviour to make sure we do not trigger spurious instantiations of meta-variables.
-/
def singleAssumptionTac : TacticM Unit := do
  let dtree ← singleAssumptionTacPreprocess
  singleAssumptionTacCore dtree

elab "sassumption " : tactic => do singleAssumptionTac

example (x y z w : Int) (h0 : x < y) (_ : x < w) (h1 : y < z) : x < z := by
  apply Int.lt_trans
  try sassumption -- This fails
  apply h0
  sassumption

/- Tactic to split on a disjunction.
   The expression `h` should be an fvar.

   TODO: there must be simpler. Use use _root_.Lean.MVarId.cases for instance.
   On the other hand this tactic is a good reference for this kind of manipulations. -/
def splitDisjTac (h : Expr) (kleft kright : Expr → TacticM Unit) : TacticM Unit := do
  trace[Utils] "assumption on which to split: {h}"
  -- Retrieve the main goal
  withMainContext do
  let goalType ← getMainTarget
  let hDecl := (← getLCtx).get! h.fvarId!
  let hName := hDecl.userName
  -- Case disjunction
  let hTy ← inferType h
  hTy.withApp fun f xs => do
  trace[Utils] "as app: {f} {xs}"
  -- Sanity check
  if ¬ (f.isConstOf ``Or ∧ xs.size = 2) then throwError "Invalid argument to splitDisjTac"
  let a := xs[0]!
  let b := xs[1]!
  /- Introduce the new goals
      Returns:
      - the new assumption
      - the match branch
      - a fresh new mvar id -/
  let mkGoal (hTy : Expr) (nGoalName : String) : MetaM (Expr × Expr × MVarId) := do
    -- Introduce a variable for the assumption (`a` or `b`). Note that we reuse
    -- the name of the assumption we split.
    withLocalDeclD hName hTy fun var => do
    -- The new goal
    let mgoal ← mkFreshExprSyntheticOpaqueMVar goalType (tag := Name.mkSimple nGoalName)
    -- Clear the assumption that we split
    let mgoal ← mgoal.mvarId!.tryClearMany #[h.fvarId!]
    -- The branch expression
    let branch ← mkLambdaFVars #[var] (mkMVar mgoal)
    pure (var, branch, mgoal)
  let (hl, inl, mleft) ← mkGoal a "left"
  let (hr, inr, mright) ← mkGoal b "right"
  trace[Utils] "left: {inl}: {mleft}"
  trace[Utils] "right: {inr}: {mright}"
  -- Create the match expression
  withLocalDeclD (← mkFreshAnonPropUserName) hTy fun hVar => do
  let motive ← mkLambdaFVars #[hVar] goalType
  let casesExpr ← mkAppOptM ``Or.casesOn #[a, b, motive, h, inl, inr]
  let mgoal ← getMainGoal
  trace[Utils] "goals: {← getUnsolvedGoals}"
  trace[Utils] "main goal: {mgoal}"
  mgoal.assign casesExpr
  let goals ← getUnsolvedGoals
  -- Focus on the left
  setGoals [mleft]
  withMainContext (kleft hl)
  let leftGoals ← getUnsolvedGoals
  -- Focus on the right
  setGoals [mright]
  withMainContext (kright hr)
  let rightGoals ← getUnsolvedGoals
  -- Put all the goals back
  setGoals (leftGoals ++ rightGoals ++ goals)
  trace[Utils] "new goals: {← getUnsolvedGoals}"

partial def splitDisjsTac (h : Expr) : TacticM Unit :=
  tryTac (splitDisjTac h splitDisjsTac splitDisjsTac)

elab "split_disj" " at " n:ident : tactic => do
  withMainContext do
  let decl ← Lean.Meta.getLocalDeclFromUserName n.getId
  let fvar := mkFVar decl.fvarId
  splitDisjTac fvar (fun _ => pure ()) (fun _ => pure ())

elab "split_disjs" " at " n:ident : tactic => do
    withMainContext do
    let decl ← Lean.Meta.getLocalDeclFromUserName n.getId
    let fvar := mkFVar decl.fvarId
    splitDisjsTac fvar

example (x y : Int) (h0 : x ≤ y ∨ x ≥ y) : x ≤ y ∨ x ≥ y := by
  split_disj at h0
  . apply Or.inl; assumption
  . apply Or.inr; assumption

example (x : Int) (h : x = 0 ∨ x = 1 ∨ x = 2) : x ≤ 2 := by
  split_disjs at h <;> simp [*]

-- Tactic to split on an exists.
-- `h` must be an FVar
def splitExistsTac (h : Expr) (optId : Option Name) (k : Expr → Expr → TacticM α) : TacticM α := do
  withMainContext do
  let goal ←  getMainGoal
  let hTy ← inferType h
  if isExists hTy then do
    -- Try to use the user-provided names
    let altVarNames ← do
      let hDecl ← h.fvarId!.getDecl
      let id ← do
        match optId with
        | none => mkFreshUserName `x
        | some id => pure id
      pure #[{ varNames := [id, hDecl.userName] }]
    let newGoals ← goal.cases h.fvarId! altVarNames
    -- There should be exactly one goal
    match newGoals.toList with
    | [ newGoal ] =>
      -- Set the new goal
      let goals ← getUnsolvedGoals
      setGoals (newGoal.mvarId :: goals)
      -- There should be exactly two fields
      let fields := newGoal.fields
      withMainContext do
      k (fields[0]!) (fields[1]!)
    | _ =>
      throwError "Unreachable"
  else
    throwError "Not a conjunction"

-- TODO: move
def listTryPopHead (ls : List α) : Option α × List α :=
  match ls with
  | [] => (none, ls)
  | hd :: tl => (some hd, tl)

/- Destruct all the existentials appearing in `h`, and introduce them as variables
   in the context.

   If `ids` is not empty, we use it to name the introduced variables. We
   transmit the stripped expression and the remaining ids to the continuation.
 -/
partial def splitAllExistsTac [Inhabited α] (h : Expr) (ids : List (Option Name))
  (k : Array Expr → Expr → List (Option Name) → TacticM α) : TacticM α := do
  let rec run (fvars : Array Expr) h ids := do
    if isExists (← inferType h) then do
      let (optId, ids) :=
        match ids with
        | [] => (none, [])
        | x :: ids => (x, ids)
      splitExistsTac h optId (fun fvar body => run (fvars.push fvar) body ids)
    else k fvars h ids
  run #[] h ids

-- Tactic to split on a conjunction.
def splitConjTac (h : Expr) (optIds : Option (Name × Name)) (k : Expr → Expr → TacticM α)  : TacticM α := do
  withMainContext do
  let goal ←  getMainGoal
  let hTy ← inferType h
  if ← isConj hTy then do
    -- Try to use the user-provided names
    let altVarNames ←
      match optIds with
      | none => do
        let id0 ← mkFreshAnonPropUserName
        let id1 ← mkFreshAnonPropUserName
        pure #[{ varNames := [id0, id1] }]
      | some (id0, id1) => do
        pure #[{ varNames := [id0, id1] }]
    let newGoals ← goal.cases h.fvarId! altVarNames
    -- There should be exactly one goal
    match newGoals.toList with
    | [ newGoal ] =>
      -- Set the new goal
      let goals ← getUnsolvedGoals
      setGoals (newGoal.mvarId :: goals)
      -- There should be exactly two fields
      let fields := newGoal.fields
      withMainContext do
      k (fields[0]!) (fields[1]!)
    | _ =>
      throwError "Unreachable"
  else
    throwError "Not a conjunction"

-- Tactic to fully split a conjunction
partial def splitFullConjTacAux [Inhabited α] [Nonempty α] (keepCurrentName : Bool) (l : List Expr) (h : Expr) (k : List Expr → TacticM α)  : TacticM α := do
  try
    let ids ← do
      if keepCurrentName then do
        let cur := (← h.fvarId!.getDecl).userName
        let nid ← mkFreshAnonPropUserName
        pure (some (cur, nid))
      else
        pure none
    splitConjTac h ids (λ h1 h2 =>
      splitFullConjTacAux keepCurrentName l h1 (λ l1 =>
        splitFullConjTacAux keepCurrentName l1 h2 (λ l2 =>
          k l2)))
  catch _ =>
    k (h :: l)

-- Tactic to fully split a conjunction
-- `keepCurrentName`: if `true`, then the first conjunct has the name of the original assumption
def splitFullConjTac [Inhabited α] [Nonempty α] (keepCurrentName : Bool) (h : Expr) (k : List Expr → TacticM α)  : TacticM α := do
  splitFullConjTacAux keepCurrentName [] h (λ l => k l.reverse)

syntax optAtArgs := ("at" ident)?

def elabOptAtArgs (args : TSyntax `Aeneas.Utils.optAtArgs) : TacticM (Option Expr) := do
  withMainContext do
  let args := (args.raw.getArgs[0]!).getArgs
  if args.size > 0 then do
    let n := (args[1]!).getId
    let decl ← Lean.Meta.getLocalDeclFromUserName n
    let fvar := mkFVar decl.fvarId
    pure (some fvar)
  else
    pure none

elab "split_conj" args:optAtArgs : tactic => do
  withMainContext do
  match ← elabOptAtArgs args with
  | some fvar => do
    trace[Utils] "split at {fvar}"
    splitConjTac fvar none (fun _ _ =>  pure ())
  | none => do
    trace[Utils] "split goal"
    splitConjTarget

elab "split_conjs" args:optAtArgs : tactic => do
  withMainContext do
  match ← elabOptAtArgs args with
  | some fvar =>
    trace[Utils] "split at {fvar}"
    splitFullConjTac false fvar (fun _ =>  pure ())
  | none =>
    trace[Utils] "split goal"
    repeatTac splitConjTarget

elab "split_existsl" " at " n:ident : tactic => do
  withMainContext do
  let decl ← Lean.Meta.getLocalDeclFromUserName n.getId
  let fvar := mkFVar decl.fvarId
  splitAllExistsTac fvar [] (fun _ _ _ => do pure ())

example (h : a ∧ b) : a := by
  split_conj at h
  assumption

example (h : ∃ x y z, x + y + z ≥ 0) : ∃ x, x ≥ 0 := by
  split_existsl at h
  rename_i x y z
  exists x + y + z

/- Adapted from Elab.Tactic.Rewrite -/
def rewriteTarget (eqThm : Expr) (symm : Bool) (config : Rewrite.Config := {}) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let r ← (← getMainGoal).rewrite (← getMainTarget) eqThm symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

/- Adapted from Elab.Tactic.Rewrite -/
def rewriteLocalDecl (eqThm : Expr) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config := {}) :
    TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let rwResult ← Term.withSynthesize <| withMainContext do
    let localDecl ← fvarId.getDecl
    (← getMainGoal).rewrite localDecl.type eqThm symm (config := config)
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

/- Adapted from Elab.Tactic.Rewrite -/
def rewriteWithThms
  (thms : List (Bool × Expr))
  (rewrite : (symm : Bool) → (thm : Expr) → TacticM Unit)
  : TacticM Unit := do
  let rec go thms :=
    match thms with
    | [] => throwError "Failed to rewrite with any theorem"
    | (symm, eqThm)::thms =>
      rewrite symm eqThm <|> go thms
  go thms

/- Adapted from Elab.Tactic.Rewrite -/
def evalRewriteSeqAux (cfg : Rewrite.Config) (thms : List (Bool × Expr)) (loc : Tactic.Location) : TacticM Unit :=
  rewriteWithThms thms fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm · cfg)
      (rewriteTarget term symm cfg)
      (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")

/-- `rpt`: if `true`, repeatedly rewrite -/
def rewriteAt (cfg : Rewrite.Config) (rpt : Bool)
  (thms : List (Bool × Name)) (loc : Tactic.Location) : TacticM Unit := do
  -- Lookup the theorems
  let lookupThm (x : Bool × Name) : TacticM (List (Bool × Expr)) := do
    let thName := x.snd
    let lookupOne (thName : Name) : TacticM (Bool × Expr) := do
      -- Lookup the theorem and introduce fresh meta-variables for the universes
      let th ← mkConstWithFreshMVarLevels thName
      pure (x.fst, th)
    match ← getEqnsFor? thName with
    | some eqThms => do
      eqThms.toList.mapM lookupOne
    | none => do
      pure [← lookupOne thName]
  let thms ← List.mapM lookupThm thms
  let thms := thms.flatten
  -- Rewrite
  if rpt then
    Utils.repeatTac (evalRewriteSeqAux cfg thms loc)
  else
    evalRewriteSeqAux cfg thms loc

@[inline] def liftMetaTactic2 (tactic : MVarId → MetaM (Option (α × MVarId))) : TacticM (Option α) :=
  withMainContext do
    if let some (res, mvarId) ← tactic (← getMainGoal) then
      replaceMainGoal [mvarId]
      pure (some res)
    else
      replaceMainGoal []
      pure none

/-- Copy/paster from `norm_cast`: we need to retrieve the new fvar id -/
def normCastHyp (cfg : Simp.NormCastConfig) (fvarId : FVarId) : TacticM (Option FVarId) :=
  liftMetaTactic2 fun goal => do
    let hyp ← instantiateMVars (← fvarId.getDecl).type
    let prf ← NormCast.derive hyp cfg
    return (← applySimpResultToLocalDecl goal fvarId prf false)

/- Return `none` if the goal was closed, otherwise return the modified fvar ids -/
def normCastAt (loc : Location) : TacticM (Option (Array (FVarId))) := do
  withMainContext do
  match loc with
  | .targets asms tgt =>
    let mut fvarIds := #[]
    if tgt then
      NormCast.normCastTarget {}
    for fvarId in asms do
      match ← normCastHyp {} fvarId with
      | some id => fvarIds := fvarIds.push id
      | none => return none
    return some fvarIds
  | .wildcard =>
    NormCast.normCastTarget {}
    let ctx ← Lean.MonadLCtx.getLCtx
    let decls ← ctx.getDecls
    let mut fvarIds := #[]
    for d in decls do
      match ← normCastHyp {} d.fvarId with
      | some id => fvarIds := fvarIds.push id
      | none => return none
    return some fvarIds

@[inline] def tryLiftMetaTactic1 (tactic : MVarId → MetaM (Option MVarId)) (msg : String) : TacticM Unit :=
  withMainContext do
    if let some mvarId ← tactic (← getMainGoal) then
      replaceMainGoal [mvarId]
    else
      throwError msg

/-- Since Lean 4.22, non-dependent let expressions are automatically rewritten
    into have expressions. However, Lean.Meta.zetaReduce does not reduce have
    expressions, therefore hindering the let-binding normalization step below.
    This function is a reimplementation of Lean's zetaReduce, with the addition of
    `allowNondep := true`, which permits reduction of have expressions.
    https://github.com/leanprover/lean4/issues/10850 tracks this issue,
    and this function should be removed if it is upstreamed in more recent versions.
-/
def zetaHaveReduce (e : Expr) : MetaM Expr := do
  let pre (e : Expr) : MetaM TransformStep := do
    let .fvar fvarId := e | return .continue
    let some localDecl := (← getLCtx).find? fvarId | return .done e
    let some value := localDecl.value? (allowNondep := true) | return .done e
    return .visit (← instantiateMVars value)
  transform e (pre := pre) (usedLetOnly := true)

/-- Normalize the let-bindings by inlining them -/
def normalizeLetBindings (e : Expr) : MetaM Expr :=
  zetaHaveReduce e

section
  variable [Monad m] [MonadOptions m] [MonadTrace m] [MonadLiftT IO m] [AddMessageContext m] [MonadError m]
  variable {α : Type}

  /-- For the attributes

      If we apply an attribute to a definition in a group of mutually recursive definitions
      (say, to `foo` in the group [`foo`, `bar`]), the attribute gets applied to `foo` but also to
      the recursive definition which encodes `foo` and `bar` (Lean encodes mutually recursive
      definitions in one recursive definition, e.g., `foo._mutual`, before deriving the individual
      definitions, e.g., `foo` and `bar`, from this one). This definition should be named `foo._mutual`
      or `bar._mutual`, and we generally want to ignore it.

      TODO: same problem happens if we use decreases clauses, etc.

      Below, we implement a small utility to do so.
    -/
  def attrIgnoreAuxDef (name : Name) (default : m α) (x : m α) : m α := do
    -- TODO: this is a hack
    if let .str _ "_mutual" := name then
      trace[Utils] "Ignoring a mutually recursive definition: {name}"
      default
    else if let .str _ "_unary" := name then
      trace[Utils] "Ignoring a unary def: {name}"
      default
    else
      -- Normal execution
      x
end

/-- Split anything in the context, and return the resulting set of subgoals.
    Raise an exception if we couldn't split.
 -/
def splitAny : TacticM (List MVarId) := do
  -- This is taken from `evalSplit`
  let mvarId ← getMainGoal
  let fvarIds ← mvarId.getNondepPropHyps
  for fvarId in fvarIds do
    if let some mvarIds ← splitLocalDecl? mvarId fvarId then
      return mvarIds
  let some mvarIds ← splitTarget? mvarId | Meta.throwTacticEx `splitAny mvarId "Could not split"
  return mvarIds

/-- Repeteadly split the disjunctions in the context, then apply a tactic when we can't split anymore -/
partial def splitAll (endTac : TacticM Unit) : TacticM Unit := do
  withMainContext do
  try
    let mvarIds ← splitAny
    -- Update the goals
    setGoals ((← getUnsolvedGoals) ++ mvarIds)
    -- Continue
    allGoalsNoRecover (focus (splitAll endTac))
  catch _ =>
    allGoalsNoRecover endTac

elab "split_all" : tactic => do
  withMainContext do
  splitAll (pure ())

example (x y z : Int) (b1 b2 : Bool)
  (h1 : if b1 then x ≤ y else y ≥ x) (h2 : if b2 then y ≤ z else z ≥ y) :
  x ≤ z := by
  split_all <;> omega


syntax (name := checkIsProp) "check_is_prop" term : tactic

/-- TODO: deprecate dcases, as we can now use by_cases

    "Decidable" cases: it often happens that we want to make a case disjunction over a decidable proposition `P`.
    If we simply call `cases P` we don't get what we expect at all, and we need to do instead: `cases h : (P : Bool)`.
    There are two important things:
    - we need to cast the proposition to `Bool` so that the elaborator understands it should lookup the instance of `Decidable``
    - we need to name the hypothesis resulting from the case split, because generally we will need it to do some rewriting

    Doing this is often annoying (the syntax is ugly) and actually people often forget to write it exactly the way above.
    For this reason we introduce the tactic below, which first checks whether the term on which we do the case disjunction
    is a proposition or not, then performs the proper case split accordingly.

    Also, when doing a case disjunction over a decidable proposition, the `cases` tactic introduces the *negation* of
    the proposition first, while we expect the reverse. For this reason we don't do a case disjunction over `P` but
    rather `¬ P`.
  -/
syntax "dcases " (atomic(ident " : "))? term : tactic

macro_rules
| `(tactic| dcases $e) => `(tactic| by_cases h : $e)
macro_rules
| `(tactic| dcases $h : $e) =>
  `(tactic| by_cases $h : $e)

example (x y : Int) : True := by
  dcases h: x = y <;> simp

example (x y : Int) : True := by
  dcases h: x = y <;> simp

/-- Inspired by the `clear` tactic -/
def clearFVarIds (fvarIds : Array FVarId) : TacticM Unit := do
  let fvarIds ← withMainContext <| sortFVarIds fvarIds
  for fvarId in fvarIds.reverse do
    withMainContext do
      let mvarId ← (← getMainGoal).clear fvarId
      replaceMainGoal [mvarId]

/- Copy/pasted from Mathlib to avoid having to compile this dependency -/
namespace MathlibDuplicate
  /-- Given a local context and an array of `FVarIds` assumed to be in that local context, remove all
    implementation details. -/
    def filterOutImplementationDetails (lctx : LocalContext) (fvarIds : Array FVarId) : Array FVarId :=
      fvarIds.filter (fun fvar => ! (lctx.fvarIdToDecl.find! fvar).isImplementationDetail)

    /-- Elaborate syntax for an `FVarId` in the local context of the given goal. -/
    def getFVarIdAt (goal : MVarId) (id : Syntax) : TacticM FVarId := withRef id do
      -- use apply-like elaboration to suppress insertion of implicit arguments
      let e ← goal.withContext do
        elabTermForApply id (mayPostpone := false)
      match e with
      | Expr.fvar fvarId => return fvarId
      | _                => throwError "unexpected term '{e}'; expected single reference to variable"

    /-- Get the array of `FVarId`s in the local context of the given `goal`.

    If `ids` is specified, elaborate them in the local context of the given goal to obtain the array of
    `FVarId`s.

    If `includeImplementationDetails` is `false` (the default), we filter out implementation details
    (`implDecl`s and `auxDecl`s) from the resulting list of `FVarId`s. -/
    def getFVarIdsAt (goal : MVarId) (ids : Option (Array Syntax) := none)
        (includeImplementationDetails : Bool := false) : TacticM (Array FVarId) :=
      goal.withContext do
        let lctx := (← goal.getDecl).lctx
        let fvarIds ← match ids with
        | none => pure lctx.getFVarIds
        | some ids => ids.mapM <| getFVarIdAt goal
        if includeImplementationDetails then
          return fvarIds
        else
          return filterOutImplementationDetails lctx fvarIds
end MathlibDuplicate

/-- Minimize the goal by removing all the unnecessary variables and assumptions -/
partial def minimizeGoal : TacticM Unit := do
  withMainContext do
  /- Retrieve the goal -/
  let goalTy ← instantiateMVars (← (← getMainGoal).getType)
  trace[Utils] "Goal type: {goalTy}"
  let goalFVarIds ← getFVarIds goalTy
  /- Explore the local declarations to check which ones are need.
     We do this recursively until we reach a fixed-point. -/
  let ctx ← Lean.MonadLCtx.getLCtx
  let decls ← ctx.getDecls
  let declsFVarIds := Std.HashSet.ofList (decls.map (fun d => d.fvarId))
  /- -/
  let mut changed := true
  let mut neededIds := goalFVarIds
  -- We need to filter the variables: some of them might come from quantifiers
  neededIds := neededIds.filter (fun x => x ∈ declsFVarIds)
  trace[Utils] "Ids used in the goal: {← neededIds.toArray.mapM (fun x => x.getUserName)}"
  /- Compute the list of pairs:
     - declaration id
     - fvar ids it references in its type and body
  -/
  trace[Utils] "Computing the ids used in the local declarations"
  let declToFVarIds ← decls.mapM fun decl => do
    trace[Utils] "Computing the fvar ids of: {decl.userName}"
    /- Explore the type and the body: if they contain needed ids, add it -/
    trace[Utils] "Type: {decl.type}"
    let mut declIds := Std.HashSet.emptyWithCapacity
    -- Add the id of the declaration itself
    declIds := declIds.insert decl.fvarId
    -- Add the ids found in the type
    let mut typeIds ← getFVarIds decl.type
    typeIds := typeIds.filter (fun x => x ∈ declsFVarIds)
    trace[Utils] "Ids in type: {← typeIds.toArray.mapM (fun x => x.getUserName)}"
    declIds := declIds.union typeIds
    -- Add the ids found in the body
    match decl.value? with
    | none =>
      trace[Utils] "No value"
      pure ()
    | some value =>
      trace[Utils] "Value: {value}"
      let valueDeclIds ← getFVarIds value
      let valueDeclIds := valueDeclIds.filter (fun x => x ∈ declsFVarIds)
      trace[Utils] "Ids in value: {← valueDeclIds.toArray.mapM (fun x => x.getUserName)}"
      declIds := declIds.union valueDeclIds
    pure (decl.fvarId, decl.userName, declIds)
  /- Repeatedly explore the local declarations -/
  trace[Utils] "Computing the needed ids"
  /- Remember the set of ids from which we already added dependencies -/
  let mut addedIds : Std.HashSet FVarId := Std.HashSet.emptyWithCapacity
  while changed do
    changed := false
    for (declId, userName, declIds) in declToFVarIds do
      -- Shortcut: do not re-explore ids
      if declId ∉ addedIds then
        trace[Utils] "Exploring: {userName}"
        trace[Utils] "declIds: {← declIds.toArray.mapM (fun x => x.getUserName)}"
        let mut inter := false
        for x in declIds do
          if x ∈ neededIds then
            inter := true
            break
        /- Check if there is an intersection -/
        if inter then
          addedIds := addedIds.insert declId
          neededIds := neededIds.insert declId
          neededIds := neededIds.union declIds
          changed := true
    if changed then
      trace[Utils] "Re-exploring all the declarations"
  trace[Utils] "Done exploring the context"
  /- Clear all the fvars which were not listed -/
  trace[Utils] "neededIds: {← neededIds.toArray.mapM (fun x => x.getUserName)}"
  let allIds ← MathlibDuplicate.getFVarIdsAt (← getMainGoal)
  trace[Utils] "All context ids: {← allIds.mapM (fun x => x.getUserName)}"
  let allIds := allIds.filter (fun x => x ∉ neededIds)
  clearFVarIds allIds

elab "minimize_goal" : tactic => do
  withMainContext do
  minimizeGoal

/-- Print the goal as an auxiliary lemma that can be copy-pasted by the user -/
def extractGoal (ref : Syntax) (fullGoal : Bool) : TacticM Unit := do
  /- First minimize the goal, if necessary -/
  if ¬ fullGoal then
    minimizeGoal
  withMainContext do
  /- Rename the local declarations to avoid collisions -/
  let mut ctx ← Lean.MonadLCtx.getLCtx
  let rec stripHygieneAux (n : Name) : MetaM (Bool × Name) := do
    trace[Utils] "stripping: {n.toString}"
    match n with
    | .str pre str =>
      let (strip, pre) ← stripHygieneAux pre
      if strip ∨ str == "_@" ∨ str == "_hyg" then
        pure (true, pre)
      else pure (false, .str pre str)
    | .anonymous => pure (false, .anonymous)
    | .num pre i =>
      let (strip, pre) ← stripHygieneAux pre
      if strip then pure (true, pre) else pure (false, .num pre i)
  let stripHygiene n : MetaM Name := do pure (← stripHygieneAux n).snd

  let rec renameDecls (allNames : Std.HashSet Name) (decls : List LocalDecl) : MetaM LocalContext := do
    match decls with
    | [] => Lean.MonadLCtx.getLCtx
    | decl :: decls =>
      trace[Utils] "declName: {decl.userName.toString}"
      let userName ← stripHygiene decl.userName
      trace[Utils] "declName after stripping hygiene parts: {userName.toString}"
      if userName ∈ allNames then
        trace[Utils] "Name already used"
        let lctx ← Lean.MonadLCtx.getLCtx
        let newName := lctx.getUnusedName userName
        trace[Utils] "New name: {newName}"
        let lctx := lctx.setUserName decl.fvarId newName
        let allNames := allNames.insert newName
        withLCtx' lctx do
        renameDecls allNames decls
      else
        trace[Utils] "Name not used"
        let allNames := allNames.insert userName
        renameDecls allNames decls
  let lctx ← renameDecls Std.HashSet.emptyWithCapacity (← (← Lean.MonadLCtx.getLCtx).getDecls).reverse
  withLCtx' lctx do
  /- Extract the goal -/
  let decls ← ctx.getDecls
  let assumptions : List Format ← decls.mapM fun decl => do
    let ty ← Meta.ppExprWithInfos decl.type
    let name ← Meta.ppExprWithInfos (Expr.fvar decl.fvarId)
    match decl.value? with
    | none =>
      pure ("\n  (" ++ name.fmt ++ " : " ++ ty.fmt ++ ")")
    | some value =>
      let value ← Meta.ppExprWithInfos value
      pure ("\n  (" ++ name.fmt ++ " : " ++ ty.fmt ++ " := " ++ value.fmt ++  ")")
  let assumptions := Format.joinSep assumptions ""
  let mgoal ← getMainGoal
  let goal ← Meta.ppExprWithInfos (← mgoal.getType)
  let msg := "example" ++ assumptions ++ " :\n  " ++ goal.fmt ++ "\n  := by sorry"
  logInfoAt ref m!"{msg}"

elab ref:"extract_goal0" full:"full"? : tactic => do
  withMainContext do
  extractGoal ref full.isSome

-- TODO: actually there already exists `extract_goal` in the standard library
syntax "extract_goal1" ("full")? : tactic

macro_rules
| `(tactic|extract_goal1) =>
  `(tactic|set_option pp.coercions.types true in extract_goal0)
| `(tactic|extract_goal1 full) =>
  `(tactic|set_option pp.coercions.types true in extract_goal0 full)

/--
info: example
  (x : Nat)
  (y : Nat)
  (h_1 : x ≤ y)
  (h : y ≤ y) :
  x ≤ y
  := by sorry
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (x x y : Nat) (h : x ≤ y) (h : y ≤ y) : x ≤ y := by
  extract_goal1
  omega

/--
info: example
  (x : Nat)
  (y : Nat)
  (h : x ≤ y) :
  y ≥ x
  := by sorry
-/
#guard_msgs in
example (x : Nat) (y : Nat) (_ : Nat) (h : x ≤ y) : y ≥ x := by
  extract_goal1
  omega

-- TODO: why do we have x✝?
/--
info: example
  (v : List Nat)
  (i : Nat)
  (x_3 : Nat)
  (v1 : List Nat)
  (h_1 : i ≤ v.length)
  (h : i < v.length)
  (x_2 : x_3 = v[i]!)
  (x_1 : i = i + 1)
  (x✝ : v1.length = v.length) :
  v1.length = v.length
  := by sorry
-/
#guard_msgs in
set_option linter.unusedVariables false in
example
  (v : List Nat)
  (i : Nat)
  (x : Nat)
  (i1 : Nat)
  (v1 : List Nat)
  (h : i ≤ v.length)
  (h : i < v.length)
  (_ : x = v[i]!)
  (_ : i = i + 1)
  (_ : v1.length = v.length) :
  v1.length = v.length
  := by
  extract_goal1
  simp [*]

/--
info: example
  (i : Nat)
  (h : i ≤ 7)
  (j : Nat := i) :
  j ≤ 7
  := by sorry
-/
#guard_msgs in
example (i : Nat) (h : i ≤ 7) :
  let j := i
  j ≤ 7 := by
  intro j
  extract_goal1
  apply h

/-- Introduce an auxiliary assertion for the goal -/
def extractAssert (ref : Syntax) : TacticM Unit := do
  withMainContext do
  let goal ← (← getMainGoal).getType
  let goal ← Lean.Meta.Tactic.TryThis.delabToRefinableSyntax goal
  let tac : TSyntax `tactic ← `(tactic|have : $goal := by sorry)
  /- Remark: there exists addHaveSuggestion -/
  Meta.Tactic.TryThis.addSuggestion ref tac (origSpan? := ← getRef)

elab tk:"extract_assert" : tactic => do
  withMainContext do
  extractAssert tk

/--
info: Try this:
  [apply] have : y ≥ x := by sorry
-/
#guard_msgs in
example (x : Nat) (y : Nat) (_ : Nat) (h : x ≤ y) : y ≥ x := by
  extract_assert
  omega

/- Group a list of expressions into a (non-dependent) tuple -/
def mkProdsVal (xl : List Expr) : MetaM Expr :=
  match xl with
  | [] =>
    pure (Expr.const ``PUnit.unit [Level.succ .zero])
  | [x] => do
    pure x
  | x :: xl => do
    let xl ← mkProdsVal xl
    mkAppM ``Prod.mk #[x, xl]

def mkProdType (x y : Expr) : MetaM Expr :=
  mkAppM ``Prod #[x, y]

def mkProd (x y : Expr) : MetaM Expr :=
  mkAppM ``Prod.mk #[x, y]

/- Deconstruct a sigma type.

   For instance, deconstructs `(a : Type) × List a` into
   `Type` and `λ a => List a`.
 -/
def getSigmaTypes (ty : Expr) : MetaM (Expr × Expr) := do
  ty.withApp fun f args => do
  if ¬ f.isConstOf ``Sigma ∨ args.size ≠ 2 then
    throwError "Invalid argument to getSigmaTypes: {ty}"
  else
    pure (args[0]!, args[1]!)

/- Make a sigma type.

   `x` should be a variable, and `ty` and type which (might) uses `x`
 -/
def mkSigmaType (x : Expr) (sty : Expr) : MetaM Expr := do
  trace[Utils] "mkSigmaType: {x} {sty}"
  let alpha ← inferType x
  let beta ← mkLambdaFVars #[x] sty
  trace[Utils] "mkSigmaType: ({alpha}) ({beta})"
  mkAppOptM ``Sigma #[some alpha, some beta]

/- Generate a Sigma type from a list of *variables* (all the expressions
   must be variables).

   Example:
   - xl = [(a:Type), (ls:List a), (i:Int)]

   Generates:
   `(a:Type) × (ls:List a) × (i:Int)`

 -/
def mkSigmasType (xl : List Expr) : MetaM Expr :=
  match xl with
  | [] => do
    trace[Utils] "mkSigmasType: []"
    pure (Expr.const ``PUnit [Level.succ .zero])
  | [x] => do
    trace[Utils] "mkSigmasType: [{x}]"
    let ty ← inferType x
    pure ty
  | x :: xl => do
    trace[Utils] "mkSigmasType: [{x}::{xl}]"
    let sty ← mkSigmasType xl
    mkSigmaType x sty

/- Generate a product type from a list of *variables*.

   Example:
   - xl = [(ls:List a), (i:Int)]

   Generates:
   `List a × Int`
 -/
def mkProdsType (xl : List Expr) : MetaM Expr :=
  match xl with
  | [] => do
    trace[Utils] "mkProdsType: []"
    pure (Expr.const ``PUnit [Level.succ .zero])
  | [x] => do
    trace[Utils] "mkProdsType: [{x}]"
    let ty ← inferType x
    pure ty
  | x :: xl => do
    trace[Utils] "mkProdsType: [{x}::{xl}]"
    let ty ← inferType x
    let xl_ty ← mkProdsType xl
    mkAppM ``Prod #[ty, xl_ty]

/- Split the input arguments between the types and the "regular" arguments.

   We do something simple: we treat an input argument as an
   input type iff it appears in the type of the following arguments.

   Note that what really matters is that we find the arguments which appear
   in the output type.

   Also, we stop at the first input that we treat as an
   input type.
 -/
def splitInputArgs (in_tys : Array Expr) (out_ty : Expr) : MetaM (Array Expr × Array Expr) := do
  -- Look for the first parameter which appears in the subsequent parameters
  let rec splitAux (in_tys : List Expr) : MetaM (Std.HashSet FVarId × List Expr × List Expr) :=
    match in_tys with
    | [] => do
      let fvars ← getFVarIds (← inferType out_ty)
      pure (fvars, [], [])
    | ty :: in_tys => do
      let (fvars, in_tys, in_args) ← splitAux in_tys
      -- Have we already found where to split between type variables/regular
      -- variables?
      if ¬ in_tys.isEmpty then
        -- The fvars set is now useless: no need to update it anymore
        pure (fvars, ty :: in_tys, in_args)
      else
        -- Check if ty appears in the set of free variables:
        let ty_id := ty.fvarId!
        if fvars.contains ty_id then
          -- We must split here. Note that we don't need to update the fvars
          -- set: it is not useful anymore
          pure (fvars, [ty], in_args)
        else
          -- We must split later: update the fvars set
          let fvars := fvars.insertMany (← getFVarIds (← inferType ty))
          pure (fvars, [], ty :: in_args)
  let (_, in_tys, in_args) ← splitAux in_tys.toList
  pure (Array.mk in_tys, Array.mk in_args)

/- Apply a lambda expression to some arguments, simplifying the lambdas -/
def applyLambdaToArgs (e : Expr) (xs : Array Expr) : MetaM Expr := do
  lambdaTelescopeN e xs.size fun vars body =>
  -- Create the substitution
  let s : Std.HashMap FVarId Expr := Std.HashMap.ofList (List.zip (vars.toList.map Expr.fvarId!) xs.toList)
  -- Substitute in the body
  pure (body.replace fun e =>
    match e with
    | Expr.fvar fvarId => match s.get? fvarId with
      | none   => e
      | some v => v
    | _ => none)

/- Group a list of expressions into a dependent tuple.

   Example:
   xl = [`a : Type`, `ls : List a`]
   returns:
   `⟨ (a:Type), (ls: List a) ⟩`

   We need the type argument because as the elements in the tuple are
   "concrete", we can't in all generality figure out the type of the tuple.

   Example:
   `⟨ True, 3 ⟩ : (x : Bool) × (if x then Int else Unit)`
 -/
def mkSigmasVal (ty : Expr) (xl : List Expr) : MetaM Expr :=
  match xl with
  | [] => do
    trace[Utils] "mkSigmasVal: []"
    pure (Expr.const ``PUnit.unit [Level.succ .zero])
  | [x] => do
    trace[Utils] "mkSigmasVal: [{x}]"
    pure x
  | fst :: xl => do
    trace[Utils] "mkSigmasVal: [{fst}::{xl}]"
    -- Deconstruct the type
    let (alpha, beta) ← getSigmaTypes ty
    -- Compute the "second" field
    -- Specialize beta for fst
    let nty ← applyLambdaToArgs beta #[fst]
    -- Recursive call
    let snd ← mkSigmasVal nty xl
    -- Put everything together
    trace[Utils] "mkSigmasVal:\n{alpha}\n{beta}\n{fst}\n{snd}"
    mkAppOptM ``Sigma.mk #[some alpha, some beta, some fst, some snd]

def mkAnonymous (s : String) (i : Nat) : Name :=
  .num (.str .anonymous s) i

/- Given a list of values `[x0:ty0, ..., xn:ty1]`, where every `xi` might use the previous
   `xj` (j < i) and a value `out` which uses `x0`, ..., `xn`, generate the following
   expression:
   ```
   fun x:((x0:ty0) × ... × (xn:tyn) => -- **Dependent** tuple
   match x with
   | (x0, ..., xn) => out
   ```

   The `index` parameter is used for naming purposes: we use it to numerotate the
   bound variables that we introduce.

   We use this function to currify functions (the function bodies given to the
   fixed-point operator must be unary functions).

   Example:
   ========
   - xl = `[a:Type, ls:List a, i:Int]`
   - out = `a`
   - index = 0

   generates (getting rid of most of the syntactic sugar):
   ```
   λ scrut0 => match scrut0 with
   | Sigma.mk x scrut1 =>
     match scrut1 with
     | Sigma.mk ls i =>
       a
   ```
-/
partial def mkSigmasMatch (xl : List Expr) (out : Expr) (index : Nat := 0) : MetaM Expr :=
  match xl with
  | [] => do
    -- This would be unexpected
    throwError "mkSigmasMatch: empty list of input parameters"
  | [x] => do
    -- In the example given for the explanations: this is the inner match case
    trace[Utils] "mkSigmasMatch: [{x}]"
    mkLambdaFVars #[x] out
  | fst :: xl => do
    /- In the example given for the explanations: this is the outer match case
       Remark: for the naming purposes, we use the same convention as for the
       fields and parameters in `Sigma.casesOn` and `Sigma.mk` (looking at
       those definitions might help)

       We want to build the match expression:
       ```
       λ scrut =>
       match scrut with
       | Sigma.mk x ...  -- the hole is given by a recursive call on the tail
       ``` -/
    trace[Utils] "mkSigmasMatch: [{fst}::{xl}]"
    let alpha ← inferType fst
    let snd_ty ← mkSigmasType xl
    let beta ← mkLambdaFVars #[fst] snd_ty
    let snd ← mkSigmasMatch xl out (index + 1)
    let mk ← mkLambdaFVars #[fst] snd
    -- Introduce the "scrut" variable
    let scrut_ty ← mkSigmaType fst snd_ty
    withLocalDeclD (mkAnonymous "scrut" index) scrut_ty fun scrut => do
    trace[Utils] "mkSigmasMatch: scrut: ({scrut}) : ({← inferType scrut})"
    -- TODO: make the computation of the motive more efficient
    let motive ← do
      let out_ty ← inferType out
      match out_ty  with
      | .sort _ | .lit _ | .const .. =>
        -- The type of the motive doesn't depend on the scrutinee
        mkLambdaFVars #[scrut] out_ty
      | _ =>
        /- The type of the motive *may* depend on the scrutinee
           TODO: make this more efficient (we could change the output type of
           mkSigmasMatch -/
        mkSigmasMatch (fst :: xl) out_ty
    -- The final expression: putting everything together
    trace[Utils] "mkSigmasMatch:\n  ({alpha})\n  ({beta})\n  ({motive})\n  ({scrut})\n  ({mk})"
    let sm ← mkAppOptM ``Sigma.casesOn #[some alpha, some beta, some motive, some scrut, some mk]
    -- Abstracting the "scrut" variable
    let sm ← mkLambdaFVars #[scrut] sm
    trace[Utils] "mkSigmasMatch: sm: {sm}"
    pure sm

/- This is similar to `mkSigmasMatch`, but with non-dependent tuples

   Remark: factor out with `mkSigmasMatch`? This is extremely similar.
-/
partial def mkProdsMatch (xl : List Expr) (out : Expr) (index : Nat := 0) : MetaM Expr :=
  match xl with
  | [] => do
    -- This would be unexpected
    throwError "mkProdsMatch: empty list of input parameters"
  | [x] => do
    -- In the example given for the explanations: this is the inner match case
    trace[Utils] "mkProdsMatch: [{x}]"
    mkLambdaFVars #[x] out
  | fst :: xl => do
    trace[Utils] "mkProdsMatch: [{fst}::{xl}]"
    let alpha ← inferType fst
    let beta ← mkProdsType xl
    let snd ← mkProdsMatch xl out (index + 1)
    let mk ← mkLambdaFVars #[fst] snd
    -- Introduce the "scrut" variable
    let scrut_ty ← mkProdType alpha beta
    withLocalDeclD (mkAnonymous "scrut" index) scrut_ty fun scrut => do
    trace[Utils] "mkProdsMatch: scrut: ({scrut}) : ({← inferType scrut})"
    -- TODO: make the computation of the motive more efficient
    let motive ← do
      let out_ty ← inferType out
      match out_ty  with
      | .sort _ | .lit _ | .const .. =>
        -- The type of the motive doesn't depend on the scrutinee
        mkLambdaFVars #[scrut] out_ty
      | _ =>
        /- The type of the motive *may* depend on the scrutinee
           TODO: make this more efficient (we could change the output type of
           mkProdsMatch) -/
        mkProdsMatch (fst :: xl) out_ty
    /-let motive ← do
      let out_ty ← inferType out
      mkLambdaFVars #[scrut] out_ty-/
    -- The final expression: putting everything together
    trace[Utils] "mkProdsMatch:\n  ({alpha})\n  ({beta})\n  ({motive})\n  ({scrut})\n  ({mk})"
    let sm ← mkAppOptM ``Prod.casesOn #[some alpha, some beta, some motive, some scrut, some mk]
    -- Abstracting the "scrut" variable
    let sm ← mkLambdaFVars #[scrut] sm
    trace[Utils] "mkProdsMatch: sm: {sm}"
    pure sm

/- Same as `mkSigmasMatch` but also accepts an empty list of inputs, in which case
   it generates the expression:
   ```
   λ () => e
   ``` -/
def mkSigmasMatchOrUnit (xl : List Expr) (out : Expr) : MetaM Expr :=
  if xl.isEmpty then do
    let scrut_ty := Expr.const ``PUnit [Level.succ .zero]
    withLocalDeclD (mkAnonymous "scrut" 0) scrut_ty fun scrut => do
    mkLambdaFVars #[scrut] out
  else
    mkSigmasMatch xl out

/- Same as `mkProdsMatch` but also accepts an empty list of inputs, in which case
   it generates the expression:
   ```
   λ () => e
   ``` -/
def mkProdsMatchOrUnit (xl : List Expr) (out : Expr) : MetaM Expr :=
  if xl.isEmpty then do
    let scrut_ty := Expr.const ``PUnit [Level.succ .zero]
    withLocalDeclD (mkAnonymous "scrut" 0) scrut_ty fun scrut => do
    mkLambdaFVars #[scrut] out
  else
    mkProdsMatch xl out

/-- Duplicate the assumptions (of type prop) in the context.
    This is useful if we want to perform non-destructive simplifications, for instance when
    converting between different views (i.e., doing something like what `natify` or `zify` does).

    We return the pair: (original assumptions, new assumptions)
-/
def duplicateAssumptions (toDuplicate : Option (Array FVarId) := none) :
  TacticM (Array FVarId × Array FVarId) :=
  withMainContext do
  let decls ← do
    match toDuplicate with
    | none => pure (← (← getLCtx).getDecls).toArray
    | some decls => decls.mapM fun d => d.getDecl
  trace[Utils] "All declarations: {decls.map fun d => Expr.fvar d.fvarId}"
  let props ← decls.filterM (fun d => do isProp d.type)
  trace[Utils] "Current assumptions: {props.map LocalDecl.type}"
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  let goalName ← goal.getTag
  let newProps ← props.mapM fun d => do
    withMainContext do
    withLocalDeclD (.str d.userName "_") d.type fun var => do
    -- The new goal
    let mgoal ← mkFreshExprSyntheticOpaqueMVar goalType (tag := goalName)
    -- Assign the current goal and replace it with the new goal
    let currentGoal ← getMainGoal
    let e ← mkLambdaFVars #[var] mgoal
    let e := mkApp e (.fvar d.fvarId)
    currentGoal.assign e
    replaceMainGoal [mgoal.mvarId!]
    pure var.fvarId!
  pure (props.map LocalDecl.fvarId, newProps)

elab "duplicate_assumptions" : tactic => do
  let _ ← duplicateAssumptions

/--
info: example
  (a : Nat)
  (b : Nat)
  (h0 : a < b)
  (h1 : b ≤ 1024)
  (h0._ : a < b)
  (h1._ : b ≤ 1024) :
  b ≤ 1024
  := by sorry
-/
#guard_msgs in
example (a b : Nat) (h0 : a < b) (h1 : b ≤ 1024) : b ≤ 1024 := by
  duplicate_assumptions
  extract_goal1 full
  assumption

def parseOptLocation (loc : Option (TSyntax `Lean.Parser.Tactic.location)) :
  Elab.TermElabM (Utils.Location) :=
  let loc := Option.map expandLocation loc
  match loc with
  | none => pure (Utils.Location.targets #[] true)
  | some loc =>
    match loc with
    | .wildcard => pure .wildcard
    | .targets ids goal => do
      let ids ← ids.mapM Lean.Elab.Term.resolveId?
      if ids.all Option.isSome then
        pure (.targets (ids.filterMap (Option.map Expr.fvarId!)) goal)
      else
        Lean.Elab.throwUnsupportedSyntax

def exprToNat? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  if let some n := e.nat? then some n
  else if let some n := e.rawNatLit? then some n
  else none

def optElabTerm (e : Option (TSyntax `term)) : TacticM (Option Expr) := do
  match e with
  | none => pure none
  | some e => pure (some (← Lean.Elab.Tactic.elabTerm e none))

def traceGoalWithNode (cls : Name) (msg : String) : TacticM Unit := do
  withTraceNode cls (fun _ => do pure msg) do
    if ← isTracingEnabledFor cls then do
        addTrace cls m!"{← getMainGoal}"
    else pure ()

end Utils

end Aeneas
