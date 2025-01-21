import Lean
import Mathlib.Tactic.Core
import Aeneas.UtilsCore
import Aesop

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

private def test1 : Nat := 0
private def test2 (x : Nat) : Nat := x
print_decl test1
print_decl test2

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
        let e' ← mkLambdaFVars xs b (usedLetOnly := false)
        return (state, e')
    | .forallE .. => do
      forallTelescope e fun xs b =>
         mapreduceVisitBinders state xs fun state => do
         let (state, b) ← visit (i + 1) state b
         let e' ← mkForallFVars xs b
         return (state, e')
    | .letE .. => do
      lambdaLetTelescope e fun xs b =>
        mapreduceVisitBinders state xs fun state => do
        let (state, b) ← visit (i + 1) state b
        let e' ← mkLambdaFVars xs b (usedLetOnly := false)
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
    lambdaTelescopeN e 1 λ xs b => k (xs.get! 0) b

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

-- TODO: this should take a continuation
def addDeclTac (name : Name) (val : Expr) (type : Expr) (asLet : Bool) : TacticM Expr :=
  -- I don't think we need that
  withMainContext do
  -- Insert the new declaration
  let withDecl := if asLet then withLetDecl name type val else withLocalDeclD name type
  withDecl fun nval => do
    -- Tranform the main goal `?m0` to `let x = nval in ?m1`
    let mvarId ← getMainGoal
    let newMVar ← mkFreshExprSyntheticOpaqueMVar (← mvarId.getType)
    let newVal ← mkLetFVars #[nval] newMVar
    -- There are two cases:
    -- - asLet is true: newVal is `let $name := $val in $newMVar`
    -- - asLet is false: ewVal is `λ $name => $newMVar`
    --   We need to apply it to `val`
    let newVal := if asLet then newVal else mkAppN newVal #[val]
    -- Assign the main goal and update the current goal
    mvarId.assign newVal
    let goals ← getUnsolvedGoals
    setGoals (newMVar.mvarId! :: goals)
    -- Return the new value - note: we are in the *new* context, created
    -- after the declaration was added, so it will persist
    pure nval

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
  let _ ← addDeclTac name val type asLet

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

/-- Adapted from allGoals

    We use this instead of allGoals, because when the tactic throws an exception that we attempt
    to catch outside, the behavior can be quite surprising.
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

def firstTac (tacl : List (TacticM Unit)) : TacticM Unit := do
  match tacl with
  | [] => pure ()
  | tac :: tacl =>
    -- Should use try ... catch or Lean.observing?
    -- Generally speaking we should use Lean.observing? to restore the state,
    -- but with tactics the try ... catch variant seems to work
    try do
      tac
      -- Check that there are no remaining goals
      let gl ← Tactic.getUnsolvedGoals
      if ¬ gl.isEmpty then throwError "tactic failed"
    catch _ => firstTac tacl
/-    let res ← Lean.observing? do
      tac
      -- Check that there are no remaining goals
      let gl ← Tactic.getUnsolvedGoals
      if ¬ gl.isEmpty then throwError "tactic failed"
    match res with
    | some _ => pure ()
    | none => firstTac tacl -/

def isConj (e : Expr) : MetaM Bool :=
  e.consumeMData.withApp fun f args => pure (f.isConstOf ``And ∧ args.size = 2)

-- Return the first conjunct if the expression is a conjunction, or the
-- expression itself otherwise. Also return the second conjunct if it is a
-- conjunction.
def optSplitConj (e : Expr) : MetaM (Expr × Option Expr) := do
  e.consumeMData.withApp fun f args =>
  if f.isConstOf ``And ∧ args.size = 2 then pure (args.get! 0, some (args.get! 1))
  else pure (e, none)

-- Split the goal if it is a conjunction
def splitConjTarget : TacticM Unit := do
  withMainContext do
  let g ← getMainTarget
  trace[Utils] "splitConjTarget: goal: {g}"
  -- The tactic was initially implemened with `_root_.Lean.MVarId.apply`
  -- but it tended to mess the goal by unfolding terms, even when it failed
  let (l, r) ← optSplitConj g
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

-- Destruct an equaliy and return the two sides
def destEq (e : Expr) : MetaM (Expr × Expr) := do
  e.consumeMData.withApp fun f args =>
  if f.isConstOf ``Eq ∧ args.size = 3 then pure (args.get! 1, args.get! 2)
  else throwError "Not an equality: {e}"

-- Return the set of FVarIds in the expression
-- TODO: this collects fvars introduced in the inner bindings
partial def getFVarIds (e : Expr) (hs : Std.HashSet FVarId := Std.HashSet.empty) : MetaM (Std.HashSet FVarId) := do
  reduceVisit (fun _ (hs : Std.HashSet FVarId) e =>
    if e.isFVar then pure (hs.insert e.fvarId!) else pure hs)
    hs e

-- Return the set of MVarIds in the expression
partial def getMVarIds (e : Expr) (hs : Std.HashSet MVarId := Std.HashSet.empty) : MetaM (Std.HashSet MVarId) := do
  reduceVisit (fun _ (hs : Std.HashSet MVarId) e =>
    if e.isMVar then pure (hs.insert e.mvarId!) else pure hs)
    hs e

-- Taken from Lean.Elab.evalAssumption
def assumptionTac : TacticM Unit :=
  liftMetaTactic fun mvarId => do mvarId.assumption; pure []

-- List all the local declarations matching the goal
def getAllMatchingAssumptions (type : Expr) : MetaM (List (LocalDecl × Name)) := do
  let decls ← (← getLCtx).getAllDecls
  decls.filterMapM fun localDecl => do
    -- Make sure we revert the meta-variables instantiations by saving the state and restoring it
    let s ← saveState
    let x :=
        if (← isDefEq type localDecl.type) then (some (localDecl, localDecl.userName))
        else none
    restoreState s
    pure x

/- Like the assumption tactic, but if the goal contains meta-variables it applies an assumption only
   if there is a single assumption matching the goal. Aborts if several assumptions match the goal.

   We implement this behaviour to make sure we do not trigger spurious instantiations of meta-variables.
-/
def singleAssumptionTac : TacticM Unit := do
  withMainContext do
  let mvarId ← getMainGoal
  mvarId.checkNotAssigned `sassumption
  let goal ← instantiateMVars (← mvarId.getType)
  let goalMVars ← getMVarIds goal
  if goalMVars.isEmpty then
    -- No meta-variables: we can safely use the assumption tactic
    trace[Utils] "The goal does not contain meta-variables"
    assumptionTac
  else
    trace[Utils] "The goal contains meta-variables"
    -- There are meta-variables that
    match ← (getAllMatchingAssumptions goal) with
    | [(localDecl, _)] =>
      -- There is a single assumption which matches the goal: use it
      -- Note that we need to call isDefEq again to properly instantiate the meta-variables
      let _ ← isDefEq goal localDecl.type
      mvarId.assign (mkFVar localDecl.fvarId)
    | [] =>
      -- No assumption
      throwError "Could not find an assumption matching the goal"
    | fvars =>
      -- Several assumptions
      let fvars := fvars.map Prod.snd
      throwError "Several assumptions match the goal: {fvars}"

elab "sassumption " : tactic => do singleAssumptionTac

example (x y z w : Int) (h0 : x < y) (_ : x < w) (h1 : y < z) : x < z := by
  apply Int.lt_trans
  try sassumption -- This fails
  apply h0
  sassumption

-- Tactic to split on a disjunction.
-- The expression `h` should be an fvar.
-- TODO: there must be simpler. Use use _root_.Lean.MVarId.cases for instance
def splitDisjTac (h : Expr) (kleft kright : TacticM Unit) : TacticM Unit := do
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
  let a := xs.get! 0
  let b := xs.get! 1
  -- Introduce the new goals
  -- Returns:
  -- - the match branch
  -- - a fresh new mvar id
  let mkGoal (hTy : Expr) (nGoalName : String) : MetaM (Expr × MVarId) := do
    -- Introduce a variable for the assumption (`a` or `b`). Note that we reuse
    -- the name of the assumption we split.
    withLocalDeclD hName hTy fun var => do
    -- The new goal
    let mgoal ← mkFreshExprSyntheticOpaqueMVar goalType (tag := Name.mkSimple nGoalName)
    -- Clear the assumption that we split
    let mgoal ← mgoal.mvarId!.tryClearMany #[h.fvarId!]
    -- The branch expression
    let branch ← mkLambdaFVars #[var] (mkMVar mgoal)
    pure (branch, mgoal)
  let (inl, mleft) ← mkGoal a "left"
  let (inr, mright) ← mkGoal b "right"
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
  withMainContext kleft
  let leftGoals ← getUnsolvedGoals
  -- Focus on the right
  setGoals [mright]
  withMainContext kright
  let rightGoals ← getUnsolvedGoals
  -- Put all the goals back
  setGoals (leftGoals ++ rightGoals ++ goals)
  trace[Utils] "new goals: {← getUnsolvedGoals}"

elab "split_disj " n:ident : tactic => do
  withMainContext do
  let decl ← Lean.Meta.getLocalDeclFromUserName n.getId
  let fvar := mkFVar decl.fvarId
  splitDisjTac fvar (fun _ => pure ()) (fun _ => pure ())

example (x y : Int) (h0 : x ≤ y ∨ x ≥ y) : x ≤ y ∨ x ≥ y := by
  split_disj h0
  . apply Or.inl; assumption
  . apply Or.inr; assumption

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
      k (fields.get! 0) (fields.get! 1)
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
partial def splitAllExistsTac [Inhabited α] (h : Expr) (ids : List (Option Name)) (k : Expr → List (Option Name) → TacticM α) : TacticM α := do
  try
    let (optId, ids) :=
      match ids with
      | [] => (none, [])
      | x :: ids => (x, ids)
    splitExistsTac h optId (fun _ body => splitAllExistsTac body ids k)
  catch _ => k h ids

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
      k (fields.get! 0) (fields.get! 1)
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
  let args := (args.raw.getArgs.get! 0).getArgs
  if args.size > 0 then do
    let n := (args.get! 1).getId
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
  splitAllExistsTac fvar [] (fun _ _ => pure ())

example (h : a ∧ b) : a := by
  split_conj at h
  assumption

example (h : ∃ x y z, x + y + z ≥ 0) : ∃ x, x ≥ 0 := by
  split_existsl at h
  rename_i x y z
  exists x + y + z

/- Initialize a context for the `simp` function.

   The initialization of the context is adapted from `Tactic.elabSimpArgs`.
   Something very annoying is that there is no function which allows to
   initialize a simp context without doing an elaboration - as a consequence
   we write our own here. -/
def mkSimpCtx (simpOnly : Bool) (config : Simp.Config) (kind : SimpKind)
  (simprocs : List Name) (declsToUnfold : List Name)
  (thms : List Name) (hypsToUse : List FVarId) :
  Tactic.TacticM (Simp.Context × Simp.SimprocsArray) := do
  -- Initialize either with the builtin simp theorems or with all the simp theorems
  let simpThms ←
    if simpOnly then Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
    else getSimpTheorems
  -- Add the equational theorem for the declarations to unfold
  let addDeclToUnfold (thms : SimpTheorems) (decl : Name) : Tactic.TacticM SimpTheorems :=
    if kind == .dsimp then pure (thms.addDeclToUnfoldCore decl)
    else thms.addDeclToUnfold decl
  let simpThms ←
    declsToUnfold.foldlM addDeclToUnfold simpThms
  -- Add the hypotheses and the rewriting theorems
  let simpThms ←
    hypsToUse.foldlM (fun thms fvarId =>
      -- post: TODO: don't know what that is. It seems to be true by default.
      -- inv: invert the equality
      thms.add (.fvar fvarId) #[] (mkFVar fvarId) (post := true) (inv := false)
      -- thms.eraseCore (.fvar fvar)
      ) simpThms
  -- Add the rewriting theorems to use
  let simpThms ←
    thms.foldlM (fun thms thmName => do
      let info ← getConstInfo thmName
      if (← isProp info.type) then
        -- post: TODO: don't know what that is
        -- inv: invert the equality
        thms.addConst thmName (post := false) (inv := false)
      else
        throwError "Not a proposition: {thmName}"
      ) simpThms
  let congrTheorems ← getSimpCongrTheorems
  let defaultSimprocs ← if simpOnly then pure {} else Simp.getSimprocs
  let simprocs ← simprocs.foldlM (fun simprocs name => simprocs.add name true) defaultSimprocs
  let ctx ← Simp.mkContext config (simpTheorems := #[simpThms]) congrTheorems
  pure (ctx, #[simprocs])

inductive Location where
  /-- Apply the tactic everywhere. Same as `Tactic.Location.wildcard` -/
  | wildcard
  /-- Apply the tactic everywhere, including in the variable types (i.e., in
      assumptions which are not propositions).  --/
  | wildcard_dep
  /-- Same as Tactic.Location -/
  | targets (hypotheses : Array Syntax) (type : Bool)

-- Adapted from Tactic.simpLocation
def customSimpLocation (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (discharge? : Option Simp.Discharge := none)
  (loc : Location) : TacticM Simp.Stats := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    -- Simply call the regular simpLocation
    simpLocation ctx simprocs discharge? (Tactic.Location.targets hyps simplifyTarget)
  | Location.wildcard =>
    -- Simply call the regular simpLocation
    simpLocation ctx simprocs discharge? Tactic.Location.wildcard
  | Location.wildcard_dep =>
    -- Custom behavior
    withMainContext do
      -- Lookup *all* the declarations
      let lctx ← Lean.MonadLCtx.getLCtx
      let decls ← lctx.getDecls
      let tgts := (decls.map (fun d => d.fvarId)).toArray
      -- Call the regular simpLocation.go
      simpLocation.go ctx simprocs discharge? tgts (simplifyTarget := true)

/- Call the simp tactic. -/
def simpAt (simpOnly : Bool) (config : Simp.Config) (simprocs : List Name)
  (declsToUnfold : List Name) (thms : List Name) (hypsToUse : List FVarId) (loc : Location) :
  Tactic.TacticM Unit := do
  -- Initialize the simp context
  let (ctx, simprocs) ← mkSimpCtx simpOnly config .simp simprocs declsToUnfold thms hypsToUse
  -- Apply the simplifier
  let _ ← customSimpLocation ctx simprocs (discharge? := .none) loc

/- Call the dsimp tactic. -/
def dsimpAt (simpOnly : Bool) (config : Simp.Config) (simprocs : List Name)
  (declsToUnfold : List Name) (thms : List Name) (hypsToUse : List FVarId) (loc : Tactic.Location) :
  Tactic.TacticM Unit := do
  -- Initialize the simp context
  let (ctx, simprocs) ← mkSimpCtx simpOnly config .dsimp simprocs declsToUnfold thms hypsToUse
  -- Apply the simplifier
  dsimpLocation ctx simprocs loc

-- Call the simpAll tactic
def simpAll (config : Simp.Config) (simpOnly : Bool) (simprocs : List Name) (declsToUnfold : List Name) (thms : List Name) (hypsToUse : List FVarId) :
  Tactic.TacticM Unit := do
  -- Initialize the simp context
  let (ctx, simprocs) ← mkSimpCtx simpOnly config .simpAll simprocs declsToUnfold thms hypsToUse
  -- Apply the simplifier
  let (result?, _) ← Lean.Meta.simpAll (← getMainGoal) ctx (simprocs := simprocs)
  match result? with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [mvarId]

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

/-- Apply norm_cast to the whole context -/
def normCastAtAll : TacticM Unit := do
  withMainContext do
  let ctx ← Lean.MonadLCtx.getLCtx
  let decls ← ctx.getDecls
  NormCast.normCastTarget {}
  decls.forM (fun d => NormCast.normCastHyp {} d.fvarId)

@[inline] def tryLiftMetaTactic1 (tactic : MVarId → MetaM (Option MVarId)) (msg : String) : TacticM Unit :=
  withMainContext do
    if let some mvarId ← tactic (← getMainGoal) then
      replaceMainGoal [mvarId]
    else
      throwError msg

/-- Call the saturate function from aesop -/
def evalAesopSaturate (options : Aesop.Options') (ruleSets : Array Name) : TacticM Unit := do
  let rss ← Aesop.Frontend.getGlobalRuleSets ruleSets
  let rs ← Aesop.mkLocalRuleSet rss options
    |> Aesop.ElabM.runForwardElab (← getMainGoal)
  tryLiftMetaTactic1 (Aesop.saturate rs · options) "Aesop.saturate failed"

/-- Normalize the let-bindings by inlining them -/
def normalizeLetBindings (e : Expr) : MetaM Expr :=
  zetaReduce e

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
def attrIgnoreAuxDef (name : Name) (default : AttrM α) (x : AttrM α) : AttrM α := do
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

/-- Small utility: see below

    Check if a term has type `Prop`.
 -/
@[tactic checkIsProp]
def checkIfPropEval : Tactic := fun stx =>
  withMainContext do
  let x := stx.getArgs.toList.get! 1
  let x ← Elab.Term.elabTerm x none
  let ty ← inferType x
  if ty.isProp then pure ()
  else throwError "Not a proposition"

/-- "Decidable" cases: it often happens that we want to make a case disjunction over a decidable proposition `P`.
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
syntax (name := dcases) "dcases" atomic(ident " : ")? term : tactic
macro_rules
| `(tactic| dcases $x) =>
   let h := mkIdent (.str .anonymous "_")
  `(tactic|
    first | check_is_prop $x; cases $h : (¬ ($x) : $(Lean.mkIdent ``Bool)) <;>
            simp only [$(mkIdent ``decide_eq_false_iff_not):ident,
                       $(mkIdent ``decide_eq_true_eq):ident,
                       $(mkIdent ``Bool.not_eq_false'):ident,
                       $(mkIdent ``Bool.not_eq_true'):ident,
                       $(mkIdent ``Decidable.not_not):ident] at $h:ident
          | cases ($x))
| `(tactic| dcases $h : $x) =>
  `(tactic|
    first | check_is_prop $x; cases $h : (¬ ($x) : $(Lean.mkIdent ``Bool)) <;>
            simp only [$(mkIdent ``decide_eq_false_iff_not):ident,
                       $(mkIdent ``decide_eq_true_eq):ident,
                       $(mkIdent ``Bool.not_eq_false'):ident,
                       $(mkIdent ``Bool.not_eq_true'):ident,
                       $(mkIdent ``Decidable.not_not):ident] at ($h)
          | cases $h : ($x))

example (x y : Int) : True := by
  dcases h: x = y <;> simp

example (x y : Int) : True := by
  dcases h: x = y <;> simp

def extractGoal : TacticM Unit := do
  withMainContext do
  let ctx ← Lean.MonadLCtx.getLCtx
  let decls ← ctx.getDecls
  let assumptions : List Format ← decls.mapM fun decl => do
    let ty ← Meta.ppExprWithInfos decl.type
    let name :=
      match decl.userName with
      | .num _ _ => "_"
      | _ => decl.userName.toString
    pure ("\n  (" ++ name ++ " : " ++ ty.fmt ++ ")")
  let assumptions := Format.joinSep assumptions ""
  let mgoal ← Tactic.getMainGoal
  let goal ← Meta.ppExprWithInfos (← mgoal.getType)
  let msg := "example  " ++ assumptions ++ " :\n  " ++ goal.fmt ++ "\n  := sorry"
  println! msg

elab "extract_goal" : tactic => do
  withMainContext do
  extractGoal

example (x : Nat) (y : Nat) (_ : Nat) (h : x ≤ y) : y ≥ x := by
  set_option linter.unusedTactic false in
  extract_goal
  omega

end Utils

end Aeneas
