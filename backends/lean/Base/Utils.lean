import Lean
import Mathlib.Tactic.Core
import Mathlib.Tactic.LeftRight

/-
Mathlib tactics:
- rcases: https://leanprover-community.github.io/mathlib_docs/tactics.html#rcases
- split_ifs: https://leanprover-community.github.io/mathlib_docs/tactics.html#split_ifs
- norm_num: https://leanprover-community.github.io/mathlib_docs/tactics.html#norm_num
- should we use linarith or omega?
- hint: https://leanprover-community.github.io/mathlib_docs/tactics.html#hint
- classical: https://leanprover-community.github.io/mathlib_docs/tactics.html#classical
-/

/-
TODO:
- we want an easier to use cases:
  - keeps in the goal an equation of the shape: `t = case`
  - if called on Prop terms, uses Classical.em
  Actually, the cases from mathlib seems already quite powerful
  (https://leanprover-community.github.io/mathlib_docs/tactics.html#cases)
  For instance: cases h : e
  Also: **casesm**
- better split tactic
- we need conversions to operate on the head of applications.
  Actually, something like this works:
  ```
  conv at Hl =>
    apply congr_fun
    simp [fix_fuel_P]
  ```
  Maybe we need a rpt ... ; focus?
- simplifier/rewriter have a strange behavior sometimes
-/


namespace List

  -- TODO: I could not find this function??
  @[simp] def flatten {a : Type u} : List (List a) → List a
  | [] => []
  | x :: ls => x ++ flatten ls

end List

-- TODO: move?
@[simp]
theorem neq_imp {α : Type u} {x y : α} (h : ¬ x = y) : ¬ y = x := by intro; simp_all

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
    let cs ← resolveGlobalConstWithInfos id
    explore_decl cs[0]!

private def test1 : Nat := 0
private def test2 (x : Nat) : Nat := x

print_decl test1
print_decl test2

#check LocalDecl

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

-- A map visitor function for expressions (adapted from `AbstractNestedProofs.visit`)
-- The continuation takes as parameters:
-- - the current depth of the expression (useful for printing/debugging)
-- - the expression to explore
partial def mapVisit (k : Nat → Expr → MetaM Expr) (e : Expr) : MetaM Expr := do
  let mapVisitBinders (xs : Array Expr) (k2 : MetaM Expr) : MetaM Expr := do
    let localInstances ← getLocalInstances
    let mut lctx ← getLCtx
    for x in xs do
      let xFVarId := x.fvarId!
      let localDecl ← xFVarId.getDecl
      let type      ← mapVisit k localDecl.type
      let localDecl := localDecl.setType type
      let localDecl ← match localDecl.value? with
         | some value => let value ← mapVisit k value; pure <| localDecl.setValue value
         | none       => pure localDecl
      lctx :=lctx.modifyLocalDecl xFVarId fun _ => localDecl
    withLCtx lctx localInstances k2
  -- TODO: use a cache? (Lean.checkCache)
  let rec visit (i : Nat) (e : Expr) : MetaM Expr := do
    -- Explore
    let e ← k i e
    match e with
    | .bvar _
    | .fvar _
    | .mvar _
    | .sort _
    | .lit _
    | .const _ _ => pure e
    | .app .. => do e.withApp fun f args => return mkAppN f (← args.mapM (visit (i + 1)))
    | .lam .. =>
      lambdaLetTelescope e fun xs b =>
        mapVisitBinders xs do mkLambdaFVars xs (← visit (i + 1) b) (usedLetOnly := false)
    | .forallE .. => do
      forallTelescope e fun xs b => mapVisitBinders xs do mkForallFVars xs (← visit (i + 1) b)
    | .letE .. => do
      lambdaLetTelescope e fun xs b => mapVisitBinders xs do
        mkLambdaFVars xs (← visit (i + 1) b) (usedLetOnly := false)
    | .mdata _ b => return e.updateMData! (← visit (i + 1) b)
    | .proj _ _ b => return e.updateProj! (← visit (i + 1) b)
  visit 0 e

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
    -- For debugging
    let lctx ← Lean.MonadLCtx.getLCtx
    let fid := nval.fvarId!
    let decl := lctx.get! fid
    trace[Arith] "  new decl: \"{decl.userName}\" ({nval}) : {decl.type} := {decl.value}"
    --
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

-- Repeatedly apply a tactic
partial def repeatTac (tac : TacticM Unit) : TacticM Unit := do
  try
    tac
    allGoals (focus (repeatTac tac))
  -- TODO: does this restore the state?
  catch _ => pure ()

def firstTac (tacl : List (TacticM Unit)) : TacticM Unit := do
  match tacl with
  | [] => pure ()
  | tac :: tacl =>
    try tac
    catch _ => firstTac tacl

-- Split the goal if it is a conjunction
def splitConjTarget : TacticM Unit := do
  withMainContext do
  let and_intro := Expr.const ``And.intro []
  let mvarIds' ← _root_.Lean.MVarId.apply (← getMainGoal) and_intro
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal mvarIds'

-- Taken from Lean.Elab.evalAssumption
def assumptionTac : TacticM Unit :=
  liftMetaTactic fun mvarId => do mvarId.assumption; pure []

def isConj (e : Expr) : MetaM Bool :=
  e.withApp fun f args => pure (f.isConstOf ``And ∧ args.size = 2)

-- Return the first conjunct if the expression is a conjunction, or the
-- expression itself otherwise. Also return the second conjunct if it is a
-- conjunction.
def optSplitConj (e : Expr) : MetaM (Expr × Option Expr) := do
  e.withApp fun f args =>
  if f.isConstOf ``And ∧ args.size = 2 then pure (args.get! 0, some (args.get! 1))
  else pure (e, none)

-- Destruct an equaliy and return the two sides
def destEq (e : Expr) : MetaM (Expr × Expr) := do
  e.withApp fun f args =>
  if f.isConstOf ``Eq ∧ args.size = 3 then pure (args.get! 1, args.get! 2)
  else throwError "Not an equality: {e}"

-- Return the set of FVarIds in the expression
partial def getFVarIds (e : Expr) (hs : HashSet FVarId := HashSet.empty) : MetaM (HashSet FVarId) := do
  e.withApp fun body args => do
  let hs := if body.isFVar then hs.insert body.fvarId! else hs
  args.foldlM (fun hs arg => getFVarIds arg hs) hs

-- Tactic to split on a disjunction.
-- The expression `h` should be an fvar.
-- TODO: there must be simpler. Use use _root_.Lean.MVarId.cases for instance
def splitDisjTac (h : Expr) (kleft kright : TacticM Unit) : TacticM Unit := do
  trace[Arith] "assumption on which to split: {h}"
  -- Retrieve the main goal
  withMainContext do
  let goalType ← getMainTarget
  let hDecl := (← getLCtx).get! h.fvarId!
  let hName := hDecl.userName
  -- Case disjunction
  let hTy ← inferType h
  hTy.withApp fun f xs => do
  trace[Arith] "as app: {f} {xs}"
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
  trace[Arith] "left: {inl}: {mleft}"
  trace[Arith] "right: {inr}: {mright}"
  -- Create the match expression
  withLocalDeclD (← mkFreshUserName `h) hTy fun hVar => do
  let motive ← mkLambdaFVars #[hVar] goalType
  let casesExpr ← mkAppOptM ``Or.casesOn #[a, b, motive, h, inl, inr]
  let mgoal ← getMainGoal
  trace[Arith] "goals: {← getUnsolvedGoals}"
  trace[Arith] "main goal: {mgoal}"
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
  trace[Arith] "new goals: {← getUnsolvedGoals}"

elab "split_disj " n:ident : tactic => do
  withMainContext do
  let decl ← Lean.Meta.getLocalDeclFromUserName n.getId
  let fvar := mkFVar decl.fvarId
  splitDisjTac fvar (fun _ => pure ()) (fun _ => pure ())

example (x y : Int) (h0 : x ≤ y ∨ x ≥ y) : x ≤ y ∨ x ≥ y := by
  split_disj h0
  . left; assumption
  . right; assumption


-- Tactic to split on an exists.
-- `h` must be an FVar
def splitExistsTac (h : Expr) (optId : Option Name) (k : Expr → Expr → TacticM α) : TacticM α := do
  withMainContext do
  let goal ←  getMainGoal
  let hTy ← inferType h
  if isExists hTy then do
    -- Try to use the user-provided names
    let altVarNames ←
      match optId with
      | none => pure #[]
      | some id => do
        let hDecl ← h.fvarId!.getDecl
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
partial def splitAllExistsTac [Inhabited α] (h : Expr) (ids : List Name) (k : Expr → List Name → TacticM α) : TacticM α := do
  try
    let (optId, ids) := listTryPopHead ids
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
      | none => pure #[]
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

elab "split_conj " n:ident : tactic => do
  withMainContext do
  let decl ← Lean.Meta.getLocalDeclFromUserName n.getId
  let fvar := mkFVar decl.fvarId
  splitConjTac fvar none (fun _ _ =>  pure ())

elab "split_all_exists " n:ident : tactic => do
  withMainContext do
  let decl ← Lean.Meta.getLocalDeclFromUserName n.getId
  let fvar := mkFVar decl.fvarId
  splitAllExistsTac fvar [] (fun _ _ => pure ())

example (h : a ∧ b) : a := by
  split_all_exists h
  split_conj h
  assumption

example (h : ∃ x y z, x + y + z ≥ 0) : ∃ x, x ≥ 0 := by
  split_all_exists h
  rename_i x y z h
  exists x + y + z

/- Call the simp tactic.
   The initialization of the context is adapted from Tactic.elabSimpArgs.
   Something very annoying is that there is no function which allows to
   initialize a simp context without doing an elaboration - as a consequence
   we write our own here. -/
def simpAt (declsToUnfold : List Name) (thms : List Name) (hypsToUse : List FVarId)
  (loc : Tactic.Location) :
  Tactic.TacticM Unit := do
  -- Initialize with the builtin simp theorems
  let simpThms ← Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  -- Add the equational theorem for the declarations to unfold
  let simpThms ←
    declsToUnfold.foldlM (fun thms decl => thms.addDeclToUnfold decl) simpThms
  -- Add the hypotheses and the rewriting theorems
  let simpThms ←
    hypsToUse.foldlM (fun thms fvarId =>
      -- post: TODO: don't know what that is
      -- inv: invert the equality
      thms.add (.fvar fvarId) #[] (mkFVar fvarId) (post := false) (inv := false)
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
  let ctx : Simp.Context := { simpTheorems := #[simpThms], congrTheorems }
  -- Apply the simplifier
  let _ ← Tactic.simpLocation ctx (discharge? := .none) loc

end Utils
