import Lean
import Mathlib.Tactic.Core

namespace Utils

open Lean Elab Term Meta

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

def addDecl (name : Name) (val : Expr) (type : Expr) (asLet : Bool) : Tactic.TacticM Expr :=
  -- I don't think we need that
  Lean.Elab.Tactic.withMainContext do
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
    let mvarId ← Tactic.getMainGoal
    let newMVar ← mkFreshExprSyntheticOpaqueMVar (← mvarId.getType)
    let newVal ← mkLetFVars #[nval] newMVar
    -- There are two cases:
    -- - asLet is true: newVal is `let $name := $val in $newMVar`
    -- - asLet is false: ewVal is `λ $name => $newMVar`
    --   We need to apply it to `val`
    let newVal := if asLet then newVal else mkAppN newVal #[val]
    -- Assign the main goal and update the current goal
    mvarId.assign newVal
    let goals ← Tactic.getUnsolvedGoals
    Lean.Elab.Tactic.setGoals (newMVar.mvarId! :: goals)
    -- Return the new value - note: we are in the *new* context, created
    -- after the declaration was added, so it will persist
    pure nval

def addDeclSyntax (name : Name) (val : Syntax) (asLet : Bool) : Tactic.TacticM Unit :=
  -- I don't think we need that
  Lean.Elab.Tactic.withMainContext do
  --
  let val ← elabTerm val .none
  let type ← inferType val
  -- In some situations, the type will be left as a metavariable (for instance,
  -- if the term is `3`, Lean has the choice between `Nat` and `Int` and will
  -- not choose): we force the instantiation of the meta-variable
  synthesizeSyntheticMVarsUsingDefault
  --
  let _ ← addDecl name val type asLet

elab "custom_let " n:ident " := " v:term : tactic => do
  addDeclSyntax n.getId v (asLet := true)

elab "custom_have " n:ident " := " v:term : tactic =>
  addDeclSyntax n.getId v (asLet := false)

example : Nat := by
  custom_let x := 4
  custom_have y := 4
  apply y

example (x : Bool) : Nat := by
  cases x <;> custom_let x := 3 <;> apply x

-- Repeatedly apply a tactic
partial def repeatTac (tac : Tactic.TacticM Unit) : Tactic.TacticM Unit := do
  try
    tac
    Tactic.allGoals (Tactic.focus (repeatTac tac))
  -- TODO: does this restore the state?
  catch _ => pure ()

def firstTac (tacl : List (Tactic.TacticM Unit)) : Tactic.TacticM Unit := do
  match tacl with
  | [] => pure ()
  | tac :: tacl =>
    try tac
    catch _ => firstTac tacl

-- Split the goal if it is a conjunction
def splitConjTarget : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  let and_intro := Expr.const ``And.intro []
  let mvarIds' ← _root_.Lean.MVarId.apply (← Tactic.getMainGoal) and_intro
  Term.synthesizeSyntheticMVarsNoPostponing
  Tactic.replaceMainGoal mvarIds'

-- Taken from Lean.Elab.Tactic.evalAssumption
def assumptionTac : Tactic.TacticM Unit :=
  Tactic.liftMetaTactic fun mvarId => do mvarId.assumption; pure []

end Utils
