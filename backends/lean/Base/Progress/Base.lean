import Lean
import Std.Lean.HashSet
import Base.Utils
import Base.Primitives.Base
import Base.Lookup.Base

import Lean.Meta.DiscrTree
import Lean.Meta.Tactic.Simp

namespace Progress

open Lean Elab Term Meta
open Utils

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Progress

/- # Progress tactic -/

/- Discrimination trees map expressions to values. When storing an expression
   in a discrimination tree, the expression is first converted to an array
   of `DiscrTree.Key`, which are the keys actually used by the discrimination
   trees. The conversion operation is monadic, however, and extensions require
   all the operations to be pure. For this reason, in the state extension, we
   store the keys from *after* the transformation (i.e., the `DiscrTreeKey`
   below).
 -/
abbrev DiscrTreeKey (simpleReduce : Bool) := Array (DiscrTree.Key simpleReduce)

abbrev DiscrTreeExtension (α : Type) (simpleReduce : Bool) :=
  SimplePersistentEnvExtension (DiscrTreeKey simpleReduce × α) (DiscrTree α simpleReduce)

def mkDiscrTreeExtention [Inhabited α] [BEq α] (name : Name := by exact decl_name%) (simpleReduce : Bool) :
  IO (DiscrTreeExtension α simpleReduce) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun a => a.foldl (fun s a => a.foldl (fun s (k, v) => s.insertCore k v) s) DiscrTree.empty,
    addEntryFn    := fun s n => s.insertCore n.1 n.2 ,
  }

structure PSpecDesc where
  -- The universally quantified variables
  fvars : Array Expr
  -- The existentially quantified variables
  evars : Array Expr
  -- The function applied to its arguments
  fArgsExpr : Expr
  -- The function
  fName : Name
  -- The function arguments
  fLevels : List Level
  args : Array Expr
  -- The universally quantified variables which appear in the function arguments
  argsFVars : Array FVarId
  -- The returned value
  ret : Expr
  -- The postcondition (if there is)
  post : Option Expr

section Methods
  variable [MonadLiftT MetaM m] [MonadControlT MetaM m] [Monad m] [MonadOptions m]
  variable [MonadTrace m] [MonadLiftT IO m] [MonadRef m] [AddMessageContext m]
  variable [MonadError m]
  variable {a : Type}

  /- Analyze a goal or a pspec theorem to decompose its arguments.

     PSpec theorems should be of the following shape:
     ```
     ∀ x1 ... xn, H1 → ... Hn → ∃ y1 ... ym. f x1 ... xn = .ret ... ∧ Post1 ∧ ... ∧ Postk
     ```

     The continuation `k` receives the following inputs:
     - universally quantified variables
     - assumptions
     - existentially quantified variables
     - function name
     - function arguments
     - return
     - postconditions

     TODO: generalize for when we do inductive proofs
  -/
  partial
  def withPSpec [Inhabited (m a)] [Nonempty (m a)] (sanityChecks : Bool := false)
    (isGoal : Bool) (th : Expr) (k : PSpecDesc → m a) :
    m a := do
    trace[Progress] "Proposition: {th}"
    -- Dive into the quantified variables and the assumptions
    -- Note that if we analyze a pspec theorem to register it in a database (i.e.
    -- a discrimination tree), we need to introduce *meta-variables* for the
    -- quantified variables.
    let telescope (k : Array Expr → Expr → m a) : m a :=
      if isGoal then forallTelescope th.consumeMData (fun fvars th => k fvars th)
      else do
        let (fvars, _, th) ← forallMetaTelescope th.consumeMData
        k fvars th
    telescope fun fvars th => do
    trace[Progress] "Universally quantified arguments and assumptions: {fvars}"
    -- Dive into the existentials
    existsTelescope th.consumeMData fun evars th => do
    trace[Progress] "Existentials: {evars}"
    trace[Progress] "Proposition after stripping the quantifiers: {th}"
    -- Take the first conjunct
    let (th, post) ← optSplitConj th.consumeMData
    trace[Progress] "After splitting the conjunction:\n- eq: {th}\n- post: {post}"
    -- Destruct the equality
    let (mExpr, ret) ← destEq th.consumeMData
    trace[Progress] "After splitting the equality:\n- lhs: {th}\n- rhs: {ret}"
    -- Destruct the monadic application to dive into the bind, if necessary (this
    -- is for when we use `withPSpec` inside of the `progress` tactic), and
    -- destruct the application to get the function name
    mExpr.consumeMData.withApp fun mf margs => do
    trace[Progress] "After stripping the arguments of the monad expression:\n- mf: {mf}\n- margs: {margs}"
    let (fArgsExpr, f, args) ← do
      if mf.isConst ∧ mf.constName = ``Bind.bind then do
        -- Dive into the bind
        let fExpr := (margs.get! 4).consumeMData
        fExpr.withApp fun f args => pure (fExpr, f, args)
      else pure (mExpr, mf, margs)
    trace[Progress] "After stripping the arguments of the function call:\n- f: {f}\n- args: {args}"
    if ¬ f.isConst then throwError "Not a constant: {f}"
    -- Compute the set of universally quantified variables which appear in the function arguments
    let allArgsFVars ← args.foldlM (fun hs arg => getFVarIds arg hs) HashSet.empty
    -- Sanity check
    if sanityChecks then
      -- All the variables which appear in the inputs given to the function are
      -- universally quantified (in particular, they are not *existentially* quantified)
      let fvarsSet : HashSet FVarId := HashSet.ofArray (fvars.map (fun x => x.fvarId!))
      let filtArgsFVars := allArgsFVars.toArray.filter (fun fvar => ¬ fvarsSet.contains fvar)
      if ¬ filtArgsFVars.isEmpty then
        let filtArgsFVars := filtArgsFVars.map (fun fvarId => Expr.fvar fvarId)
        throwError "Some of the function inputs are not universally quantified: {filtArgsFVars}"
    let argsFVars := fvars.map (fun x => x.fvarId!)
    let argsFVars := argsFVars.filter (fun fvar => allArgsFVars.contains fvar)
    -- Return
    trace[Progress] "Function with arguments: {fArgsExpr}";
    let thDesc := {
      fvars := fvars
      evars := evars
      fArgsExpr
      fName := f.constName!
      fLevels := f.constLevels!
      args := args
      argsFVars
      ret := ret
      post := post
    }
    k thDesc

end Methods

/-def getPSpecFunArgsExpr (th : Expr) : MetaM Expr :=
  withPSpec true th (fun d => do pure d.fArgsExpr)

def getPSpecFunName (th : Expr) : MetaM Name :=
  withPSpec true th (fun d => do pure d.fName)-/

-- pspec attribute
structure PSpecAttr where
  attr : AttributeImpl
  ext  : DiscrTreeExtension Name true
  deriving Inhabited

/- The persistent map from function to pspec theorems. -/
initialize pspecAttr : PSpecAttr ← do
  let ext ← mkDiscrTreeExtention `pspecMap true
  let attrImpl : AttributeImpl := {
    name := `pspec
    descr := "Marks theorems to use with the `progress` tactic"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "invalid attribute 'pspec', must be global"
      -- Lookup the theorem
      let env ← getEnv
      let thDecl := env.constants.find! thName
      let isGoal := false
      let fKey ← MetaM.run' (withPSpec true isGoal thDecl.type fun d => do
        let fExpr := d.fArgsExpr
        trace[Progress] "Registering spec theorem for {fExpr}"
        -- Convert the function expression to a discrimination tree key
        DiscrTree.mkPath fExpr)
      let env := ext.addEntry env (fKey, thName)
      setEnv env
      pure ()
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def PSpecAttr.find? (s : PSpecAttr) (e : Expr) : MetaM (Array Name) := do
  (s.ext.getState (← getEnv)).getMatch e

def PSpecAttr.getState (s : PSpecAttr) : MetaM (DiscrTree Name true) := do
  pure (s.ext.getState (← getEnv))

def showStoredPSpec : MetaM Unit := do
  let st ← pspecAttr.getState
  -- TODO: how can we iterate over (at least) the values stored in the tree?
  --let s := st.toList.foldl (fun s (f, th) => f!"{s}\n{f} → {th}") f!""
  let s := f!"{st}"
  IO.println s

end Progress
