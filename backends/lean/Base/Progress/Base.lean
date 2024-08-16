import Lean
import Base.Utils
import Base.Primitives.Base
import Base.Extensions

namespace Progress

open Lean Elab Term Meta
open Utils Extensions

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Progress

/- # Progress tactic -/

structure PSpecDesc where
  -- The universally quantified variables
  -- Can be fvars or mvars
  fvars : Array Expr
  -- The existentially quantified variables
  evars : Array Expr
  -- The function applied to its arguments
  fArgsExpr : Expr
  -- ⊤ if the function is a constant (must be if we are registering a theorem,
  -- but is not necessarily the case if we are looking at a goal)
  fIsConst : Bool
  -- The function arguments
  fLevels : List Level
  args : Array Expr
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
  def withPSpec [Inhabited (m a)] [Nonempty (m a)]
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
    trace[Progress] "After splitting the equality:\n- lhs: {mExpr}\n- rhs: {ret}"
    -- Recursively destruct the monadic application to dive into the binds,
    -- if necessary (this is for when we use `withPSpec` inside of the `progress` tactic),
    -- and destruct the application to get the function name
    let rec strip_monad mExpr := do
      mExpr.consumeMData.withApp fun mf margs => do
      trace[Progress] "After stripping the arguments of the monad expression:\n- mf: {mf}\n- margs: {margs}"
      if mf.isConst ∧ mf.constName = ``Bind.bind then do
        -- Dive into the bind
        let fExpr := (margs.get! 4).consumeMData
        -- Recursve
        strip_monad fExpr
      else
        -- No bind
        pure (mExpr, mf, margs)
    let (fArgsExpr, f, args) ← strip_monad mExpr
    trace[Progress] "After stripping the arguments of the function call:\n- f: {f}\n- args: {args}"
    let fLevels ← do
      -- If we are registering a theorem, then the function must be a constant
      if ¬ f.isConst then
        if isGoal then pure []
        else throwError "Not a constant: {f}"
      else pure f.constLevels!
    -- *Sanity check* (activated if we are analyzing a theorem to register it in a DB)
    -- Check if some existentially quantified variables
    let _ := do
      -- Collect all the free variables in the arguments
      let allArgsFVars ← args.foldlM (fun hs arg => getFVarIds arg hs) HashSet.empty
      -- Check if they intersect the fvars we introduced for the existentially quantified variables
      let evarsSet : HashSet FVarId := HashSet.empty.insertMany (evars.map (fun (x : Expr) => x.fvarId!))
      let filtArgsFVars := allArgsFVars.toArray.filter (fun var => evarsSet.contains var)
      if filtArgsFVars.isEmpty then pure ()
      else
        let filtArgsFVars := filtArgsFVars.map (fun fvarId => Expr.fvar fvarId)
        throwError "Some of the function inputs are not universally quantified: {filtArgsFVars}"
    -- Return
    trace[Progress] "Function with arguments: {fArgsExpr}";
    let thDesc := {
      fvars := fvars
      evars := evars
      fArgsExpr
      fIsConst := f.isConst
      fLevels
      args := args
      ret := ret
      post := post
    }
    k thDesc

end Methods

def getPSpecFunArgsExpr (isGoal : Bool) (th : Expr) : MetaM Expr :=
  withPSpec isGoal th (fun d => do pure d.fArgsExpr)

-- pspec attribute
structure PSpecAttr where
  attr : AttributeImpl
  ext  : DiscrTreeExtension Name
  deriving Inhabited

/- The persistent map from expressions to pspec theorems. -/
initialize pspecAttr : PSpecAttr ← do
  let ext ← mkDiscrTreeExtension `pspecMap
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
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreMutRec thName (pure ()) do
        trace[Progress] "Registering spec theorem for {thName}"
        let thDecl := env.constants.find! thName
        let fKey ← MetaM.run' (do
          trace[Progress] "Theorem: {thDecl.type}"
          -- Normalize to eliminate the let-bindings
          let ty ← normalizeLetBindings thDecl.type
          trace[Progress] "Theorem after normalization (to eliminate the let bindings): {ty}"
          let fExpr ← getPSpecFunArgsExpr false ty
          trace[Progress] "Registering spec theorem for expr: {fExpr}"
          -- Convert the function expression to a discrimination tree key
          -- We use the default configuration
          let config : WhnfCoreConfig := {}
          DiscrTree.mkPath fExpr config)
        let env := ext.addEntry env (fKey, thName)
        setEnv env
        trace[Progress] "Saved the environment"
        pure ()
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def PSpecAttr.find? (s : PSpecAttr) (e : Expr) : MetaM (Array Name) := do
  -- We use the default configuration
  let config : WhnfCoreConfig := {}
  (s.ext.getState (← getEnv)).getMatch e config

def PSpecAttr.getState (s : PSpecAttr) : MetaM (DiscrTree Name) := do
  pure (s.ext.getState (← getEnv))

def showStoredPSpec : MetaM Unit := do
  let st ← pspecAttr.getState
  -- TODO: how can we iterate over (at least) the values stored in the tree?
  --let s := st.toList.foldl (fun s (f, th) => f!"{s}\n{f} → {th}") f!""
  let s := f!"{st}"
  IO.println s

end Progress
