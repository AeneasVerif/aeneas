import Lean
import Base.Utils
import Base.Primitives

namespace Progress

open Lean Elab Term Meta
open Utils

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Progress

/- # Progress tactic -/

structure PSpecDesc where
  -- The universally quantified variables
  fvars : Array Expr
  -- The existentially quantified variables
  evars : Array Expr
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

  /- Analyze a pspec theorem to decompose its arguments.

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
  def withPSpec [Inhabited (m a)] [Nonempty (m a)] (th : Expr) (k : PSpecDesc → m a)
    (sanityChecks : Bool := false) :
    m a := do
    trace[Progress] "Theorem: {th}"
    -- Dive into the quantified variables and the assumptions
    forallTelescope th fun fvars th => do
    trace[Progress] "All arguments: {fvars}"
  /-  -- Filter the argumens which are not propositions
    let rec getFirstPropIdx (i : Nat) : MetaM Nat := do
      if i ≥ fargs.size then pure i
      else do
        let x := fargs.get! i
        if ← Meta.isProp (← inferType x) then pure i
        else getFirstPropIdx (i + 1)
    let i ← getFirstPropIdx 0
    let fvars := fargs.extract 0 i
    let hyps := fargs.extract i fargs.size
    trace[Progress] "Quantified variables: {fvars}"
    trace[Progress] "Assumptions: {hyps}"
    -- Sanity check: all hypotheses are propositions (in particular, all the
    -- quantified variables are at the beginning)
    let hypsAreProp ← hyps.allM fun x => do Meta.isProp (← inferType x)
    if ¬ hypsAreProp then
      throwError "The theorem doesn't have the proper shape: all the quantified arguments should be at the beginning"
      -/
    -- Dive into the existentials
    existsTelescope th fun evars th => do
    trace[Progress] "Existentials: {evars}"
    -- Take the first conjunct
    let (th, post) ← optSplitConj th
    -- Destruct the equality
    let (th, ret) ← destEq th
    -- Destruct the application to get the name
    th.withApp fun f args => do
    if ¬ f.isConst then throwError "Not a constant: {f}"
    -- Compute the set of universally quantified variables which appear in the function arguments
    let allArgsFVars ← args.foldlM (fun hs arg => getFVarIds arg hs) HashSet.empty
    -- Sanity check
    if sanityChecks then
      let fvarsSet : HashSet FVarId := HashSet.ofArray (fvars.map (fun x => x.fvarId!))
      let filtArgsFVars := allArgsFVars.toArray.filter (fun fvar => ¬ fvarsSet.contains fvar)
      if ¬ filtArgsFVars.isEmpty then
        let filtArgsFVars := filtArgsFVars.map (fun fvarId => Expr.fvar fvarId)
        throwError "Some of the function inputs are not universally quantified: {filtArgsFVars}"
    let argsFVars := fvars.map (fun x => x.fvarId!)
    let argsFVars := argsFVars.filter (fun fvar => allArgsFVars.contains fvar)
    -- Return
    trace[Progress] "Function: {f.constName!}";
    let thDesc := {
      fvars := fvars
      evars := evars
      fName := f.constName!
      fLevels := f.constLevels!
      args := args
      argsFVars
      ret := ret
      post := post
    }
    k thDesc
end Methods


def getPSpecFunName (th : Expr) : MetaM Name :=
  withPSpec th (fun d => do pure d.fName) true

structure PSpecAttr where
  attr : AttributeImpl
  ext  : MapDeclarationExtension Name
  deriving Inhabited

/- The persistent map from function to pspec theorems. -/
initialize pspecAttr : PSpecAttr ← do
  let ext ← mkMapDeclarationExtension `pspecMap
  let attrImpl := {
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
      let fName ← MetaM.run' (getPSpecFunName thDecl.type)
      trace[Progress] "Registering spec theorem for {fName}"
      let env := ext.addEntry env (fName, thName)
      setEnv env
      pure ()
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def PSpecAttr.find? (s : PSpecAttr) (name : Name) : MetaM (Option Name) := do
  return (s.ext.getState (← getEnv)).find? name

end Progress
