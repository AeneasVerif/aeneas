import Lean
import Std.Lean.HashSet
import Base.Utils
import Base.Primitives.Base
import Base.Lookup.Base

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
  fExpr : Expr
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
    trace[Progress] "Proposition: {th}"
    -- Dive into the quantified variables and the assumptions
    forallTelescope th.consumeMData fun fvars th => do
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
    let (fExpr, f, args) ← do
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
    trace[Progress] "Function: {f.constName!}";
    let thDesc := {
      fvars := fvars
      evars := evars
      fExpr
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

def getPSpecClassFunNames (th : Expr) : MetaM (Name × Name) :=
  withPSpec th (fun d => do
    let arg0 := d.args.get! 0
    arg0.withApp fun f _ => do
    if ¬ f.isConst then throwError "Not a constant: {f}"
    pure (d.fName, f.constName)
    ) true

def getPSpecClassFunNameArg (th : Expr) : MetaM (Name × Expr) :=
  withPSpec th (fun d => do
    let arg0 := d.args.get! 0
    pure (d.fName, arg0)
    ) true

-- "Regular" pspec attribute
structure PSpecAttr where
  attr : AttributeImpl
  ext  : MapDeclarationExtension Name
  deriving Inhabited

/- pspec attribute for type classes: we use the name of the type class to
   lookup another map. We use the *first* argument of the type class to lookup
   into this second map.

   Example:
   ========
   We use type classes for addition. For instance, the addition between two
   U32 is written (without syntactic sugar) as `HAdd.add (Scalar ty) x y`. As a consequence,
   we store the theorem through the bindings: HAdd.add → Scalar → ...

   SH: TODO: this (and `PSpecClassExprAttr`) is a bit ad-hoc. For now it works for the
   specs of the scalar operations, which is what I really need, but I'm not sure it
   applies well to other situations. A better way would probably to use type classes, but
   I couldn't get them to work on those cases. It is worth retrying.
   UPDATE: use discrimination trees (`DiscrTree`) from core Lean
-/
structure PSpecClassAttr where
  attr : AttributeImpl
  ext  : MapDeclarationExtension (NameMap Name)
  deriving Inhabited

/- Same as `PSpecClassAttr` but we use the full first argument (it works when it
   is a constant). -/
structure PSpecClassExprAttr where
  attr : AttributeImpl
  ext  : MapDeclarationExtension (HashMap Expr Name)
  deriving Inhabited

/- The persistent map from function to pspec theorems. -/
initialize pspecAttr : PSpecAttr ← do
  let ext ← Lookup.mkMapDeclarationExtension `pspecMap
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
      let fName ← MetaM.run' (getPSpecFunName thDecl.type)
      trace[Progress] "Registering spec theorem for {fName}"
      let env := ext.addEntry env (fName, thName)
      setEnv env
      pure ()
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

/- The persistent map from type classes to pspec theorems -/
initialize pspecClassAttr : PSpecClassAttr ← do
  let ext : MapDeclarationExtension (NameMap Name) ←
    Lookup.mkMapMapDeclarationExtension Name.quickCmp `pspecClassMap
  let attrImpl : AttributeImpl  := {
    name := `cpspec
    descr := "Marks theorems to use for type classes with the `progress` tactic"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "invalid attribute 'cpspec', must be global"
      -- Lookup the theorem
      let env ← getEnv
      let thDecl := env.constants.find! thName
      let (fName, argName) ← MetaM.run' (getPSpecClassFunNames thDecl.type)
      trace[Progress] "Registering class spec theorem for ({fName}, {argName})"
      -- Update the entry if there is one, add an entry if there is none
      let env :=
        match (ext.getState (← getEnv)).find? fName with
        | none =>
          let m := RBMap.ofList [(argName, thName)]
          ext.addEntry env (fName, m)
        | some m =>
          let m := m.insert argName thName
          ext.addEntry env (fName, m)
      setEnv env
      pure ()
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

/- The 2nd persistent map from type classes to pspec theorems -/
initialize pspecClassExprAttr : PSpecClassExprAttr ← do
  let ext : MapDeclarationExtension (HashMap Expr Name) ←
    Lookup.mkMapHashMapDeclarationExtension `pspecClassExprMap
  let attrImpl : AttributeImpl  := {
    name := `cepspec
    descr := "Marks theorems to use for type classes with the `progress` tactic"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "invalid attribute 'cpspec', must be global"
      -- Lookup the theorem
      let env ← getEnv
      let thDecl := env.constants.find! thName
      let (fName, arg) ← MetaM.run' (getPSpecClassFunNameArg thDecl.type)
      -- Sanity check: no variables appear in the argument
      MetaM.run' do
        let fvars ← getFVarIds arg
        if ¬ fvars.isEmpty then throwError "The first argument ({arg}) contains variables"
      -- We store two bindings:
      -- - arg to theorem name
      -- - reduced arg to theorem name
      let rarg ← MetaM.run' (reduceAll arg)
      trace[Progress] "Registering class spec theorem for ({fName}, {arg}) and ({fName}, {rarg})"
      -- Update the entry if there is one, add an entry if there is none
      let env :=
        match (ext.getState (← getEnv)).find? fName with
        | none =>
          let m := HashMap.ofList [(arg, thName), (rarg, thName)]
          ext.addEntry env (fName, m)
        | some m =>
          let m := m.insert arg thName
          let m := m.insert rarg thName
          ext.addEntry env (fName, m)
      setEnv env
      pure ()
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }


def PSpecAttr.find? (s : PSpecAttr) (name : Name) : MetaM (Option Name) := do
  return (s.ext.getState (← getEnv)).find? name

def PSpecClassAttr.find? (s : PSpecClassAttr) (className argName : Name) : MetaM (Option Name) := do
  match (s.ext.getState (← getEnv)).find? className with
  | none => return none
  | some map => return map.find? argName

def PSpecClassExprAttr.find? (s : PSpecClassExprAttr) (className : Name) (arg : Expr) : MetaM (Option Name) := do
  match (s.ext.getState (← getEnv)).find? className with
  | none => return none
  | some map => return map.find? arg

def PSpecAttr.getState (s : PSpecAttr) : MetaM (NameMap Name) := do
  pure (s.ext.getState (← getEnv))

def PSpecClassAttr.getState (s : PSpecClassAttr) : MetaM (NameMap (NameMap Name)) := do
  pure (s.ext.getState (← getEnv))

def PSpecClassExprAttr.getState (s : PSpecClassExprAttr) : MetaM (NameMap (HashMap Expr Name)) := do
  pure (s.ext.getState (← getEnv))

def showStoredPSpec : MetaM Unit := do
  let st ← pspecAttr.getState
  let s := st.toList.foldl (fun s (f, th) => f!"{s}\n{f} → {th}") f!""
  IO.println s

def showStoredPSpecClass : MetaM Unit := do
  let st ← pspecClassAttr.getState
  let s := st.toList.foldl (fun s (f, m) =>
    let ms := m.toList.foldl (fun s (f, th) =>
      f!"{s}\n  {f} → {th}") f!""
    f!"{s}\n{f} → [{ms}]") f!""
  IO.println s

def showStoredPSpecExprClass : MetaM Unit := do
  let st ← pspecClassExprAttr.getState
  let s := st.toList.foldl (fun s (f, m) =>
    let ms := m.toList.foldl (fun s (f, th) =>
      f!"{s}\n  {f} → {th}") f!""
    f!"{s}\n{f} → [{ms}]") f!""
  IO.println s

end Progress
