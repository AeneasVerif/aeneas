import Lean
import Aeneas.Utils
import Aeneas.Std.Core
import Aeneas.Extensions
import Aeneas.Progress.Trace

namespace Aeneas

namespace Progress

open Lean Elab Term Meta
open Utils Extensions

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
        else throwError "{f} should be a constant"
      else pure f.constLevels!
    -- *Sanity check* (activated if we are analyzing a theorem to register it in a DB)
    -- Check if some existentially quantified variables
    let _ := do
      -- Collect all the free variables in the arguments
      let allArgsFVars ← args.foldlM (fun hs arg => getFVarIds arg hs) Std.HashSet.empty
      -- Check if they intersect the fvars we introduced for the existentially quantified variables
      let evarsSet : Std.HashSet FVarId := Std.HashSet.empty.insertMany (evars.map (fun (x : Expr) => x.fvarId!))
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

-- The progress attribute
structure PSpecAttr where
  attr : AttributeImpl
  ext  : DiscrTreeExtension Name
  deriving Inhabited

private def saveProgressSpecFromThm (ext : DiscrTreeExtension Name) (attrKind : AttributeKind) (thName : Name) :
  AttrM Unit := do
  -- TODO: use the attribute kind
  unless attrKind == AttributeKind.global do
    throwError "invalid attribute 'progress', must be global"
  -- Lookup the theorem
  let env ← getEnv
  -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
  attrIgnoreAuxDef thName (pure ()) do
    trace[Progress] "Registering `progress` theorem for {thName}"
    let thDecl := env.constants.find! thName
    let fKey ← MetaM.run' (do
      trace[Progress] "Theorem: {thDecl.type}"
      -- Normalize to eliminate the let-bindings
      let ty ← normalizeLetBindings thDecl.type
      trace[Progress] "Theorem after normalization (to eliminate the let bindings): {ty}"
      let fExpr ← getPSpecFunArgsExpr false ty
      trace[Progress] "Registering spec theorem for expr: {fExpr}"
      -- Convert the function expression to a discrimination tree key
      DiscrTree.mkPath fExpr)
    let env := ext.addEntry env (fKey, thName)
    setEnv env
    trace[Progress] "Saved the environment"
    pure ()

/- Initiliaze the `progress` attribute. -/
initialize pspecAttr : PSpecAttr ← do
  let ext ← mkDiscrTreeExtension `pspecMap
  let attrImpl : AttributeImpl := {
    name := `progress
    descr := "Adds theorems to the `progress` database"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      saveProgressSpecFromThm ext attrKind thName
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def PSpecAttr.find? (s : PSpecAttr) (e : Expr) : MetaM (Array Name) := do
  (s.ext.getState (← getEnv)).getMatch e

def PSpecAttr.getState (s : PSpecAttr) : MetaM (DiscrTree Name) := do
  pure (s.ext.getState (← getEnv))

def showStoredPSpec : MetaM Unit := do
  let st ← pspecAttr.getState
  -- TODO: how can we iterate over (at least) the values stored in the tree?
  --let s := st.toList.foldl (fun s (f, th) => f!"{s}\n{f} → {th}") f!""
  let s := f!"{st}"
  IO.println s

/-- Convert a list of fvars to a structure. TODO: for now we just create a big tuple, and it may not always work... -/
private def fvarsToStruct (fvars : Array Expr) : MetaM Expr := do
  mkProdsVal fvars.toList

private def mkExistsFVars (fvars : Array Expr) (body : Expr) : MetaM Expr := do
  let rec aux (fvars : List Expr) : MetaM Expr :=
    match fvars with
    | [] => pure body
    | fv :: fvars => do
      let e ← aux fvars
      let thm ← mkLambdaFVars #[fv] e
      mkAppM ``Exists #[thm]
  aux fvars.toList

/-- Auxiliary helper for `progress_pure` -/
private def liftThm (thm : Expr) : MetaM Expr := do
  forallTelescope thm fun fvars thm => do
  match thm with
  | .letE (declName : Name) declTy (value : Expr) (post : Expr) _ => do
    /- Introduce an fvar for the local declaration -/
    withLocalDeclD declName declTy fun fv => do
    /- Create the lifted expression -/
    let bound ← mkAppM ``Std.toResult #[value]
    let okExpr ← mkAppM ``Std.Result.ok #[fv]
    let eq ← mkAppM ``Eq #[bound, okExpr]
    /- Introduce the existential -/
    let thm ← mkLambdaFVars #[fv] (mkAnd eq post)
    let thm ← mkAppM ``Exists #[thm]
    /- Introduce the foralls -/
    mkLambdaFVars fvars thm
  | _ => do
    /- "Complex" let-bindings such as `let (x, y) := ...` are actually desugared to matches -/
    let me ← matchMatcherApp? thm
    let error (_ : Unit) : MetaM Expr := do throwError "The theorem does not have the proper shape: the statement after the universally quantified variables should start with a let-binding; found {thm} instead."
    let .some me := me
      | error ()
    if me.alts.size ≠ 1 ∨ me.discrs.size ≠ 1 then error ()
    else
    let numParams := me.altNumParams[0]!
    let branch := me.alts[0]!
    let discr := me.discrs[0]!
    /- Destruct the universally quantified variables -/
    forallTelescope branch.consumeMData fun fvars' post => do
    let fvars'' := fvars'.extract numParams fvars'.size
    let fvars' := fvars'.extract 0 numParams
    let post ← mkLambdaFVars fvars'' post
    /- Create the lifted expression -/
    let bound ← mkAppM ``Std.toResult #[discr]
    let okExpr ← mkAppM ``Std.Result.ok #[← fvarsToStruct fvars']
    let eq ← mkAppM ``Eq #[bound, okExpr]
    /- Introduce the existentials -/
    let thm ← mkExistsFVars fvars' (mkAnd eq post)
    /- Introduce the foralls -/
    mkLambdaFVars fvars thm

open Tactic

#check @Eq

namespace Test
  /-!
  Making some tests here to see how we should generate the proof terms when lifting theorems in `progress_pure`
  -/
  open Std Result
  def mk_pos_pair : Int × Int := (0, 1)

  theorem is_pos :
    let (x, y) := mk_pos_pair
    x ≥ 0 ∧ y ≥ 0 := by simp [mk_pos_pair]

  theorem lifted_is_pos :
    ∃ x y, toResult mk_pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0 :=
  (match mk_pos_pair with
  | (x, y) =>
    fun (h : match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0) =>
    Exists.intro x (Exists.intro y (@And.intro (ok (x, y) = ok (x, y)) _ (Eq.refl (ok (x, y))) h))
  : ∀ (_ : match mk_pos_pair with | (x, y) => x ≥ 0 ∧ y ≥ 0),
    ∃ x y, toResult mk_pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0) is_pos

  theorem lifted_is_pos' :
    ∃ x y, toResult mk_pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0 :=
  (match mk_pos_pair with
  | (x, y) =>
    fun (h : match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0) =>
    @Exists.intro Int (fun x_1 => ∃ y_1, ok (x, y) = ok (x_1, y_1) ∧ x_1 ≥ 0 ∧ y_1 ≥ 0)
      x (@Exists.intro Int (fun y_1 => ok (x, y) = ok (x, y_1) ∧ x ≥ 0 ∧ y_1 ≥ 0)
        y (@And.intro (ok (x, y) = ok (x, y)) _ (Eq.refl (ok (x, y))) h))
  : ∀ (_ : match mk_pos_pair with | (x, y) => x ≥ 0 ∧ y ≥ 0),
    ∃ x y, toResult mk_pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0) is_pos

  #print lifted_is_pos'

  #print Prod.casesOn
  theorem lifted_is_pos'' :
    ∃ x y, toResult mk_pos_pair = ok (x, y) ∧
    x ≥ 0 ∧ y ≥ 0 :=
  @Prod.casesOn Int Int
    (fun (s : Int × Int) =>
      (match s with | (x, y) => x ≥ 0 ∧ y ≥ 0) →
      ∃ x y, toResult s = ok (x, y) ∧
      match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0)
    mk_pos_pair
    (fun x y (h : match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0) =>
     (Exists.intro x (Exists.intro y (And.intro (Eq.refl (ok (x, y))) h)) :
     ∃ (x' y' : Int), toResult (x, y) = ok (x', y') ∧
      match (x', y') with
      | (x, y) => x ≥ 0 ∧ y ≥ 0))
      is_pos

  #check Exists.intro
  --set_option pp.coercions false
  --set_option pp.all false
  --set_option pp.explicit true
  #print lifted_is_pos''
  #print Prod.rec
  /-
  Prod.casesOn (motive := fun s =>
    (match s with
    | (x, y) => x ≥ 0 ∧ y ≥ 0) →
    ∃ x y, ↑s = ok (x, y) ∧ x ≥ 0 ∧ y ≥ 0)
    mk_pos_pair (fun x y h => Exists.intro x (Exists.intro y ⟨Eq.refl (ok (x, y)), h⟩)) is_pos

  Prod.casesOn (motive := fun s =>
    (match s with
     | (x, y) => x ≥ 0 ∧ y ≥ 0) →
     ∃ x y, ↑s = ok (x, y) ∧ match (x, y) with | (x, y) => x ≥ 0 ∧ y ≥ 0)
    mk_pos_pair (fun x y pureThm => Exists.intro x (Exists.intro y ⟨Eq.refl (ok (x, y)), pureThm⟩)) is_pos
  -/
end Test

partial def destProdTy (x : Expr) : List Expr :=
  x.consumeMData.withApp fun f args =>
  if f.isConst ∧ f.constName = ``Prod ∧ args.size = 2 then
    let ty0 := args[0]!
    let ty1 := args[1]!
    ty0 :: destProdTy ty1
  else [x]

partial def destProdVal (x : Expr) : List Expr :=
  x.consumeMData.withApp fun f args =>
  if f.isConst ∧ f.constName = ``Prod.mk ∧ args.size = 4 then
    let val0 := args[2]!
    let val1 := args[3]!
    val0 :: destProdVal val1
  else [x]

/--
  Returns the expression and its type
-/
partial def mkProdsMatch' (xl : List Expr) (out outTy : Expr) (index : Nat := 0) : MetaM (Expr × Expr) :=
  match xl with
  | [] => do
    -- This would be unexpected
    throwError "mkProdsMatch: empty list of input parameters"
  | [x] => do
    -- In the example given for the explanations: this is the inner match case
    trace[Utils] "mkProdsMatch: [{x}]"
    let out ← mkLambdaFVars #[x] out
    let outTy ← mkArrowN #[x] outTy
    pure (out, outTy)
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
      match outTy  with
      | .sort _ | .lit _ | .const .. =>
        -- The type of the motive doesn't depend on the scrutinee
        mkLambdaFVars #[scrut] outTy
      | _ =>
        /- The type of the motive *may* depend on the scrutinee
           TODO: make this more efficient (we could change the output type of
           mkProdsMatch) -/
        mkProdsMatch (fst :: xl) outTy
    /-let motive ← do
      let out_ty ← inferType out
      mkLambdaFVars #[scrut] out_ty-/
    -- The final expression: putting everything together
    trace[Utils] "mkProdsMatch:\n  ({alpha})\n  ({beta})\n  ({motive})\n  ({scrut})\n  ({mk})"
    let sm ← mkAppOptM ``Prod.casesOn #[some alpha, some beta, some motive, some scrut, some mk]
    -- Abstracting the "scrut" variable
    let sm ← mkLambdaFVars #[scrut] sm
    trace[Utils] "mkProdsMatch: sm: {sm}"
    pure (sm, motive)

partial def mkProdsMatch'' (xl : List Expr) (out : Expr) (index : Nat := 0) : MetaM Expr :=
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
      /- Replace the pair in the type -/
      match out_ty  with
      | .sort _ | .lit _ | .const .. =>
        -- The type of the motive doesn't depend on the scrutinee
        mkLambdaFVars #[scrut] out_ty
      | _ =>
        /- The type of the motive *may* depend on the scrutinee
           TODO: make this more efficient (we could change the output type of
           mkProdsMatch) -/
        -- We need to replace the tuples
        let tval ← mkProdsVal (fst :: xl)
        trace[Utils] "mkProdsMatch: replacing tval ({tval}) in out_ty ({out_ty})"
        let out_ty ←
          mapVisit (fun _ e => do if e == tval then pure scrut else pure e) out_ty
        trace[Utils] "mkProdsMatch: after replacing tval: {out_ty}"
        mkProdsMatch (fst :: xl) out_ty
    -- The final expression: putting everything together
    trace[Utils] "mkProdsMatch:\n- alpha: {alpha}\n- beta: {beta}\n- motive: {motive}\n- scrut: {scrut}\n- mk: {mk}"
    let sm ← mkAppOptM ``Prod.casesOn #[some alpha, some beta, some motive, some scrut, some mk]
    -- Abstracting the "scrut" variable
    let sm ← mkLambdaFVars #[scrut] sm
    trace[Utils] "mkProdsMatch: sm: {sm}"
    pure sm

/-partial def mkProdsMatchWithType (mkOutTy : List Expr → Expr → MetaM Expr)
  (accXl : List Expr) (xl : List Expr)
  (scrut : Expr)
  (out : Expr) (index : Nat := 0) : MetaM Expr := do
  match xl with
  | [] => do
    -- This would be unexpected
    throwError "mkProdsMatchWithType: empty list of input parameters"
  | [x] => do
    -- In the example given for the explanations: this is the inner match case
    trace[Utils] "mkProdsMatchWithType: [{x}]"
    mkLambdaFVars #[x] out
  | fst :: xl => do
    trace[Utils] "mkProdsMatchWithType: [{fst}::{xl}]"
    let alpha ← inferType fst
    let beta ← mkProdsType xl
    let snd ← mkProdsMatch xl out (index + 1)
    let mk ← mkLambdaFVars #[fst] snd
    -- Introduce the "scrut" variable
    let scrut_ty ← mkProdType alpha beta
    withLocalDeclD (mkAnonymous "scrut" index) scrut_ty fun scrut => do
    trace[Utils] "mkProdsMatchWithType: scrut: ({scrut}) : ({← inferType scrut})"
    -- TODO: make the computation of the motive more efficient
    let motive ← do
      let out_ty ← inferType out
      /- Replace the pair in the type -/
      match out_ty  with
      | .sort _ | .lit _ | .const .. =>
        -- The type of the motive doesn't depend on the scrutinee
        mkLambdaFVars #[scrut] out_ty
      | _ =>
        /- The type of the motive *may* depend on the scrutinee
           TODO: make this more efficient (we could change the output type of
           mkProdsMatch) -/
        -- We need to replace the tuples
        let tval ← mkProdsVal (fst :: xl)
        trace[Utils] "mkProdsMatchWithType: replacing tval ({tval}) in out_ty ({out_ty})"
        let out_ty ←
          mapVisit (fun _ e => do if e == tval then pure scrut else pure e) out_ty
        trace[Utils] "mkProdsMatchWithType: after replacing tval: {out_ty}"
        mkProdsMatch (fst :: xl) out_ty
    -- The final expression: putting everything together
    trace[Utils] "mkProdsMatchWithType:\n- alpha: {alpha}\n- beta: {beta}\n- motive: {motive}\n- scrut: {scrut}\n- mk: {mk}"
    let sm ← mkAppOptM ``Prod.casesOn #[some alpha, some beta, some motive, some scrut, some mk]
    -- Abstracting the "scrut" variable
    let sm ← mkLambdaFVars #[scrut] sm
    trace[Utils] "mkProdsMatchWithType: sm: {sm}"
    pure sm-/

def getSortUniverse (x : Expr) : MetaM Level := do
  trace[Utils] "getSortUniverse: {x}"
  match ← inferType x with
  | .sort u => pure u
  | _ => throwError "Unexpected error: please report an issue"

def getTypeUniverse (x : Expr) : MetaM Level := do
  trace[Utils] "getTypeUniverse: {x}"
  match ← getSortUniverse x with
  | .succ u => pure u
  | _ => throwError "Unexpected error: please report an issue"

#check Expr
#check Prod.casesOn
#check Level
#check Expr.sort
partial def mkProdsMatchWithType (mkOutTy : List Expr → Expr → MetaM Expr)
  (accXl : List Expr) (xl : List Expr)
  (scrut : Expr)
  (out : Expr) (index : Nat := 0) : MetaM Expr := do
  match xl with
  | [] => do
    trace[Utils] "mkProdsMatchWithType: []"
    -- This would be unexpected
    throwError "mkProdsMatch: empty list of input parameters"
  | [x] => do
    -- A single variable: this is a degenerate case
    let fvId := x.fvarId!
    pure (mkLet (← fvId.getUserName) (← inferType x) scrut out)
  | [x, y] => do
    trace[Utils] "mkProdsMatchWithType: [{x}::{y}]"
    -- Exactly two variables: we introduce a single match
    let alpha ← inferType x
    let beta ← inferType y
    -- Introduce the motive
    let motive ← do
      -- We need to introduce an intermediate variable
      let scrutTy ← mkProdType alpha beta
      withLocalDeclD (mkAnonymous "scrut" index) scrutTy fun scrut => do
      let motive ← mkOutTy accXl.reverse scrut
      mkLambdaFVars #[scrut] motive
    trace[Utils] "mkProdsMatchWithType: motive: {motive}"
    let mk ← mkLambdaFVars #[x, y] out
    trace[Utils] "mkProdsMatchWithType: mk: {mk}"
    trace[Utils] "mkProdsMatchWithType: scrut: {scrut}"
    let m ← mkAppOptM ``Prod.casesOn #[alpha, beta, motive, scrut, mk]
    trace[Utils] "mkProdsMatchWithType: m: {m}"
    pure m
  | x :: xl => do
    throwError "TODO"
    /- -- Recursive case: we need stricly more than one match
    trace[Utils] "mkProdsMatchWithType: [{x}::{xl}]"
    let alpha ← inferType x
    let beta ← mkProdsType xl
    -- We introduce an intermediate scrutinee
    let scrut_ty ← mkProdType alpha beta
    withLocalDeclD (mkAnonymous "scrut" index) scrut_ty fun scrut => do
    let body ← mkProdsMatchWithType mkOutTy (x :: accXl) xl scrut out (index + 1)
    let mk ← mkLambdaFVars #[x, scrut] body
    --
    let accXl := x :: accXl
    let motive ← mkOutTy accXl.reverse scrut
    let motive ← mkLambdaFVars #[scrut] motive
    --
    let m ← mkAppOptM ``Prod.casesOn #[alpha, beta, motive, scrut, mk]
    pure m -/

#check mkFreshFVarId
#check @Exists.intro
#check Declaration
#check mkArrowN
#print Prod.casesOn
#check Prod.rec

#check Prod.exists

theorem congr_toResult_eq_ok {x y : α} {p : α → Prop} (h0 : p x) :
  ∃ y, Std.toResult x = Std.Result.ok y ∧ p y := by
  exists x




#check congrArg
theorem test (x y : α) (h : x = y) : y = x := by simp [h]
#print test

/-def mkToResult (x : Expr) : MetaM Expr := do
  --mkAppM ``Std.toResult #[x]
  let ty ← inferType x
  let u ← getTypeUniverse ty
  pure (mkAppN (.const ``Std.toResult [u]) #[ty, x])

def mkResultOk (x : Expr) : MetaM Expr := do
  --mkAppM ``Std.Result.ok #[x]
  let ty ← inferType x
  let u ← getTypeUniverse ty
  pure (mkAppN (.const ``Std.Result.ok [u]) #[ty, x])

def mkEqRefl (x : Expr) : MetaM Expr := do
  let ty ← inferType x
  let u ← getSortUniverse ty
  pure (mkAppN (.const ``Eq.refl [u]) #[ty, x])

#check Exists
def mkExists (ty x : Expr) : MetaM Expr := do
  let u ← getSortUniverse ty
  pure (mkAppN (.const ``Exists [u]) #[ty, x])

def mkExistsIntro (ty p w h : Expr) : MetaM Expr := do
  let u ← getSortUniverse ty
  pure (mkAppN (.const ``Exists.intro [u]) #[ty, p, w, h])-/

open Std Result
def tryGeneralize (pat : Syntax) (n : Name) : TermElabM Unit := do
  trace[Progress] "Name: {n}"
  let env ← getEnv
  let decl := env.constants.find! n
  -- Strip the quantifiers before elaborating the pattern
  forallTelescope decl.type.consumeMData fun fvars thm0 => do
  let (pat, _) ← Elab.Term.elabTerm pat none |>.run
  let pat ← instantiateMVars pat
  trace[Progress] "Elaborated pattern: {pat}"
  --
  existsTelescope pat.consumeMData fun _ eqMatch => do
  existsTelescope pat.consumeMData fun _ eqExists => do
  /- Destruct the equality. Note that there may not be a tuple, in which case
     we introduce a single variable -/
  let tryDestEq (eq : Expr) (k : Expr → Expr → TermElabM Unit) : TermElabM Unit := do
    match ← destEqOpt eq with
    | some (x, y) => k x y
    | none =>
      let pat := eq
      let ty ← inferType pat
      let name ← mkFreshUserName (.str .anonymous "x")
      withLocalDeclD name ty fun decompPat => do
      k pat decompPat
  tryDestEq eqMatch fun pat decompPatMatch => do
  tryDestEq eqExists fun _ decompPatExists => do
  trace[Progress] "Decomposed equality: {pat}, {decompPatMatch}"
  -- The decomp pattern should be a tuple
  let fvarsMatch : Array Expr := ⟨ destProdVal decompPatMatch ⟩
  let fvarsExists : Array Expr := ⟨ destProdVal decompPatExists ⟩
  /- Prepare the type of the final theorem -/
  let mkThmType (xl : List Expr) (scrut : Expr) : MetaM Expr := do
    let npatMatch ← mkProdsVal (xl++[scrut])
    -- Update the theorem statement to replace the pattern with the decomposed pattern
    let thmType ←
      mapVisit (fun _ e => do if e == pat then pure decompPatExists else pure e) thm0
    trace[Progress] "Theorem type without lifted equality: {thmType}"
    let pureThmType ←
      mapVisit (fun _ e => do if e == pat then pure npatMatch else pure e) thm0
    trace[Progress] "Pure theorem type: {pureThmType}"
    let toResultPat ← mkAppM ``Std.toResult #[npatMatch]
    let okDecompPat ← mkAppM ``Std.Result.ok #[decompPatExists]
    let eqType ← mkEq toResultPat okDecompPat
    let thmType := mkAnd eqType thmType
    trace[Progress] "Theorem type after lifting equality: {thmType}"
    -- Introduce the existentials
    let thmType ← Array.foldrM (fun fvar thmType => do
        let p ← mkLambdaFVars #[fvar] thmType
        mkAppM ``Exists #[p]
        ) thmType fvarsExists
    trace[Progress] "Theorem type after adding the existentials: {thmType}"
    -- Introduce the arrow
    let thmType ← mkArrow pureThmType thmType
    trace[Progress] "Theorem type after adding the arrow: {thmType}"
    pure thmType

  -- Update the theorem statement to replace the pattern with the decomposed pattern
  let pureThmType ←
    mapVisit (fun _ e => do if e == pat then pure decompPatMatch else pure e) thm0
  let pureThmName ← mkFreshUserName (.str .anonymous "pureThm")
  withLocalDeclD pureThmName pureThmType fun pureThm => do
  -- Introduce the equality
  --let toResultPat ← mkAppM ``Std.toResult #[patMatch]
  let okDecompPat ← mkAppM ``Std.Result.ok #[decompPatMatch]
  let eqExpr ← mkEqRefl okDecompPat
  let thm ← mkAppM ``And.intro #[eqExpr, pureThm]
  trace[Progress] "Theorem after introducing the lifted equality: {thm} : {← inferType thm}"
  let mkThmType' (toResultArg : Expr) (xl0 : List Expr) (xl1 : List Expr) : MetaM Expr := do
    let npatExists ← mkProdsVal (xl0 ++ xl1)
    -- Update the theorem statement to replace the pattern with the decomposed pattern
    let thmType ←
      mapVisit (fun _ e => do if e == pat then pure npatExists else pure e) thm0
    trace[Progress] "Theorem type without lifted equality: {thmType}"
    /-let pureThmType ←
      mapVisit (fun _ e => do if e == pat then pure npatMatch else pure e) thm0-/
    --trace[Progress] "Pure theorem type: {pureThmType}"
    let toResultPat ← mkAppM ``Std.toResult #[toResultArg]
    let okDecompPat ← mkAppM ``Std.Result.ok #[npatExists]
    let eqType ← mkEq toResultPat okDecompPat
    let thmType := mkAnd eqType thmType
    trace[Progress] "Theorem type after lifting equality: {thmType}"
    -- Introduce the existentials, only for the suffix of the list of variables
    let thmType ← List.foldrM (fun fvar thmType => do
        let p ← mkLambdaFVars #[fvar] thmType
        mkAppM ``Exists #[p]
        ) thmType xl1
    trace[Progress] "Theorem type after adding the existentials: {thmType}"
    -- Introduce the arrow
    --let thmType ← mkArrow pureThmType thmType
    --trace[Progress] "Theorem type after adding the arrow: {thmType}"
    pure thmType
  -- We need to precise the theorem type when introducting the existentials
  let thmType ← do
    let thmType ←
      mapVisit (fun _ e => do if e == pat then pure decompPatExists else pure e) thm0
    trace[Progress] "Theorem type without lifted equality: {thmType}"
    let pureThmType ←
      mapVisit (fun _ e => do if e == pat then pure decompPatMatch else pure e) thm0
    trace[Progress] "Pure theorem type: {pureThmType}"
    let toResultPat ← mkAppM ``Std.toResult #[decompPatMatch]
    let okDecompPat ← mkAppM ``Std.Result.ok #[decompPatExists]
    let eqType ← mkEq toResultPat okDecompPat
    pure (mkAnd eqType thmType)
  trace[Progress] "Theorem type after lifting the equality: {thmType}"
  -- Introduce the existentials
  let rec introExists (xl0 xl1 : List (Expr × Expr)) : MetaM Expr := do
    match xl1 with
    | [] => pure thm
    | fvarPair :: xl1 =>
      let thm ← introExists (fvarPair :: xl0) xl1
      let (fvarMatch, fvarExists) := fvarPair
      let α ← inferType fvarMatch
      let thmType ← mkThmType' decompPatMatch (fvarExists :: (List.unzip xl0).fst).reverse (List.unzip xl1).snd
      let p ← mkLambdaFVars #[fvarExists] thmType
      let x := fvarMatch
      let h := thm
      trace[Progress] "introExists: about to insert existential:\n- α: {α}\n- p: {p}\n- x: {x}\n- h: {h}"
      let thm ← mkAppOptM ``Exists.intro #[α, p, x, h]
      trace[Progress] "introExists: resulting theorem:\n{thm}\n  :\n{← inferType thm}"
      pure thm
  let thm ← introExists [] (List.zip fvarsMatch.toList fvarsExists.toList)
  trace[Progress] "Theorem after introducing the existentials: {thm} :\n{← inferType thm}"
  -- Introduce the λ which binds the pure theorem
  let thm ← mkLambdaFVars #[pureThm] thm
  trace[Progress] "Theorem after introducing the lambda: {thm} :\n{← inferType thm}"
  -- Introduce the matches
  let thm ← mkProdsMatch fvarsMatch.toList thm
  trace[Progress] "Theorem after introducing the matches: {thm} :\n{← inferType thm}"
  -- Add the scrutinee
  let thm := mkApp thm pat
  --let thm ← mkProdsMatchWithType mkThmType [] fvarsMatch.toList pat thm
  trace[Progress] "Theorem after introducing the scrutinee: {thm} :\n{← inferType thm}"
  -- Apply the pure theorem
  let thm := mkAppN thm #[.const decl.name (List.map Level.param decl.levelParams)]
  trace[Progress] "Theorem after introducing the matches and the app: {thm} :\n{← inferType thm}"
  let thm ← mkLambdaFVars fvars thm
  /- Prepare the theorem type -/
  let thmType ← do
    let thmType ← mkThmType' pat [] fvarsExists.toList
    mkForallFVars fvars thmType
  --let thmType ← inferType thm
  trace[Progress] "Final theorem: {thm}\n  :\n{thmType}"
  -- Save the auxiliary theorem
  let auxDecl : TheoremVal := {
    name := Name.str decl.name "progress_spec"
    levelParams := decl.levelParams
    type := thmType
    value := thm
  }
  addDecl (.thmDecl auxDecl)

#check mkForallFVars

local elab "#try_generalize" "(" pat:term ")" id:ident : command => do
  Lean.Elab.Command.runTermElabM (fun _ => do
  let some cs ← Term.resolveId? id | throwError m!"Unknown id: {id}"
  let name := cs.constName!
  tryGeneralize pat name)

open Test
set_option trace.Progress true in
set_option trace.Utils true in
#try_generalize (∃ x y, Test.mk_pos_pair = (x, y)) Test.is_pos

#check Int × Int
#check Test.is_pos.progress_spec


/-
def tryGeneralize (pat : Syntax) (n : Name) : TermElabM Unit := do
  trace[Progress] "Name: {n}"
  let env ← getEnv
  let decl := env.constants.find! n
  -- Strip the quantifiers before elaborating the pattern
  forallTelescope decl.type.consumeMData fun fvars thm0 => do
  let (pat, _) ← Elab.Term.elabTerm pat none |>.run
  trace[Progress] "Elaborated pattern: {pat}"
  --
  existsTelescope pat.consumeMData fun fvarsPat eq => do
  /- Destruct the equality. Note that there may not be a tuple, in which case
     we introduce a single variable -/
  let tryDestEq (k : Expr → Expr → TermElabM Unit) : TermElabM Unit := do
    match ← destEqOpt eq with
    | some (x, y) => k x y
    | none =>
      let pat := eq
      let ty ← inferType pat
      let name ← mkFreshUserName (.str .anonymous "x")
      withLocalDeclD name ty fun decompPat => do
      k pat decompPat
  tryDestEq fun pat decompPat => do
  trace[Progress] "Decomposed equality: {pat}, {decompPat}"
  -- The decomp pattern should be a tuple
  let pats := destProdVal decompPat
  trace[Progress] "Decomposed pattern: {pats}"
  -- Update the theorem statement to replace the pattern with the decomposed pattern
  let thm1 ←
    mapVisit (fun _ e => do if e == pat then pure decompPat else pure e) thm0
  trace[Progress] "Updated theorem statement: {thm1}"
  -- Dive into the λ which binds the pure theorem
  let pureThmName ← mkFreshUserName (.str .anonymous "pureThm")
  withLocalDeclD pureThmName thm1 fun pureThm => do
  -- Introduce the equality
  let okDecompPat ← mkAppM ``Std.Result.ok #[decompPat]
  let toResultPat ← mkAppM ``Std.toResult #[pat]
  let eqExpr ← mkAppM ``Eq.refl #[okDecompPat]
  --let eqType ← mkAppM ``Eq #[toResultPat, okDecompPat]
  let thm ← mkAppOptM ``And.intro #[none, none, eqExpr, pureThm]
  --let thm ← mkAppOptM ``And.intro #[none, none, eqExpr, pureThm]
  trace[Progress] "Theorem after introducing the lifted equality: {thm} : {← inferType thm}"
  /- Prepare the type of the final theorem -/
  let mkThmType (xl : List Expr) (scrut : Expr) : MetaM Expr := do
    let pat0 := pat
    let pat ← mkProdsVal (xl++[scrut])
    -- Update the theorem statement to replace the pattern with the decomposed pattern
    let thmType ←
      mapVisit (fun _ e => do if e == pat0 then pure decompPat else pure e) thm0
    let pureThmType ←
      mapVisit (fun _ e => do if e == pat0 then pure pat else pure e) thm0
    trace[Progress] "Theorem type without lifted equality: {thmType}"
    -- Dive into the λ which binds the pure theorem
    let pureThmName ← mkFreshUserName (.str .anonymous "pureThm")
    withLocalDeclD pureThmName pureThmType fun pureThm => do
    let toResultPat ← mkAppM ``Std.toResult #[pat]
    let eqType ← mkEq toResultPat okDecompPat
    let thmType := mkAnd eqType thmType
    trace[Progress] "Theorem type after lifting equality: {thmType}"
    -- Introduce the existentials
    let thmType ← Array.foldrM (fun fvar thmType => do
        let p ← mkLambdaFVars #[fvar] thmType
        mkAppOptM ``Exists #[← inferType fvar, p]
        ) thmType fvarsPat
    trace[Progress] "Theorem type after adding the existentials: {thmType}"
    -- Introduce the arrow
    let thmType ← mkArrow (← inferType pureThm) thmType
    trace[Progress] "Theorem type after adding the arrow: {thmType}"
    pure thmType
  let (thmType, thmAndEqType) ← do
    let thmType := thm1
    trace[Progress] "Theorem type without lifted equality: {thmType}"
    let eqType ← mkEq toResultPat okDecompPat
    trace[Progress] "Theorem type after lifting equality: {thmType}"
    let thmType := mkAnd eqType thmType
    let thmAndEqType := thmType
    let thmAndEqType ← mkArrow (← inferType pureThm) thmAndEqType
    -- Introduce the existentials
    let thmType ← Array.foldrM (fun fvar thmType => do
        let p ← mkLambdaFVars #[fvar] thmType
        mkAppOptM ``Exists #[← inferType fvar, p]
        ) thmType fvarsPat
    pure (thmType, thmAndEqType)
  trace[Progress] "Theorem and eq type: {thmAndEqType}"
  trace[Progress] "Theorem type: {thmType}"
  -- Introduce the existentials
  let thm ←
    Array.foldrM (fun fvar thm => do
      let p ← mkLambdaFVars #[fvar] (← inferType thm)
      mkAppOptM ``Exists.intro #[← inferType fvar, p, fvar, thm]
      ) thm fvarsPat
  trace[Progress] "Theorem after introducing the existentials: {thm} :\n{← inferType thm}"
  -- Introduce the λ which binds the pure theorem
  let thm ← mkLambdaFVars #[pureThm] thm
  trace[Progress] "Theorem after introducing the lambda: {thm} :\n{← inferType thm}"
  -- Introduce the matches
  let thm ← mkProdsMatchWithType mkThmType [] pats pat thm -- TODO: should be mkProdsMatch
  trace[Progress] "Theorem after introducing the matches: {thm} :\n{← inferType thm}"
  let thm ← mkAppM' thm #[pat]
  trace[Progress] "Theorem after introducing the matches and the app: {thm} :\n{← inferType thm}"
  -- Apply the pure theorem
  let thm := mkAppN thm #[.const decl.name (List.map Level.param decl.levelParams)]
  let thm ← mkLambdaFVars fvars thm
  trace[Progress] "Final theorem: {thm} :\n{← inferType thm}"
  /- -- Prepare the type of the final theorem
  let thmType := thm1
  trace[Progress] "Theorem type without lifted equality: {thmType}"
  let eqType ← mkEq toResultPat okDecompPat
  trace[Progress] "Theorem type after lifting equality: {thmType}"
  let thmType := mkAnd eqType thmType
  -- Introduce the existentials
  let thmType ← Array.foldrM (fun fvar thmType => do
      let p ← mkLambdaFVars #[fvar] thmType
      mkAppOptM ``Exists #[← inferType fvar, p]
      ) thmType fvarsPat
  trace[Progress] "Theorem type: {thmType}" -/
  --let pureThmType ← mkArrowN fvars (← inferType existsThm)
  -- Save the auxiliary theorem
  let auxDecl : TheoremVal := {
    name := Name.str decl.name "progress_spec"
    levelParams := decl.levelParams
    type := thmType
    value := thm
  }
  addDecl (.thmDecl auxDecl)
  --
  --let thm ← mkLambdaFVars #[pureThm] pureThm
  pure ()
  /--- Introduce matches
  let rec introMatches (decompPat : Expr) (k : TermElabM Unit) := do
    match decompPat with
    | .
  pure ()-/
-/

/-- Auxiliary helper: prove the auxiliary theorem (generates the proof term) -/
private def pspecPureProve (pureThm : ConstantInfo) (th : Expr) : TermElabM Expr := do
  let goal ← mkFreshExprMVar (some th)
  let prove : TacticM Unit := do
    let goal ← getMainGoal
    let (_, goal) ← goal.intros
    setGoals [goal]
    let lctx ← getLCtx
    -- Introduce the lemma
    let levelParams := List.map Level.param pureThm.levelParams
    let pureThmExpr := Expr.const pureThm.name levelParams
    let pureThmExpr := mkAppN pureThmExpr lctx.getFVars
    let pureThmExprName ← mkFreshUserName (.str .anonymous "auxThm")
    withLetDecl pureThmExprName (← inferType pureThmExpr) pureThmExpr fun _ => do
    -- We simply call the simplifier
    let simpOnly := true
    let config : Simp.Config := {}
    let simprocs := []
    let declsToUnfold := []
    let thms := []
    let loc := Utils.Location.targets #[] true
    let pureThm ← getFVarFromUserName pureThmExprName
    simpAt simpOnly config simprocs declsToUnfold thms [pureThm.fvarId!] loc
    let lctx ← getLCtx
    let hypsToUse := lctx.getFVarIds
    simpAt simpOnly config simprocs declsToUnfold thms hypsToUse.toList loc
  let ngoals ← Tactic.run goal.mvarId! prove
  /- There should be no remaining goals -/
  if ngoals == [] then
    pure (← instantiateMVars goal)
  else
    throwError "Error while elaborating 'progress_spec': we could not prove the auxiliary theorem"

/- Initiliaze the `progress_pure` attribute, which lifts lemmas about pure functions to
   `progress` lemmas.

   For instance, if we annotate the following theorem with `progress_pure` (note the `let` binding
   which must be at the beginning of the theorem statement):
   ```
   @[progress_pure]
   theorem U32.wrapping_add_eq (x y : U32) :
    let z := wrapping_add x y
    z.bv = x.bv + y.bv
   ```
   `progress_pure` introduces the following intermediate definition:
   ```
   @[progress_pure]
   theorem U32.wrapping_add_eq.progress_spec (x y : U32) :
    ∃ z, ↑(wrapping_add x y) = ok z ∧
    z.bv = x.bv + y.bv
   ```
 -/
initialize pspecPureAttribute : PSpecAttr ← do
  let ext ← mkDiscrTreeExtension `pspecMap
  let attrImpl : AttributeImpl := {
    name := `progress_pure
    descr := "Adds lifted version of pure theorems to the `progress_pure` databse"
    add := fun thName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "invalid attribute 'progress_pure', must be global"
      -- Lookup the theorem
      let env ← getEnv
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef thName (pure ()) do
        trace[Progress] "Registering pure `progress` theorem for {thName}"
        let thDecl := env.constants.find! thName
        -- Lift the theorem statement
        let liftedThm ← MetaM.run' (liftThm thDecl.type.consumeMData)
        -- Prove the lifted statement
        let value ← liftM (pspecPureProve thDecl liftedThm)
        -- Save an auxiliary theorem for the lifted statement
        let liftedThmName := Name.str thName "progress_spec"
        let liftedThmDecl := Declaration.defnDecl {
          name := Name.str thName "progress_spec"
          levelParams := thDecl.levelParams
          type := liftedThm
          value := value
          hints := .opaque
          safety := .safe
          all := [liftedThmName]
        }
        addDecl liftedThmDecl
        -- Save the auxiliary theorem to the `progress` database
        saveProgressSpecFromThm pspecAttr.ext attrKind liftedThmName
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

#check elabTerminationHints
end Progress

end Aeneas
