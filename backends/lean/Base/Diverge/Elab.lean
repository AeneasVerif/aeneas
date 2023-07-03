import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
import Base.Diverge.Base
import Base.Diverge.ElabBase

namespace Diverge

/- Automating the generation of the encoding and the proofs so as to use nice
   syntactic sugar. -/

syntax (name := divergentDef)
  declModifiers "divergent" "def" declId ppIndent(optDeclSig) declVal : command

open Lean Elab Term Meta Primitives Lean.Meta

set_option trace.Diverge.def true
-- set_option trace.Diverge.def.valid true
-- set_option trace.Diverge.def.sigmas true
set_option trace.Diverge.def.unfold true

/- The following was copied from the `wfRecursion` function. -/

open WF in

def mkList (xl : List Expr) (ty : Expr) : MetaM Expr :=
  match xl with
  | [] =>
    mkAppOptM ``List.nil #[some ty]
  | x :: tl => do
    let tl ← mkList tl ty
    mkAppOptM ``List.cons #[some ty, some x, some tl]

def mkProd (x y : Expr) : MetaM Expr :=
  mkAppM ``Prod.mk #[x, y]

def mkInOutTy (x y : Expr) : MetaM Expr :=
  mkAppM ``FixI.mk_in_out_ty #[x, y]

-- TODO: is there already such a utility somewhere?
-- TODO: change to mkSigmas
def mkProds (tys : List Expr) : MetaM Expr :=
  match tys with
  | [] => do pure (Expr.const ``PUnit.unit [])
  | [ty] => do pure ty
  | ty :: tys => do
    let pty ← mkProds tys
    mkAppM ``Prod.mk #[ty, pty]

-- Return the `a` in `Return a`
def get_result_ty (ty : Expr) : MetaM Expr :=
  ty.withApp fun f args => do
  if ¬ f.isConstOf ``Result ∨ args.size ≠ 1 then
    throwError "Invalid argument to get_result_ty: {ty}"
  else
    pure (args.get! 0)

-- Group a list of expressions into a dependent tuple
def mkSigmas (xl : List Expr) : MetaM Expr :=
  match xl with
  | [] => do
    trace[Diverge.def.sigmas] "mkSigmas: []"
    pure (Expr.const ``PUnit.unit [])
  | [x] => do
    trace[Diverge.def.sigmas] "mkSigmas: [{x}]"
    pure x
  | fst :: xl => do
    trace[Diverge.def.sigmas] "mkSigmas: [{fst}::{xl}]"
    let alpha ← Lean.Meta.inferType fst
    let snd ← mkSigmas xl
    let snd_ty ← inferType snd
    let beta ← mkLambdaFVars #[fst] snd_ty
    trace[Diverge.def.sigmas] "mkSigmas:\n{alpha}\n{beta}\n{fst}\n{snd}"
    mkAppOptM ``Sigma.mk #[some alpha, some beta, some fst, some snd]

/- Generate the input type of a function body, which is a sigma type (i.e., a
   dependent tuple) which groups all its inputs.

   Example:
   - xl = [(a:Type), (ls:List a), (i:Int)]

   Generates:
   `(a:Type) × (ls:List a) × (i:Int)`

 -/
def mkSigmasTypesOfTypes (xl : List Expr) : MetaM Expr :=
  match xl with
  | [] => do
    trace[Diverge.def.sigmas] "mkSigmasOfTypes: []"
    pure (Expr.const ``PUnit.unit [])
  | [x] => do
    trace[Diverge.def.sigmas] "mkSigmasOfTypes: [{x}]"
    let ty ← Lean.Meta.inferType x
    pure ty
  | x :: xl => do
    trace[Diverge.def.sigmas] "mkSigmasOfTypes: [{x}::{xl}]"
    let alpha ← Lean.Meta.inferType x
    let sty ← mkSigmasTypesOfTypes xl
    trace[Diverge.def.sigmas] "mkSigmasOfTypes: [{x}::{xl}]: alpha={alpha}, sty={sty}"
    let beta ← mkLambdaFVars #[x] sty
    trace[Diverge.def.sigmas] "mkSigmasOfTypes: ({alpha}) ({beta})"
    mkAppOptM ``Sigma #[some alpha, some beta]

def mk_indexed_name (index : Nat) : Name := .num (.str .anonymous "_uniq") index

/- Given a list of values `[x0:ty0, ..., xn:ty1]` where every `xi` might use the previous
   `xj` (j < i) and a value `out` which uses `x0`, ..., `xn`, generate the following
   expression:
   ```
   fun x:((x0:ty0) × ... × (xn:tyn) => -- **Dependent** tuple
   match x with
   | (x0, ..., xn) => out
   ```
   
   The `index` parameter is used for naming purposes: we use it to numerotate the
   bound variables that we introduce.

   Example:
   ========
   More precisely:
   - xl = `[a:Type, ls:List a, i:Int]`
   - out = `a`
   - index = 0

   generates:
   ```
   match scrut0 with
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
    throwError "mkSigmasMatch: empyt list of input parameters"
  | [x] => do
    -- In the explanations above: inner match case
    trace[Diverge.def.sigmas] "mkSigmasMatch: [{x}]"
    mkLambdaFVars #[x] out
  | fst :: xl => do
    -- In the explanations above: outer match case
    -- Remark: for the naming purposes, we use the same convention as for the
    -- fields and parameters in `Sigma.casesOn and `Sigma.mk
    trace[Diverge.def.sigmas] "mkSigmasMatch: [{fst}::{xl}]"
    let alpha ← Lean.Meta.inferType fst
    let snd_ty ← mkSigmasTypesOfTypes xl
    let beta ← mkLambdaFVars #[fst] snd_ty
    let snd ← mkSigmasMatch xl out (index + 1)
    let scrut_ty ← mkSigmasTypesOfTypes (fst :: xl)
    withLocalDeclD (mk_indexed_name index) scrut_ty fun scrut => do
    let mk ← mkLambdaFVars #[fst] snd
    trace[Diverge.def.sigmas] "mkSigmasMatch: scrut: ({scrut}) : ({← inferType scrut})"
    -- TODO: make the computation of the motive more efficient
    let motive ← do
      let out_ty ← inferType out
      match out_ty  with
      | .sort _ | .lit _ | .const .. =>
        -- The type of the motive doesn't depend on the scrutinee
        mkLambdaFVars #[scrut] out_ty
      | _ =>
        -- The type of the motive *may* depend on the scrutinee
        -- TODO: make this more efficient (we could change the output type of
        -- mkSigmasMatch
        mkSigmasMatch (fst :: xl) out_ty
    trace[Diverge.def.sigmas] "mkSigmasMatch:\n  ({alpha})\n  ({beta})\n  ({motive})\n  ({scrut})\n  ({mk})"
    let sm ← mkAppOptM ``Sigma.casesOn #[some alpha, some beta, some motive, some scrut, some mk]
    let sm ← mkLambdaFVars #[scrut] sm
    trace[Diverge.def.sigmas] "mkSigmasMatch: sm: {sm}"
    pure sm

/- Small tests for list_nth: give a model of what `mkSigmasMatch` should generate -/
private def list_nth_out_ty2 (a :Type) (scrut1: @Sigma (List a) (fun (_ls : List a) => Int)) :=
  @Sigma.casesOn (List a)
                 (fun (_ls : List a) => Int)
                 (fun (_scrut1:@Sigma (List a) (fun (_ls : List a) => Int)) => Type)
                 scrut1
                 (fun (_ls : List a) (_i : Int) => Diverge.Primitives.Result a)

private def list_nth_out_ty1 (scrut0 : @Sigma (Type) (fun (a:Type) =>
                      @Sigma (List a) (fun (_ls : List a) => Int))) :=
  @Sigma.casesOn (Type)
                 (fun (a:Type) => @Sigma (List a) (fun (_ls : List a) => Int))
                 (fun (_scrut0:@Sigma (Type) (fun (a:Type) => @Sigma (List a) (fun (_ls : List a) => Int))) => Type)
                 scrut0
                 (fun (a : Type) (scrut1: @Sigma (List a) (fun (_ls : List a) => Int)) =>
                  list_nth_out_ty2 a scrut1)
/- -/

-- TODO: move
-- TODO: we can use Array.mapIdx
@[specialize] def mapiAux (i : Nat) (f : Nat → α → β) : List α → List β
  | []    => []
  | a::as => f i a :: mapiAux (i+1) f as

@[specialize] def mapi (f : Nat → α → β) : List α → List β := mapiAux 0 f

-- Return the expression: `Fin n`
-- TODO: use more
def mkFin (n : Nat) : Expr :=
  mkAppN (.const ``Fin []) #[.lit (.natVal n)]

-- Return the expression: `i : Fin n`
def mkFinVal (n i : Nat) : MetaM Expr := do
  let n_lit : Expr := .lit (.natVal (n - 1))
  let i_lit : Expr := .lit (.natVal i)
  -- We could use `trySynthInstance`, but as we know the instance that we are
  -- going to use, we can save the lookup
  let ofNat ← mkAppOptM ``Fin.instOfNatFinHAddNatInstHAddInstAddNatOfNat #[n_lit, i_lit]
  mkAppOptM ``OfNat.ofNat #[none, none, ofNat]

-- TODO: remove?
def mkFinValOld (n i : Nat) : MetaM Expr := do
  let finTy := mkFin n
  let ofNat ← mkAppM ``OfNat #[finTy, .lit (.natVal i)]
  match ← trySynthInstance ofNat with
  | LOption.some x =>
    mkAppOptM ``OfNat.ofNat #[none, none, x]
  | _ => throwError "mkFinVal: could not synthesize an instance of {ofNat} "

/- Generate and declare as individual definitions the bodies for the individual funcions:
   - replace the recursive calls with calls to the continutation `k`
   - make those bodies take one single dependent tuple as input

   We name the declarations: "[original_name].body".
   We return the new declarations.
 -/
def mkDeclareUnaryBodies (grLvlParams : List Name) (kk_var : Expr)
  (preDefs : Array PreDefinition) :
  MetaM (Array Expr) := do
  let grSize := preDefs.size

  -- Compute the map from name to index - the continuation has an indexed type:
  -- we use the index (a finite number of type `Fin`) to control the function
  -- we call at the recursive call
  let nameToId : HashMap Name Nat :=
    let namesIds := mapi (fun i d => (d.declName, i)) preDefs.toList
    HashMap.ofList namesIds

  trace[Diverge.def.genBody] "nameToId: {nameToId.toList}"

  -- Auxiliary function to explore the function bodies and replace the
  -- recursive calls
  let visit_e (e : Expr) : MetaM Expr := do
    trace[Diverge.def.genBody] "visiting expression: {e}"
    match e with
    | .app .. => do
      e.withApp fun f args => do
        trace[Diverge.def.genBody] "this is an app: {f} {args}"
        -- Check if this is a recursive call
        if f.isConst then
          let name := f.constName!
          match nameToId.find? name with
          | none => pure e
          | some id =>
            -- This is a recursive call: replace it
            -- Compute the index
            let i ← mkFinVal grSize id
            -- Put the arguments in one big dependent tuple
            let args ← mkSigmas args.toList
            mkAppM' kk_var #[i, args]
        else
          -- Not a recursive call: do nothing
          pure e
     | .const name _ =>
       -- Sanity check: we eliminated all the recursive calls
       if (nameToId.find? name).isSome then
         throwError "mkUnaryBodies: a recursive call was not eliminated"
       else pure e
     | _ => pure e

  -- Explore the bodies
  preDefs.mapM fun preDef => do
    -- Replace the recursive calls
    let body ← mapVisit visit_e preDef.value

    -- Change the type
    lambdaLetTelescope body fun args body => do
    let body ← mkSigmasMatch args.toList body 0

    -- Add the declaration
    let value ← mkLambdaFVars #[kk_var] body
    let name := preDef.declName.append "sbody"
    let levelParams := grLvlParams
    let decl := Declaration.defnDecl {
      name := name
      levelParams := levelParams
      type := ← inferType value -- TODO: change the type
      value := value
      hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
      safety := .safe
      all := [name]
    }
    addDecl decl
    trace[Diverge.def] "individual body of {preDef.declName}: {body}"
    -- Return the constant
    let body := Lean.mkConst name (levelParams.map .param)
    -- let body ← mkAppM' body #[kk_var]
    trace[Diverge.def] "individual body (after decl): {body}"
    pure body

-- Generate a unique function body from the bodies of the mutually recursive group,
-- and add it as a declaration in the context.
-- We return the list of bodies (of type `Funs ...`) and the mutually recursive body.
def mkDeclareMutRecBody (grName : Name) (grLvlParams : List Name)
  (kk_var i_var : Expr)
  (in_ty out_ty : Expr) (inOutTys : List (Expr × Expr))
  (bodies : Array Expr) : MetaM (Expr × Expr) := do
  -- Generate the body
  let grSize := bodies.size
  let finTypeExpr := mkFin grSize
  -- TODO: not very clean
  let inOutTyType ← do
    let (x, y) := inOutTys.get! 0
    inferType (← mkInOutTy x y)
  let rec mkFuns (inOutTys : List (Expr × Expr)) (bl : List Expr) : MetaM Expr :=
    match inOutTys, bl with
    | [], [] =>
      mkAppOptM ``FixI.Funs.Nil #[finTypeExpr, in_ty, out_ty]
    | (ity, oty) :: inOutTys, b :: bl => do
      -- Retrieving ity and oty - this is not very clean
      let inOutTysExpr ← mkList (← inOutTys.mapM (λ (x, y) => mkInOutTy x y)) inOutTyType
      let fl ← mkFuns inOutTys bl
      mkAppOptM ``FixI.Funs.Cons #[finTypeExpr, in_ty, out_ty, ity, oty, inOutTysExpr, b, fl]
    | _, _ => throwError "mkDeclareMutRecBody: `tys` and `bodies` don't have the same length"
  let bodyFuns ← mkFuns inOutTys bodies.toList
  -- Wrap in `get_fun`
  let body ← mkAppM ``FixI.get_fun #[bodyFuns, i_var, kk_var]
  -- Add the index `i` and the continuation `k` as a variables
  let body ← mkLambdaFVars #[kk_var, i_var] body
  trace[Diverge.def] "mkDeclareMutRecBody: body: {body}"
  -- Add the declaration
  let name := grName.append "mut_rec_body"
  let levelParams := grLvlParams
  let decl := Declaration.defnDecl {
    name := name
    levelParams := levelParams
    type := ← inferType body
    value := body
    hints := ReducibilityHints.regular (getMaxHeight (← getEnv) body + 1)
    safety := .safe
    all := [name]
  }
  addDecl decl
  -- Return the constant
  pure (bodyFuns, Lean.mkConst name (levelParams.map .param))

def isCasesExpr (e : Expr) : MetaM Bool := do
  let e := e.getAppFn
  if e.isConst then
    return isCasesOnRecursor (← getEnv) e.constName
  else return false

structure MatchInfo where
  matcherName       : Name
  matcherLevels     : Array Level
  params            : Array Expr
  motive            : Expr
  scruts            : Array Expr
  branchesNumParams : Array Nat
  branches          : Array Expr

instance : ToMessageData MatchInfo where
  -- This is not a very clean formatting, but we don't need more
  toMessageData := fun me => m!"\n- matcherName: {me.matcherName}\n- params: {me.params}\n- motive: {me.motive}\n- scruts: {me.scruts}\n- branchesNumParams: {me.branchesNumParams}\n- branches: {me.branches}"

-- An expression which doesn't use the continuation kk is valid
def proveNoKExprIsValid (k_var : Expr) (e : Expr) : MetaM Expr := do
  trace[Diverge.def.valid] "proveNoKExprIsValid: {e}"
  let eIsValid ← mkAppM ``FixI.is_valid_p_same #[k_var, e]
  trace[Diverge.def.valid] "proveNoKExprIsValid: result:\n{eIsValid}:\n{← inferType eIsValid}"
  pure eIsValid

mutual

partial def proveExprIsValid (k_var kk_var : Expr) (e : Expr) : MetaM Expr := do
  trace[Diverge.def.valid] "proveValid: {e}"
  match e with
  | .const _ _ => throwError "Unimplemented" -- Shouldn't get there?
  | .bvar _
  | .fvar _
  | .lit _
  | .mvar _
  | .sort _ => throwError "Unreachable"
  | .lam .. => throwError "Unimplemented"
  | .forallE .. => throwError "Unreachable" -- Shouldn't get there
  | .letE dName dTy dValue body _nonDep => do
    -- Introduce a local declaration for the let-binding
    withLetDecl dName dTy dValue fun decl => do
    let isValid ← proveExprIsValid k_var kk_var body
    -- Add the let-binding around.
    -- Rem.: the let-binding should be *inside* the `is_valid_p`, not outside,
    -- but because it reduces in the end it doesn't matter. More precisely:
    -- `P (let x := v in y)` and `let x := v in P y` reduce to the same expression.
    mkLetFVars #[decl] isValid
  | .mdata _ b => proveExprIsValid k_var kk_var b
  | .proj _ _ _ =>
    -- The projection shouldn't use the continuation
    proveNoKExprIsValid k_var e
  | .app .. =>
    e.withApp fun f args => do
      -- There are several cases: first, check if this is a match/if
      -- The expression is a (dependent) if then else
      let isIte := e.isIte
      if isIte || e.isDIte then do
        e.withApp fun f args => do
        trace[Diverge.def.valid] "ite/dite: {f}:\n{args}"
        if args.size ≠ 5 then
           throwError "Wrong number of parameters for {f}: {args}"
        let cond := args.get! 1
        let dec := args.get! 2
        -- Prove that the branches are valid
        let br0 := args.get! 3
        let br1 := args.get! 4
        let proveBranchValid (br : Expr) : MetaM Expr :=
          if isIte then proveExprIsValid k_var kk_var br
          else do
            -- There is a lambda -- TODO: how do we remove exacly *one* lambda?
            lambdaLetTelescope br fun xs br => do
            let x := xs.get! 0
            let xs := xs.extract 1 xs.size
            let br ← mkLambdaFVars xs br
            let brValid ← proveExprIsValid k_var kk_var br
            mkLambdaFVars #[x] brValid
        let br0Valid ← proveBranchValid br0
        let br1Valid ← proveBranchValid br1
        let const := if isIte then ``FixI.is_valid_p_ite else ``FixI.is_valid_p_dite
        let eIsValid ← mkAppOptM const #[none, none, none, none, some k_var, some cond, some dec, none, none, some br0Valid, some br1Valid]
        trace[Diverge.def.valid] "ite/dite: result:\n{eIsValid}:\n{← inferType eIsValid}"
        pure eIsValid
      -- The expression is a match (this case is for when the elaborator
      -- introduces auxiliary definitions to hide the match behind syntactic
      -- sugar)
      else if let some me := ← matchMatcherApp? e then do
        trace[Diverge.def.valid]
          "matcherApp:
           - params: {me.params}
           - motive: {me.motive}
           - discrs: {me.discrs}
           - altNumParams: {me.altNumParams}
           - alts: {me.alts}
           - remaining: {me.remaining}"
        -- matchMatcherApp has already done the work for us
        if me.remaining.size ≠ 0 then
          throwError "MatcherApp: non empty remaining array: {me.remaining}"
        let me : MatchInfo := {
          matcherName := me.matcherName
          matcherLevels := me.matcherLevels
          params := me.params
          motive := me.motive
          scruts := me.discrs
          branchesNumParams := me.altNumParams
          branches := me.alts
        }
        proveMatchIsValid k_var kk_var me
      -- The expression is a raw match (this case is for when the expression
      -- is a direct call to the primitive `casesOn` function, without
      -- syntactic sugar)
      else if ← isCasesExpr f then do
        trace[Diverge.def.valid] "rawMatch: {e}"
        -- The casesOn definition is always of the following shape:
        -- input parameters (implicit parameters), then motive (implicit), 
        -- scrutinee (explicit), branches (explicit).
        let matcherName := f.constName!
        let matcherLevels := f.constLevels!.toArray
        -- Find the first explicit parameter: this is the scrutinee
        forallTelescope (← inferType f) fun xs _ => do
        let rec findFirstExplicit (i : Nat) : MetaM Nat := do
          if i ≥ xs.size then throwError "Unexpected: could not find an explicit parameter"
          else
            let x := xs.get! i
            let xFVarId := x.fvarId!
            let localDecl ← xFVarId.getDecl
            match localDecl.binderInfo with
            | .default => pure i
            | _ => findFirstExplicit (i + 1)
        let scrutIdx ← findFirstExplicit 0
        -- Split the arguments
        let params := args.extract 0 (scrutIdx - 1)
        let motive := args.get! (scrutIdx - 1)
        let scrut := args.get! scrutIdx
        let branches := args.extract (scrutIdx + 1) args.size
        -- Compute the number of parameters for the branches: for this we use
        -- the type of the uninstantiated casesOn constant
        let branchesNumParams : Array Nat ← do
          let env ← getEnv
          let decl := env.constants.find! matcherName
          let ty := decl.type
          forallTelescope ty fun xs _ => do
          let xs := xs.extract (scrutIdx + 1) xs.size
          xs.mapM fun x => do
          let xty ← inferType x
          forallTelescope xty fun ys _ => do
          pure ys.size
        let me : MatchInfo := {
          matcherName,
          matcherLevels,
          params,
          motive,
          scruts := #[scrut],
          branchesNumParams,
          branches,
        }
        proveMatchIsValid k_var kk_var me
      -- Monadic let-binding
      else if f.isConstOf ``Bind.bind then do
        trace[Diverge.def.valid] "bind:\n{args}"
        let x := args.get! 4
        let y := args.get! 5
        -- Prove that the subexpressions are valid
        let xValid ← proveExprIsValid k_var kk_var x
        trace[Diverge.def.valid] "bind: xValid:\n{xValid}:\n{← inferType xValid}"
        let yValid ← do
          -- This is a lambda expression -- TODO: how do we remove exacly *one* lambda?
          lambdaLetTelescope y fun xs y => do
          let x := xs.get! 0
          let xs := xs.extract 1 xs.size
          let y ← mkLambdaFVars xs y
          trace[Diverge.def.valid] "bind: y: {y}"
          let yValid ← proveExprIsValid k_var kk_var y
          trace[Diverge.def.valid] "bind: yValid (no forall): {yValid}"
          trace[Diverge.def.valid] "bind: yValid: x: {x}"
          let yValid ← mkLambdaFVars #[x] yValid
          trace[Diverge.def.valid] "bind: yValid (forall): {yValid}: {← inferType yValid}"
          pure yValid
        -- Put everything together
        trace[Diverge.def.valid] "bind:\n- xValid: {xValid}: {← inferType xValid}\n- yValid: {yValid}: {← inferType yValid}"
        mkAppM ``FixI.is_valid_p_bind #[xValid, yValid]
      -- Recursive call
      else if f.isFVarOf kk_var.fvarId! then do
        trace[Diverge.def.valid] "rec: args: \n{args}"
        if args.size ≠ 2 then throwError "Recursive call with invalid number of parameters: {args}"
        let i_arg := args.get! 0
        let x_arg := args.get! 1
        let eIsValid ← mkAppM ``FixI.is_valid_p_rec #[k_var, i_arg, x_arg]
        trace[Diverge.def.valid] "rec: result: \n{eIsValid}"
        pure eIsValid
      else do
        -- Remaining case: normal application.
        -- It shouldn't use the continuation
        proveNoKExprIsValid k_var e

partial def proveMatchIsValid (k_var kk_var : Expr) (me : MatchInfo) : MetaM Expr := do
  trace[Diverge.def.valid] "proveMatchIsValid: {me}"
  -- Prove the validity of the branch expressions
  let branchesValid:Array Expr ← me.branches.mapIdxM fun idx br => do
    -- Go inside the lambdas - note that we have to be careful: some of the
    -- binders might come from the match, and some of the binders might come
    -- from the fact that the expression in the match is a lambda expression:
    -- we use the branchesNumParams field for this reason
    lambdaLetTelescope br fun xs br => do
    let numParams := me.branchesNumParams.get! idx
    let xs_beg := xs.extract 0 numParams
    let xs_end := xs.extract numParams xs.size
    let br ← mkLambdaFVars xs_end br
    -- Prove that the branch expression is valid
    let brValid ← proveExprIsValid k_var kk_var br
    -- Reconstruct the lambda expression
    mkLambdaFVars xs_beg brValid
  trace[Diverge.def.valid] "branchesValid:\n{branchesValid}"
  -- Put together: compute the motive.
  -- It must be of the shape:
  -- ```
  -- λ scrut => is_valid_p k (λ k => match scrut with ...)
  -- ```
  let validMotive : Expr ← do
    -- The motive is a function of the scrutinees (i.e., a lambda expression):
    -- introduce binders for the scrutinees
    let declInfos := me.scruts.mapIdx fun idx scrut =>
      let name : Name :=  (.num (.str .anonymous "scrut") idx)
      let ty := λ (_ : Array Expr) => inferType scrut
      (name, ty)
    withLocalDeclsD declInfos fun scrutVars => do
    -- Create a match expression but where the scrutinees have been replaced
    -- by variables
    let params : Array (Option Expr) := me.params.map some
    let motive : Option Expr := some me.motive
    let scruts : Array (Option Expr) := scrutVars.map some
    let branches : Array (Option Expr) := me.branches.map some
    let args := params ++ [motive] ++ scruts ++ branches
    let matchE ← mkAppOptM me.matcherName args
    -- let matchE ← mkLambdaFVars scrutVars (← mkAppOptM me.matcherName args)
    -- Wrap in the `is_valid_p` predicate
    let matchE ← mkLambdaFVars #[kk_var] matchE
    let validMotive ← mkAppM ``FixI.is_valid_p #[k_var, matchE]
    -- Abstract away the scrutinee variables
    mkLambdaFVars scrutVars validMotive
  trace[Diverge.def.valid] "valid motive: {validMotive}"
  -- Put together
  let valid ← do
    let params : Array (Option Expr) := me.params.map (λ _ => none)
    let motive := some validMotive
    let scruts := me.scruts.map some
    let branches := branchesValid.map some
    let args := params ++ [motive] ++ scruts ++ branches
    mkAppOptM me.matcherName args
  trace[Diverge.def.valid] "proveMatchIsValid:\n{valid}:\n{← inferType valid}"
  pure valid

end

-- Prove that a single body (in the mutually recursive group) is valid
partial def proveSingleBodyIsValid (k_var : Expr) (preDef : PreDefinition) (bodyConst : Expr) :
  MetaM Expr := do
  trace[Diverge.def.valid] "proveSingleBodyIsValid: bodyConst: {bodyConst}"
  -- Lookup the definition (`bodyConst` is the definition of the body, we want
  -- to retrieve the value itself to dive inside)
  let name := bodyConst.constName!
  let env ← getEnv
  let body := (env.constants.find! name).value!
  trace[Diverge.def.valid] "body: {body}"
  lambdaLetTelescope body fun xs body => do
  assert! xs.size = 2
  let kk_var := xs.get! 0
  let x_var := xs.get! 1
  -- State the type of the theorem to prove
  let thmTy ← mkAppM ``FixI.is_valid_p
    #[k_var, ← mkLambdaFVars #[kk_var] (← mkAppM' bodyConst #[kk_var, x_var])]
  trace[Diverge.def.valid] "thmTy: {thmTy}"
  -- Prove that the body is valid
  let proof ← proveExprIsValid k_var kk_var body
  let proof ← mkLambdaFVars #[k_var, x_var] proof
  trace[Diverge.def.valid] "proveSingleBodyIsValid: proof:\n{proof}:\n{← inferType proof}"
  -- The target type (we don't have to do this: this is simply a sanity check,
  -- and this allows a nicer debugging output)
  let thmTy ← do
    let body ← mkAppM' bodyConst #[kk_var, x_var]
    let body ← mkLambdaFVars #[kk_var] body
    let ty ← mkAppM ``FixI.is_valid_p #[k_var, body]
    mkForallFVars #[k_var, x_var] ty
  trace[Diverge.def.valid] "proveSingleBodyIsValid: thmTy\n{thmTy}:\n{← inferType thmTy}"
  -- Save the theorem
  let name := preDef.declName ++ "sbody_is_valid"
  let decl := Declaration.thmDecl {
    name
    levelParams := preDef.levelParams
    type := thmTy
    value := proof
    all := [name]
  }
  addDecl decl
  trace[Diverge.def.valid] "proveSingleBodyIsValid: added thm: {name}"
  -- Return the theorem
  pure (Expr.const name (preDef.levelParams.map .param))

partial def proveFunsBodyIsValid (inOutTys: Expr) (bodyFuns : Expr)
  (k_var : Expr) (bodiesValid : Array Expr) : MetaM Expr := do
  -- Create the big "and" expression, which groups the validity proof of the individual bodies
  let rec mkValidConj (i : Nat) : MetaM Expr := do
    if i = bodiesValid.size then
      -- We reached the end
      mkAppM ``FixI.Funs.is_valid_p_Nil #[k_var]
    else do
      -- We haven't reached the end: introduce a conjunction
      let valid := bodiesValid.get! i
      let valid ← mkAppM' valid #[k_var]
      mkAppM ``And.intro #[valid, ← mkValidConj (i + 1)]
  let andExpr ← mkValidConj 0
  -- Wrap in the `is_valid_p_is_valid_p` theorem, and abstract the continuation
  let isValid ← mkAppM ``FixI.Funs.is_valid_p_is_valid_p #[inOutTys, k_var, bodyFuns, andExpr]
  mkLambdaFVars #[k_var] isValid

-- Prove that the mut rec body is valid
-- TODO: maybe this function should introduce k_var itself
def proveMutRecIsValid
  (grName : Name) (grLvlParams : List Name)
  (inOutTys : Expr) (bodyFuns mutRecBodyConst : Expr)
  (k_var : Expr) (preDefs : Array PreDefinition)
  (bodies : Array Expr) : MetaM Expr := do
  -- First prove that the individual bodies are valid
  let bodiesValid ←
    bodies.mapIdxM fun idx body => do
      let preDef := preDefs.get! idx
      proveSingleBodyIsValid k_var preDef body
  -- Then prove that the mut rec body is valid
  let isValid ← proveFunsBodyIsValid inOutTys bodyFuns k_var bodiesValid
  -- Save the theorem
  let thmTy ← mkAppM ``FixI.is_valid #[mutRecBodyConst]
  let name := grName ++ "mut_rec_body_is_valid"
  let decl := Declaration.thmDecl {
    name
    levelParams := grLvlParams
    type := thmTy
    value := isValid
    all := [name]
  }
  addDecl decl
  trace[Diverge.def.valid] "proveFunsBodyIsValid: added thm: {name}:\n{thmTy}"
  -- Return the theorem
  pure (Expr.const name (grLvlParams.map .param))

-- Generate the final definions by using the mutual body and the fixed point operator.
def mkDeclareFixDefs (mutRecBody : Expr) (preDefs : Array PreDefinition) :
  TermElabM (Array Name) := do
  let grSize := preDefs.size
  let defs ← preDefs.mapIdxM fun idx preDef => do
    lambdaLetTelescope preDef.value fun xs _ => do
    -- Create the index
    let idx ← mkFinVal grSize idx.val
    -- Group the inputs into a dependent tuple
    let input ← mkSigmas xs.toList
    -- Apply the fixed point
    let fixedBody ← mkAppM ``FixI.fix #[mutRecBody, idx, input]
    let fixedBody ← mkLambdaFVars xs fixedBody
    -- Create the declaration
    let name := preDef.declName
    let decl := Declaration.defnDecl {
      name := name
      levelParams := preDef.levelParams
      type := preDef.type
      value := fixedBody
      hints := ReducibilityHints.regular (getMaxHeight (← getEnv) fixedBody + 1)
      safety := .safe
      all := [name]
    }
    addDecl decl
    pure name
  pure defs

-- Prove the equations that we will use as unfolding theorems
partial def proveUnfoldingThms (isValidThm : Expr) (preDefs : Array PreDefinition)
  (decls : Array Name) : MetaM Unit := do
  let grSize := preDefs.size
  let proveIdx (i : Nat) : MetaM Unit := do
    let preDef := preDefs.get! i
    let defName := decls.get! i
    -- Retrieve the arguments
    lambdaLetTelescope preDef.value fun xs body => do
    trace[Diverge.def.unfold] "proveUnfoldingThms: xs: {xs}"
    trace[Diverge.def.unfold] "proveUnfoldingThms: body: {body}"
    -- The theorem statement
    let thmTy ← do
      -- The equation: the declaration gives the lhs, the pre-def gives the rhs
      let lhs ← mkAppOptM defName (xs.map some)
      let rhs := body
      let eq ← mkAppM ``Eq #[lhs, rhs]
      mkForallFVars xs eq
    trace[Diverge.def.unfold] "proveUnfoldingThms: thm statement: {thmTy}"
    -- The proof
    -- Use the fixed-point equation
    let proof ← mkAppM ``FixI.is_valid_fix_fixed_eq #[isValidThm]
    -- Add the index
    let idx ← mkFinVal grSize i
    let proof ← mkAppM ``congr_fun #[proof, idx]
    -- Add the input argument
    let arg ← mkSigmas xs.toList
    let proof ← mkAppM ``congr_fun #[proof, arg]
    -- Abstract the arguments away
    let proof ← mkLambdaFVars xs proof
    trace[Diverge.def.unfold] "proveUnfoldingThms: proof: {proof}:\n{← inferType proof}"
    -- Declare the theorem
    let name := preDef.declName ++ "unfold"
    let decl := Declaration.thmDecl {
      name
      levelParams := preDef.levelParams
      type := thmTy
      value := proof
      all := [name]
    }
    addDecl decl
    trace[Diverge.def.unfold] "proveUnfoldingThms: added thm: {name}:\n{thmTy}"
  let rec prove (i : Nat) : MetaM Unit := do
    if i = preDefs.size then pure ()
    else do
      proveIdx i
      prove (i + 1)
  --
  prove 0

def divRecursion (preDefs : Array PreDefinition) : TermElabM Unit := do
  let msg := toMessageData <| preDefs.map fun pd => (pd.declName, pd.levelParams, pd.type, pd.value)
  trace[Diverge.def] ("divRecursion: defs: " ++ msg)

  -- CHANGE HERE This function should add definitions with these names/types/values ^^
  -- Temporarily add the predefinitions as axioms
  -- for preDef in preDefs do
  --  addAsAxiom preDef

  -- TODO: what is this?
  for preDef in preDefs do
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation

  -- Retrieve the name of the first definition, that we will use as the namespace
  -- for the definitions common to the group
  let def0 := preDefs[0]!
  let grName := def0.declName
  trace[Diverge.def] "group name: {grName}"

  /- # Compute the input/output types of the continuation `k`. -/
  let grLvlParams := def0.levelParams
  trace[Diverge.def] "def0 universe levels: {def0.levelParams}"

  -- We first compute the list of pairs: (input type × output type)
  let inOutTys : Array (Expr × Expr) ←
      preDefs.mapM (fun preDef => do
        withRef preDef.ref do -- is the withRef useful?
        -- Check the universe parameters - TODO: I'm not sure what the best thing
        -- to do is. In practice, all the type parameters should be in Type 0, so
        -- we shouldn't have universe issues.
        if preDef.levelParams ≠ grLvlParams then
          throwError "Non-uniform polymorphism in the universes"
        forallTelescope preDef.type (fun in_tys out_ty => do
          let in_ty ← liftM (mkSigmasTypesOfTypes in_tys.toList)
          -- Retrieve the type in the "Result"
          let out_ty ← get_result_ty out_ty
          let out_ty ← liftM (mkSigmasMatch in_tys.toList out_ty)
          pure (in_ty, out_ty)
        )
      )
  trace[Diverge.def] "inOutTys: {inOutTys}"
  -- Turn the list of input/output type pairs into an expresion
  let inOutTysExpr ← inOutTys.mapM (λ (x, y) => mkInOutTy x y)
  let inOutTysExpr ← mkList inOutTysExpr.toList (← inferType (inOutTysExpr.get! 0))

  -- From the list of pairs of input/output types, actually compute the
  -- type of the continuation `k`.
  -- We first introduce the index `i : Fin n` where `n` is the number of
  -- functions in the group.
  let i_var_ty := mkFin preDefs.size
  withLocalDeclD (.num (.str .anonymous "i") 0) i_var_ty fun i_var => do
  let in_out_ty ← mkAppM ``List.get #[inOutTysExpr, i_var]
  trace[Diverge.def] "in_out_ty := {in_out_ty} : {← inferType in_out_ty}"
  -- Add an auxiliary definition for `in_out_ty`
  let in_out_ty ← do
    let value ← mkLambdaFVars #[i_var] in_out_ty
    let name := grName.append "in_out_ty"
    let levelParams := grLvlParams
    let decl := Declaration.defnDecl {
      name := name
      levelParams := levelParams
      type := ← inferType value
      value := value
      hints := .abbrev
      safety := .safe
      all := [name]
    }
    addDecl decl
    -- Return the constant
    let in_out_ty := Lean.mkConst name (levelParams.map .param)
    mkAppM' in_out_ty #[i_var]
  trace[Diverge.def] "in_out_ty (after decl) := {in_out_ty} : {← inferType in_out_ty}"
  let in_ty ← mkAppM ``Sigma.fst #[in_out_ty]
  trace[Diverge.def] "in_ty: {in_ty}"
  withLocalDeclD (.num (.str .anonymous "x") 1) in_ty fun input => do
  let out_ty ← mkAppM' (← mkAppM ``Sigma.snd #[in_out_ty]) #[input]
  trace[Diverge.def] "out_ty: {out_ty}"

  -- Introduce the continuation `k`
  let in_ty ← mkLambdaFVars #[i_var] in_ty
  let out_ty ← mkLambdaFVars #[i_var, input] out_ty
  let kk_var_ty ← mkAppM ``FixI.kk_ty #[i_var_ty, in_ty, out_ty]
  trace[Diverge.def] "kk_var_ty: {kk_var_ty}"
  withLocalDeclD (.num (.str .anonymous "kk") 2) kk_var_ty fun kk_var => do
  trace[Diverge.def] "kk_var: {kk_var}"

  -- Replace the recursive calls in all the function bodies by calls to the
  -- continuation `k` and and generate for those bodies declarations
  let bodies ← mkDeclareUnaryBodies grLvlParams kk_var preDefs
  -- Generate the mutually recursive body
  let (bodyFuns, mutRecBody) ← mkDeclareMutRecBody grName grLvlParams kk_var i_var in_ty out_ty inOutTys.toList bodies
  trace[Diverge.def] "mut rec body (after decl): {mutRecBody}"

  -- Prove that the mut rec body satisfies the validity criteria required by
  -- our fixed-point
  let k_var_ty ← mkAppM ``FixI.k_ty #[i_var_ty, in_ty, out_ty]
  withLocalDeclD (.num (.str .anonymous "k") 3) k_var_ty fun k_var => do
  let isValidThm ← proveMutRecIsValid grName grLvlParams inOutTysExpr bodyFuns mutRecBody k_var preDefs bodies

  -- Generate the final definitions
  let decls ← mkDeclareFixDefs mutRecBody preDefs

  -- Prove the unfolding theorems
  proveUnfoldingThms isValidThm preDefs decls

  -- Process the definitions - TODO
  addAndCompilePartialRec preDefs

-- The following function is copy&pasted from Lean.Elab.PreDefinition.Main
-- This is the only part where we make actual changes and hook into the equation compiler.
-- (I've removed all the well-founded stuff to make it easier to read though.)

open private ensureNoUnassignedMVarsAtPreDef betaReduceLetRecApps partitionPreDefs
  addAndCompilePartial addAsAxioms from Lean.Elab.PreDefinition.Main

def addPreDefinitions (preDefs : Array PreDefinition) : TermElabM Unit := withLCtx {} {} do
  for preDef in preDefs do
    trace[Diverge.elab] "{preDef.declName} : {preDef.type} :=\n{preDef.value}"
  let preDefs ← preDefs.mapM ensureNoUnassignedMVarsAtPreDef
  let preDefs ← betaReduceLetRecApps preDefs
  let cliques := partitionPreDefs preDefs
  let mut hasErrors := false
  for preDefs in cliques do
    trace[Diverge.elab] "{preDefs.map (·.declName)}"
    try
      withRef (preDefs[0]!.ref) do
        divRecursion preDefs
    catch ex =>
      -- If it failed, we add the functions as partial functions
      hasErrors := true
      logException ex
      let s ← saveState
      try
        if preDefs.all fun preDef => preDef.kind == DefKind.def ||
           preDefs.all fun preDef => preDef.kind == DefKind.abbrev then
          -- try to add as partial definition
          try
            addAndCompilePartial preDefs (useSorry := true)
          catch _ =>
            -- Compilation failed try again just as axiom
            s.restore
            addAsAxioms preDefs
        else return ()
      catch _ => s.restore

-- The following two functions are copy&pasted from Lean.Elab.MutualDef

open private elabHeaders levelMVarToParamHeaders getAllUserLevelNames withFunLocalDecls elabFunValues
  instantiateMVarsAtHeader instantiateMVarsAtLetRecToLift checkLetRecsToLiftTypes withUsed from Lean.Elab.MutualDef

def Term.elabMutualDef (vars : Array Expr) (views : Array DefView) : TermElabM Unit := do
    let scopeLevelNames ← getLevelNames
    let headers ← elabHeaders views
    let headers ← levelMVarToParamHeaders views headers
    let allUserLevelNames := getAllUserLevelNames headers
    withFunLocalDecls headers fun funFVars => do
      for view in views, funFVar in funFVars do
        addLocalVarInfo view.declId funFVar
      let values ←
        try
          let values ← elabFunValues headers
          Term.synthesizeSyntheticMVarsNoPostponing
          values.mapM (instantiateMVars ·)
        catch ex =>
          logException ex
          headers.mapM fun header => mkSorry header.type (synthetic := true)
      let headers ← headers.mapM instantiateMVarsAtHeader
      let letRecsToLift ← getLetRecsToLift
      let letRecsToLift ← letRecsToLift.mapM instantiateMVarsAtLetRecToLift
      checkLetRecsToLiftTypes funFVars letRecsToLift
      withUsed vars headers values letRecsToLift fun vars => do
        let preDefs ← MutualClosure.main vars headers funFVars values letRecsToLift
        for preDef in preDefs do
          trace[Diverge.elab] "{preDef.declName} : {preDef.type} :=\n{preDef.value}"
        let preDefs ← withLevelNames allUserLevelNames <| levelMVarToParamPreDecls preDefs
        let preDefs ← instantiateMVarsAtPreDecls preDefs
        let preDefs ← fixLevelParams preDefs scopeLevelNames allUserLevelNames
        for preDef in preDefs do
          trace[Diverge.elab] "after eraseAuxDiscr, {preDef.declName} : {preDef.type} :=\n{preDef.value}"
        checkForHiddenUnivLevels allUserLevelNames preDefs
        addPreDefinitions preDefs

open Command in
def Command.elabMutualDef (ds : Array Syntax) : CommandElabM Unit := do
  let views ← ds.mapM fun d => do
    let `($mods:declModifiers divergent def $id:declId $sig:optDeclSig $val:declVal) := d
      | throwUnsupportedSyntax
    let modifiers ← elabModifiers mods
    let (binders, type) := expandOptDeclSig sig
    let deriving? := none
    pure { ref := d, kind := DefKind.def, modifiers,
           declId := id, binders, type? := type, value := val, deriving? }
  runTermElabM fun vars => Term.elabMutualDef vars views

-- Special command so that we don't fall back to the built-in mutual when we produce an error.
local syntax "_divergent" Parser.Command.mutual : command
elab_rules : command | `(_divergent mutual $decls* end) => Command.elabMutualDef decls

macro_rules
  | `(mutual $decls* end) => do
    unless !decls.isEmpty && decls.all (·.1.getKind == ``divergentDef) do
      Macro.throwUnsupported
    `(command| _divergent mutual $decls* end)

open private setDeclIdName from Lean.Elab.Declaration
elab_rules : command
  | `($mods:declModifiers divergent%$tk def $id:declId $sig:optDeclSig $val:declVal) => do
    let (name, _) := expandDeclIdCore id
    if (`_root_).isPrefixOf name then throwUnsupportedSyntax
    let view := extractMacroScopes name
    let .str ns shortName := view.name | throwUnsupportedSyntax
    let shortName' := { view with name := shortName }.review
    let cmd ← `(mutual $mods:declModifiers divergent%$tk def $(⟨setDeclIdName id shortName'⟩):declId $sig:optDeclSig $val:declVal end)
    if ns matches .anonymous then
      Command.elabCommand cmd
    else
      Command.elabCommand <| ← `(namespace $(mkIdentFrom id ns) $cmd end $(mkIdentFrom id ns))

divergent def list_nth {a: Type} (ls : List a) (i : Int) : Result a :=
  match ls with
  | [] => .fail .panic
  | x :: ls =>
    if i = 0 then return x
    else return (← list_nth ls (i - 1))

example {a: Type} (ls : List a) :
  ∀ (i : Int),
  0 ≤ i → i < ls.length →
  ∃ x, list_nth ls i = .ret x := by
  induction ls
  . intro i hpos h; simp at h; linarith
  . rename_i hd tl ih
    intro i hpos h
    rw [list_nth.unfold]; simp
    split <;> simp [*]
    . tauto
    . -- TODO: we shouldn't have to do that
      have hneq : 0 < i := by cases i <;> rename_i a _ <;> simp_all; cases a <;> simp_all
      simp at h
      have ⟨ x, ih ⟩ := ih (i - 1) (by linarith) (by linarith)
      simp [ih]
      tauto

mutual
  divergent def is_even (i : Int) : Result Bool :=
    if i = 0 then return true else return (← is_odd (i - 1))

  divergent def is_odd (i : Int) : Result Bool :=
    if i = 0 then return false else return (← is_even (i - 1))
end

#print is_even.unfold
#print is_odd.unfold

mutual
  divergent def foo (i : Int) : Result Nat :=
    if i > 10 then return (← foo (i / 10)) + (← bar i) else bar 10

  divergent def bar (i : Int) : Result Nat :=
    if i > 20 then foo (i / 20) else .ret 42
end

#print foo.unfold
#print bar.unfold

-- Testing dependent branching and let-bindings
-- TODO: why the linter warning?
divergent def is_non_zero (i : Int) : Result Bool :=
  if _h:i = 0 then return false
  else
    let b := true
    return b

#print is_non_zero.unfold

end Diverge
