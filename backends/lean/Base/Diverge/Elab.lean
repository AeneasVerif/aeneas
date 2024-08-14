import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Base.Utils
import Base.Diverge.Base
import Base.Diverge.ElabBase

namespace Diverge

/- Automating the generation of the encoding and the proofs so as to use nice
   syntactic sugar. -/

syntax (name := divergentDef)
  declModifiers "divergent" "def" declId ppIndent(optDeclSig) declVal : command

open Lean Elab Term Meta Primitives Lean.Meta
open Utils

def normalize_let_bindings := true

/- The following was copied from the `wfRecursion` function. -/

open WF in

-- Small utility - it seems that `Name.append` doesn't do what we want
def appendToName (n : Name) (s : String) : Name :=
  Name.str n s

-- TODO: use those
def UnitType := Expr.const ``PUnit [Level.succ .zero]
def UnitValue := Expr.const ``PUnit.unit [Level.succ .zero]

def mkProdType (x y : Expr) : MetaM Expr :=
  mkAppM ``Prod #[x, y]

def mkProd (x y : Expr) : MetaM Expr :=
  mkAppM ``Prod.mk #[x, y]

def mkInOutTy (x y z : Expr) : MetaM Expr := do
  mkAppM ``FixII.mk_in_out_ty #[x, y, z]

-- Return the `a` in `Result a`
def getResultTy (ty : Expr) : MetaM Expr :=
  ty.withApp fun f args => do
  if ¬ f.isConstOf ``Result ∨ args.size ≠ 1 then
    throwError "Invalid argument to getResultTy: {ty}"
  else
    pure (args.get! 0)

/- Deconstruct a sigma type.

   For instance, deconstructs `(a : Type) × List a` into
   `Type` and `λ a => List a`.
 -/
def getSigmaTypes (ty : Expr) : MetaM (Expr × Expr) := do
  ty.withApp fun f args => do
  if ¬ f.isConstOf ``Sigma ∨ args.size ≠ 2 then
    throwError "Invalid argument to getSigmaTypes: {ty}"
  else
    pure (args.get! 0, args.get! 1)

/- Make a sigma type.

   `x` should be a variable, and `ty` and type which (might) uses `x`
 -/
def mkSigmaType (x : Expr) (sty : Expr) : MetaM Expr := do
  trace[Diverge.def.sigmas] "mkSigmaType: {x} {sty}"
  let alpha ← inferType x
  let beta ← mkLambdaFVars #[x] sty
  trace[Diverge.def.sigmas] "mkSigmaType: ({alpha}) ({beta})"
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
    trace[Diverge.def.sigmas] "mkSigmasType: []"
    pure (Expr.const ``PUnit [Level.succ .zero])
  | [x] => do
    trace[Diverge.def.sigmas] "mkSigmasType: [{x}]"
    let ty ← inferType x
    pure ty
  | x :: xl => do
    trace[Diverge.def.sigmas] "mkSigmasType: [{x}::{xl}]"
    let sty ← mkSigmasType xl
    mkSigmaType x sty

/- Generate a product type from a list of *variables* (this is similar to `mkSigmas`).

   Example:
   - xl = [(ls:List a), (i:Int)]

   Generates:
   `List a × Int`
 -/
def mkProdsType (xl : List Expr) : MetaM Expr :=
  match xl with
  | [] => do
    trace[Diverge.def.prods] "mkProdsType: []"
    pure (Expr.const ``PUnit [Level.succ .zero])
  | [x] => do
    trace[Diverge.def.prods] "mkProdsType: [{x}]"
    let ty ← inferType x
    pure ty
  | x :: xl => do
    trace[Diverge.def.prods] "mkProdsType: [{x}::{xl}]"
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
  let rec splitAux (in_tys : List Expr) : MetaM (HashSet FVarId × List Expr × List Expr) :=
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
  let (_, in_tys, in_args) ← splitAux in_tys.data
  pure (Array.mk in_tys, Array.mk in_args)

/- Apply a lambda expression to some arguments, simplifying the lambdas -/
def applyLambdaToArgs (e : Expr) (xs : Array Expr) : MetaM Expr := do
  lambdaTelescopeN e xs.size fun vars body =>
  -- Create the substitution
  let s : HashMap FVarId Expr := HashMap.ofList (List.zip (vars.toList.map Expr.fvarId!) xs.toList)
  -- Substitute in the body
  pure (body.replace fun e =>
    match e with
    | Expr.fvar fvarId => match s.find? fvarId with
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
    trace[Diverge.def.sigmas] "mkSigmasVal: []"
    pure (Expr.const ``PUnit.unit [Level.succ .zero])
  | [x] => do
    trace[Diverge.def.sigmas] "mkSigmasVal: [{x}]"
    pure x
  | fst :: xl => do
    trace[Diverge.def.sigmas] "mkSigmasVal: [{fst}::{xl}]"
    -- Deconstruct the type
    let (alpha, beta) ← getSigmaTypes ty
    -- Compute the "second" field
    -- Specialize beta for fst
    let nty ← applyLambdaToArgs beta #[fst]
    -- Recursive call
    let snd ← mkSigmasVal nty xl
    -- Put everything together
    trace[Diverge.def.sigmas] "mkSigmasVal:\n{alpha}\n{beta}\n{fst}\n{snd}"
    mkAppOptM ``Sigma.mk #[some alpha, some beta, some fst, some snd]

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
    trace[Diverge.def.sigmas] "mkSigmasMatch: [{x}]"
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
    trace[Diverge.def.sigmas] "mkSigmasMatch: [{fst}::{xl}]"
    let alpha ← inferType fst
    let snd_ty ← mkSigmasType xl
    let beta ← mkLambdaFVars #[fst] snd_ty
    let snd ← mkSigmasMatch xl out (index + 1)
    let mk ← mkLambdaFVars #[fst] snd
    -- Introduce the "scrut" variable
    let scrut_ty ← mkSigmaType fst snd_ty
    withLocalDeclD (mkAnonymous "scrut" index) scrut_ty fun scrut => do
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
    -- The final expression: putting everything together
    trace[Diverge.def.sigmas] "mkSigmasMatch:\n  ({alpha})\n  ({beta})\n  ({motive})\n  ({scrut})\n  ({mk})"
    let sm ← mkAppOptM ``Sigma.casesOn #[some alpha, some beta, some motive, some scrut, some mk]
    -- Abstracting the "scrut" variable
    let sm ← mkLambdaFVars #[scrut] sm
    trace[Diverge.def.sigmas] "mkSigmasMatch: sm: {sm}"
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
    trace[Diverge.def.prods] "mkProdsMatch: [{x}]"
    mkLambdaFVars #[x] out
  | fst :: xl => do
    trace[Diverge.def.prods] "mkProdsMatch: [{fst}::{xl}]"
    let alpha ← inferType fst
    let beta ← mkProdsType xl
    let snd ← mkProdsMatch xl out (index + 1)
    let mk ← mkLambdaFVars #[fst] snd
    -- Introduce the "scrut" variable
    let scrut_ty ← mkProdType alpha beta
    withLocalDeclD (mkAnonymous "scrut" index) scrut_ty fun scrut => do
    trace[Diverge.def.prods] "mkProdsMatch: scrut: ({scrut}) : ({← inferType scrut})"
    -- TODO: make the computation of the motive more efficient
    let motive ← do
      let out_ty ← inferType out
      mkLambdaFVars #[scrut] out_ty
    -- The final expression: putting everything together
    trace[Diverge.def.prods] "mkProdsMatch:\n  ({alpha})\n  ({beta})\n  ({motive})\n  ({scrut})\n  ({mk})"
    let sm ← mkAppOptM ``Prod.casesOn #[some alpha, some beta, some motive, some scrut, some mk]
    -- Abstracting the "scrut" variable
    let sm ← mkLambdaFVars #[scrut] sm
    trace[Diverge.def.prods] "mkProdsMatch: sm: {sm}"
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

/- Small tests for list_nth: give a model of what `mkSigmasMatch` should generate -/
private def list_nth_out_ty_inner (a :Type) (scrut1: @Sigma (List a) (fun (_ls : List a) => Int)) :=
  @Sigma.casesOn (List a)
                 (fun (_ls : List a) => Int)
                 (fun (_scrut1:@Sigma (List a) (fun (_ls : List a) => Int)) => Type)
                 scrut1
                 (fun (_ls : List a) (_i : Int) => Primitives.Result a)

private def list_nth_out_ty_outer (scrut0 : @Sigma (Type) (fun (a:Type) =>
                      @Sigma (List a) (fun (_ls : List a) => Int))) :=
  @Sigma.casesOn (Type)
                 (fun (a:Type) => @Sigma (List a) (fun (_ls : List a) => Int))
                 (fun (_scrut0:@Sigma (Type) (fun (a:Type) => @Sigma (List a) (fun (_ls : List a) => Int))) => Type)
                 scrut0
                 (fun (a : Type) (scrut1: @Sigma (List a) (fun (_ls : List a) => Int)) =>
                  list_nth_out_ty_inner a scrut1)
/- -/

-- Return the expression: `Fin n`
-- TODO: use more
def mkFin (n : Nat) : Expr :=
  mkAppN (.const ``Fin []) #[.lit (.natVal n)]

-- Return the expression: `i : Fin n`
def mkFinVal (n i : Nat) : MetaM Expr := do
  let n_lit : Expr := .lit (.natVal (n - 1))
  let i_lit : Expr := .lit (.natVal i)
  mkAppOptM ``Fin.ofNat #[.some n_lit, .some i_lit]

/- Information about the type of a function in a declaration group.

   In the comments about the fields, we take as example the
   `list_nth (α : Type) (ls : List α) (i : Int) : Result α` function.
 -/
structure TypeInfo where
  /- The total number of input arguments.

     For list_nth: 3
   -/
  total_num_args : ℕ
  /- The number of type parameters (they should be a prefix of the input arguments).

     For `list_nth`: 1
   -/
  num_params : ℕ
  /- The type of the dependent tuple grouping the type parameters.

     For `list_nth`: `Type`
   -/
  params_ty : Expr
  /- The type of the tuple grouping the input values. This is a function taking
     as input a value of type `params_ty`.

     For `list_nth`: `λ a => List a × Int`
   -/
  in_ty : Expr
  /- The output type, without the `Result`. This is a function taking
     as input a value of type `params_ty`.

     For `list_nth`: `λ a => a`
   -/
  out_ty : Expr

def mkInOutTyFromTypeInfo (info : TypeInfo) : MetaM Expr := do
  mkInOutTy info.params_ty info.in_ty info.out_ty

instance : Inhabited TypeInfo :=
  { default := { total_num_args := 0, num_params := 0, params_ty := UnitType,
                 in_ty := UnitType, out_ty := UnitType } }

instance : ToMessageData TypeInfo :=
 ⟨ λ ⟨ total_num_args, num_params, params_ty, in_ty, out_ty ⟩ =>
  f!"\{ total_num_args: {total_num_args}, num_params: {num_params}, params_ty: {params_ty}, in_ty: {in_ty}, out_ty: {out_ty} }}"
 ⟩

/- Generate and declare as individual definitions the bodies for the individual funcions:
   - replace the recursive calls with calls to the continutation `k`
   - make those bodies take one single dependent tuple as input

   We name the declarations: "[original_name].body".
   We return the new declarations.
 -/
def mkDeclareUnaryBodies (grLvlParams : List Name) (kk_var : Expr)
  (paramInOutTys : Array TypeInfo) (preDefs : Array PreDefinition) :
  MetaM (Array Expr) := do
  let grSize := preDefs.size

  /- Compute the map from name to (index, type info).

     Remark: the continuation has an indexed type; we use the index (a finite number of
     type `Fin`) to control which function we call at the recursive call site. -/
  let nameToInfo : HashMap Name (Nat × TypeInfo) :=
    let bl := preDefs.mapIdx fun i d =>
      (d.declName, (i.val, paramInOutTys.get! i.val))
    HashMap.ofList bl.toList

  trace[Diverge.def.genBody] "nameToId: {nameToInfo.toList}"

  -- Auxiliary function to explore the function bodies and replace the
  -- recursive calls
  let visit_e (i : Nat) (e : Expr) : MetaM Expr := do
    trace[Diverge.def.genBody.visit] "visiting expression (dept: {i}): {e}"
    let ne ← do
      match e with
      | .app .. => do
        e.withApp fun f args => do
          trace[Diverge.def.genBody.visit] "this is an app: {f} {args}"
          -- Check if this is a recursive call
          if f.isConst then
            let name := f.constName!
            match nameToInfo.find? name with
            | none => pure e
            | some (id, type_info) =>
              trace[Diverge.def.genBody.visit] "this is a recursive call"
              -- This is a recursive call: replace it
              -- Compute the index
              let i ← mkFinVal grSize id
              -- It can happen that there are no input values given to the
              -- recursive calls, and only type parameters.
              let num_args := args.size
              if num_args ≠ type_info.total_num_args ∧ num_args ≠ type_info.num_params then
                throwError "Invalid number of arguments for the recursive call: {e}"
              -- Split the arguments, and put them in two tuples (the first
              -- one is a dependent tuple)
              let (param_args, args) := args.toList.splitAt type_info.num_params
              trace[Diverge.def.genBody.visit] "param_args: {param_args}, args: {args}"
              let param_args ← mkSigmasVal type_info.params_ty param_args
              -- Check if there are input values
              if num_args = type_info.total_num_args then do
                trace[Diverge.def.genBody.visit] "Recursive call with input values"
                let args ← mkProdsVal args
                mkAppM' kk_var #[i, param_args, args]
              else do
                trace[Diverge.def.genBody.visit] "Recursive call without input values"
                mkAppM' kk_var #[i, param_args]
          else
            -- Not a recursive call: do nothing
            pure e
       | .const name _ =>
         /- This might refer to the one of the top-level functions if we use
            it without arguments (if we give it to a higher-order
            function for instance) and there are actually no type parameters.
          -/
         if (nameToInfo.find? name).isSome then do
           -- Checking the type information
           match nameToInfo.find? name with
           | none => pure e
           | some (id, type_info) =>
             trace[Diverge.def.genBody.visit] "this is a recursive call"
             -- This is a recursive call: replace it
             -- Compute the index
             let i ← mkFinVal grSize id
             -- Check that there are no type parameters
             if type_info.num_params ≠ 0 then throwError "mkUnaryBodies: a recursive call was not eliminated"
             -- We might be in a degenerate case, if the function takes no arguments
             -- at all (i.e., the function is a constant).
             -- For instance:
             -- ```
             -- divergent def infinite_loop : Result Unit := infinite_loop
             -- ``
             if type_info.total_num_args == 0 then do
                trace[Diverge.def.genBody.visit] "Degenerate case: total_num_args=0"
                mkAppM' kk_var #[i, UnitValue, UnitValue]
             else do
               -- Introduce the call to the continuation
               let param_args ← mkSigmasVal type_info.params_ty []
               mkAppM' kk_var #[i, param_args]
         else pure e
       | _ => pure e
    trace[Diverge.def.genBody.visit] "done with expression (depth: {i}): {e}"
    pure ne

  -- Explore the bodies
  preDefs.mapM fun preDef => do
    -- Replace the recursive calls
    trace[Diverge.def.genBody] "About to replace recursive calls in {preDef.declName}"
    let body ← mapVisit visit_e preDef.value
    trace[Diverge.def.genBody] "Body after replacement of the recursive calls: {body}"

    -- Currify the function by grouping the arguments into dependent tuples
    -- (over which we match to retrieve the individual arguments).
    lambdaTelescope body fun args body => do
    -- Split the arguments between the type parameters and the "regular" inputs
    let (_, type_info) := nameToInfo.find! preDef.declName
    let (param_args, args) := args.toList.splitAt type_info.num_params
    let body ← mkProdsMatchOrUnit args body
    trace[Diverge.def.genBody] "Body after mkProdsMatchOrUnit: {body}"
    let body ← mkSigmasMatchOrUnit param_args body
    trace[Diverge.def.genBody] "Body after mkSigmasMatchOrUnit: {body}"

    -- Add the declaration
    let value ← mkLambdaFVars #[kk_var] body
    trace[Diverge.def.genBody] "Body after abstracting kk: {value}"
    let name := appendToName preDef.declName "body"
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
    trace[Diverge.def.genBody] "About to add decl"
    addDecl decl
    trace[Diverge.def] "individual body of {preDef.declName}: {body}"
    -- Return the constant
    let body := Lean.mkConst name (levelParams.map .param)
    trace[Diverge.def] "individual body (after decl): {body}"
    pure body

/- Generate a unique function body from the bodies of the mutually recursive group,
   and add it as a declaration in the context.
   We return the list of bodies (of type `FixI.Funs ...`) and the mutually recursive body.
 -/
def mkDeclareMutRecBody (grName : Name) (grLvlParams : List Name)
  (kk_var i_var : Expr)
  (param_ty in_ty out_ty : Expr) (paramInOutTys : Array TypeInfo)
  (bodies : Array Expr) : MetaM (Expr × Expr) := do
  -- Generate the body
  let grSize := bodies.size
  let finTypeExpr := mkFin grSize
  -- TODO: not very clean
  let paramInOutTyType ← do
    let info := paramInOutTys.get! 0
    inferType (← mkInOutTyFromTypeInfo info)
  let rec mkFuns (paramInOutTys : List TypeInfo) (bl : List Expr) : MetaM Expr :=
    match paramInOutTys, bl with
    | [], [] =>
      mkAppOptM ``FixII.Funs.Nil #[finTypeExpr, param_ty, in_ty, out_ty]
    | info :: paramInOutTys, b :: bl => do
      let pty := info.params_ty
      let ity := info.in_ty
      let oty := info.out_ty
      -- Retrieving ity and oty - this is not very clean
      let paramInOutTysExpr ← mkListLit paramInOutTyType
        (← paramInOutTys.mapM mkInOutTyFromTypeInfo)
      let fl ← mkFuns paramInOutTys bl
      mkAppOptM ``FixII.Funs.Cons #[finTypeExpr, param_ty, in_ty, out_ty, pty, ity, oty, paramInOutTysExpr, b, fl]
    | _, _ => throwError "mkDeclareMutRecBody: `tys` and `bodies` don't have the same length"
  let bodyFuns ← mkFuns paramInOutTys.toList bodies.toList
  -- Wrap in `get_fun`
  let body ← mkAppM ``FixII.get_fun #[bodyFuns, i_var, kk_var]
  -- Add the index `i` and the continuation `k` as a variables
  let body ← mkLambdaFVars #[kk_var, i_var] body
  trace[Diverge.def] "mkDeclareMutRecBody: body: {body}"
  -- Add the declaration
  let name := appendToName grName "mut_rec_body"
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
  -- Return the bodies and the constant
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

/- Small helper: prove that an expression which doesn't use the continuation `kk`
   is valid, and return the proof. -/
def proveNoKExprIsValid (k_var : Expr) (e : Expr) : MetaM Expr := do
  trace[Diverge.def.valid] "proveNoKExprIsValid: {e}"
  let eIsValid ← mkAppM ``FixII.is_valid_p_same #[k_var, e]
  trace[Diverge.def.valid] "proveNoKExprIsValid: result:\n{eIsValid}:\n{← inferType eIsValid}"
  pure eIsValid

mutual

/- Prove that an expression is valid, and return the proof.

   More precisely, if `e` is an expression which potentially uses the continution
   `kk`, return an expression of type:
   ```
   is_valid_p k (λ kk => e)
   ```
 -/
partial def proveExprIsValid (k_var kk_var : Expr) (e : Expr) : MetaM Expr := do
  trace[Diverge.def.valid] "proveExprIsValid: {e}"
  -- Normalize to eliminate the let-bindings
  let e ← do
    if e.isLet ∧ normalize_let_bindings then do
      let e ← normalizeLetBindings e
      trace[Diverge.def.valid] "e (after normalization): {e}"
      pure e
    else pure e
  match e with
  | .const _ _ => throwError "Unimplemented" -- Shouldn't get there?
  | .bvar _
  | .fvar _
  | .lit _
  | .mvar _
  | .sort _ => throwError "Unreachable"
  | .lam .. => throwError "Unimplemented" -- TODO
  | .forallE .. => throwError "Unreachable" -- Shouldn't get there
  | .letE .. => do
    -- Remark: this branch is not taken if we normalize the expressions (above)
    -- Telescope all the let-bindings (remark: this also telescopes the lambdas)
    lambdaLetTelescope e fun xs body => do
    -- Note that we don't visit the bound values: there shouldn't be
    -- recursive calls, lambda expressions, etc. inside
    -- Prove that the body is valid
    let isValid ← proveExprIsValid k_var kk_var body
    -- Add the let-bindings around.
    -- Rem.: the let-binding should be *inside* the `is_valid_p`, not outside,
    -- but because it reduces in the end it doesn't matter. More precisely:
    -- `P (let x := v in y)` and `let x := v in P y` reduce to the same expression.
    mkLambdaFVars xs isValid (usedLetOnly := false)
  | .mdata _ b => proveExprIsValid k_var kk_var b
  | .proj _ _ _ =>
    -- The projection shouldn't use the continuation
    proveNoKExprIsValid k_var e
  | .app .. =>
    e.withApp fun f args => do
    proveAppIsValid k_var kk_var e f args

partial def proveAppIsValid (k_var kk_var : Expr) (e : Expr) (f : Expr) (args : Array Expr): MetaM Expr := do
  trace[Diverge.def.valid] "proveAppIsValid: {e}\nDecomposed: {f} {args}"
  /- There are several cases: first, check if this is a match/if
     Check if the expression is a (dependent) if then else.
     We treat the if then else expressions differently from the other matches,
     and have dedicated theorems for them. -/
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
        -- There is a lambda
        lambdaOne br fun x br => do
        let brValid ← proveExprIsValid k_var kk_var br
        mkLambdaFVars #[x] brValid
    let br0Valid ← proveBranchValid br0
    let br1Valid ← proveBranchValid br1
    let const := if isIte then ``FixII.is_valid_p_ite else ``FixII.is_valid_p_dite
    let eIsValid ←
      mkAppOptM const #[none, none, none, none, none,
                        some k_var, some cond, some dec, none, none,
                        some br0Valid, some br1Valid]
    trace[Diverge.def.valid] "ite/dite: result:\n{eIsValid}:\n{← inferType eIsValid}"
    pure eIsValid
  /- Check if the expression is a match (this case is for when the elaborator
     introduces auxiliary definitions to hide the match behind syntactic
     sugar): -/
  else if let some me := ← matchMatcherApp? e then do
    trace[Diverge.def.valid]
      "matcherApp:
       - params: {me.params}
       - motive: {me.motive}
       - discrs: {me.discrs}
       - altNumParams: {me.altNumParams}
       - alts: {me.alts}
       - remaining: {me.remaining}"
    -- matchMatcherApp does all the work for us: we simply need to gather
    -- the information and call the auxiliary helper `proveMatchIsValid`
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
  /- Check if the expression is a raw match (this case is for when the expression
     is a direct call to the primitive `casesOn` function, without syntactic sugar).
     We have to check this case because functions like `mkSigmasMatch`, which we
     use to currify function bodies, introduce such raw matches. -/
  else if ← isCasesExpr f then do
    trace[Diverge.def.valid] "rawMatch: {e}"
    /- Deconstruct the match, and call the auxiliary helper `proveMatchIsValid`.

       The casesOn definition is always of the following shape:
       - input parameters (implicit parameters)
       - motive (implicit), -- the motive gives the return type of the match
       - scrutinee (explicit)
       - branches (explicit).
       In particular, we notice that the scrutinee is the first *explicit*
       parameter - this is how we spot it.
     -/
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
    /- Compute the number of parameters for the branches: for this we use
       the type of the uninstantiated casesOn constant (we can't just
       destruct the lambdas in the branch expressions because the result
       of a match might be a lambda expression). -/
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
  -- Check if this is a monadic let-binding
  else if f.isConstOf ``Bind.bind then do
    trace[Diverge.def.valid] "bind:\n{args}"
    -- We simply need to prove that the subexpressions are valid, and call
    -- the appropriate lemma.
    let x := args.get! 4
    let y := args.get! 5
    -- Prove that the subexpressions are valid
    let xValid ← proveExprIsValid k_var kk_var x
    trace[Diverge.def.valid] "bind: xValid:\n{xValid}:\n{← inferType xValid}"
    let yValid ← do
      -- This is a lambda expression
      lambdaOne y fun x y => do
      trace[Diverge.def.valid] "bind: y: {y}"
      let yValid ← proveExprIsValid k_var kk_var y
      trace[Diverge.def.valid] "bind: yValid (no forall): {yValid}"
      trace[Diverge.def.valid] "bind: yValid: x: {x}"
      let yValid ← mkLambdaFVars #[x] yValid
      trace[Diverge.def.valid] "bind: yValid (forall): {yValid}: {← inferType yValid}"
      pure yValid
    -- Put everything together
    trace[Diverge.def.valid] "bind:\n- xValid: {xValid}: {← inferType xValid}\n- yValid: {yValid}: {← inferType yValid}"
    mkAppM ``FixII.is_valid_p_bind #[xValid, yValid]
  -- Check if this is a recursive call, i.e., a call to the continuation `kk`
  else if f.isFVarOf kk_var.fvarId! then do
    trace[Diverge.def.valid] "rec: args: \n{args}"
    if args.size ≠ 3 then throwError "Recursive call with invalid number of parameters: {args}"
    let i_arg := args.get! 0
    let t_arg := args.get! 1
    let x_arg := args.get! 2
    let eIsValid ← mkAppM ``FixII.is_valid_p_rec #[k_var, i_arg, t_arg, x_arg]
    trace[Diverge.def.valid] "rec: result: \n{eIsValid}"
    pure eIsValid
  else do
    /- Remaining case: normal application.
       Check if the arguments use the continuation:
       - if no: this is simple
       - if yes: we have to lookup theorems in div spec database and continue -/
    trace[Diverge.def.valid] "regular app: {e}, f: {f}, args: {args}"
    let argsFVars ← args.mapM getFVarIds
    let allArgsFVars := argsFVars.foldl (fun hs fvars => hs.insertMany fvars) HashSet.empty
    trace[Diverge.def.valid] "allArgsFVars: {allArgsFVars.toList.map mkFVar}"
    if ¬ allArgsFVars.contains kk_var.fvarId! then do
      -- Simple case
      trace[Diverge.def.valid] "kk doesn't appear in the arguments"
      proveNoKExprIsValid k_var e
    else do
      -- Lookup in the database for suitable theorems
      trace[Diverge.def.valid] "kk appears in the arguments"
      let thms ← divspecAttr.find? e
      trace[Diverge.def.valid] "Looked up theorems: {thms}"
      -- Try the theorems one by one
      proveAppIsValidApplyThms k_var kk_var e f args thms.toList

partial def proveAppIsValidApplyThms (k_var kk_var : Expr) (e : Expr)
  (f : Expr) (args : Array Expr) (thms : List Name) : MetaM Expr := do
  match thms with
  | [] => throwError "Could not prove that the following expression is valid: {e}"
  | thName :: thms =>
    -- Lookup the theorem itself
    let env ← getEnv
    let thDecl := env.constants.find! thName
    -- Introduce fresh meta-variables for the universes
    let ul : List (Name × Level) ←
      thDecl.levelParams.mapM (λ x => do pure (x, ← mkFreshLevelMVar))
    let ulMap : HashMap Name Level := HashMap.ofList ul
    let thTy := thDecl.type.instantiateLevelParamsCore (λ x => ulMap.find! x)
    trace[Diverge.def.valid] "Trying with theorem {thName}: {thTy}"
    -- Introduce meta variables for the universally quantified variables
    let (mvars, _binders, thTyBody) ← forallMetaTelescope thTy
    let thTermToMatch := thTyBody
    trace[Diverge.def.valid] "thTermToMatch: {thTermToMatch}"
    -- Create the term: `is_valid_p k (λ kk => e)`
    let termToMatch ← mkLambdaFVars #[kk_var] e
    let termToMatch ← mkAppM ``FixII.is_valid_p #[k_var, termToMatch]
    trace[Diverge.def.valid] "termToMatch: {termToMatch}"
    -- Attempt to match
    trace[Diverge.def.valid] "Matching terms:\n\n{termToMatch}\n\n{thTermToMatch}"
    let ok ← isDefEq termToMatch thTermToMatch
    if ¬ ok then
      -- Failure: attempt with the other theorems
      proveAppIsValidApplyThms k_var kk_var e f args thms
    else do
      /- Success: continue with this theorem

         Instantiate the meta variables (some of them will not be instantiated:
         they are new subgoals)
       -/
      let mvars ← mvars.mapM instantiateMVars
      let th ← mkAppOptM thName (Array.map some mvars)
      trace[Diverge.def.valid] "Instantiated theorem: {th}\n{← inferType th}"
      -- Filter the instantiated meta variables
      let mvars := mvars.filter (fun v => v.isMVar)
      let mvars := mvars.map (fun v => v.mvarId!)
      trace[Diverge.def.valid] "Remaining subgoals: {mvars}"
      for mvarId in mvars do
        -- Prove the subgoal (i.e., the precondition of the theorem)
        let mvarDecl ← mvarId.getDecl
        let declType ← instantiateMVars mvarDecl.type
        -- Reduce the subgoal before diving in, if necessary
        trace[Diverge.def.valid] "Subgoal: {declType}"
        -- Dive in the type
        forallTelescope declType fun forall_vars mvar_e => do
        trace[Diverge.def.valid] "forall_vars: {forall_vars}"
        -- `mvar_e` should have the shape `is_valid_p k (λ kk => ...)`
        -- We need to retrieve the new `k` variable, and dive into the
        -- `λ kk => ...`
        mvar_e.consumeMData.withApp fun is_valid args => do
        if is_valid.constName? ≠ ``FixII.is_valid_p ∨ args.size ≠ 7 then
          throwError "Invalid precondition: {mvar_e}"
        else do
          let k_var := args.get! 5
          let e_lam := args.get! 6
          trace[Diverge.def.valid] "k_var: {k_var}\ne_lam: {e_lam}"
          -- The outer lambda should be for the kk_var
          lambdaOne e_lam.consumeMData fun kk_var e => do
          -- Continue
          trace[Diverge.def.valid] "kk_var: {kk_var}\ne: {e}"
          -- We sometimes need to reduce the term - TODO: this is really dangerous
          let e ← do
            let updt_config config :=
              { config with transparency := .reducible }
            withConfig updt_config (whnf e)
          trace[Diverge.def.valid] "e (after normalization): {e}"
          let e_valid ← proveExprIsValid k_var kk_var e
          trace[Diverge.def.valid] "e_valid (for e): {e_valid}"
          let e_valid ← mkLambdaFVars forall_vars e_valid
          trace[Diverge.def.valid] "e_valid (with foralls): {e_valid}"
          let _ ← inferType e_valid -- Sanity check
          -- Assign the meta variable
          mvarId.assign e_valid
      pure th

-- Prove that a match expression is valid.
partial def proveMatchIsValid (k_var kk_var : Expr) (me : MatchInfo) : MetaM Expr := do
  trace[Diverge.def.valid] "proveMatchIsValid: {me}"
  -- Prove the validity of the branch expressions
  let branchesValid:Array Expr ← me.branches.mapIdxM fun idx br => do
    /- Go inside the lambdas - note that we have to be careful: some of the
       binders might come from the match, and some of the binders might come
       from the fact that the expression in the match is a lambda expression:
       we use the branchesNumParams field for this reason. -/
    let numParams := me.branchesNumParams.get! idx
    lambdaTelescopeN br numParams fun xs br => do
    -- Prove that the branch expression is valid
    let brValid ← proveExprIsValid k_var kk_var br
    -- Reconstruct the lambda expression
    mkLambdaFVars xs brValid
  trace[Diverge.def.valid] "branchesValid:\n{branchesValid}"
  /- Compute the motive, which has the following shape:
     ```
     λ scrut => is_valid_p k (λ k => match scrut with ...)
                                     ^^^^^^^^^^^^^^^^^^^^
                             this is the original match expression, with the
                            the difference that the scrutinee(s) is a variable
     ```
   -/
  let validMotive : Expr ← do
    -- The motive is a function of the scrutinees (i.e., a lambda expression):
    -- introduce binders for the scrutinees
    let declInfos := me.scruts.mapIdx fun idx scrut =>
      let name : Name := mkAnonymous "scrut" idx
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
    -- Wrap in the `is_valid_p` predicate
    let matchE ← mkLambdaFVars #[kk_var] matchE
    let validMotive ← mkAppM ``FixII.is_valid_p #[k_var, matchE]
    -- Abstract away the scrutinee variables
    mkLambdaFVars scrutVars validMotive
  trace[Diverge.def.valid] "valid motive: {validMotive}"
  -- Put together
  let valid ← do
    -- We let Lean infer the parameters
    let params : Array (Option Expr) := me.params.map (λ _ => none)
    let motive := some validMotive
    let scruts := me.scruts.map some
    let branches := branchesValid.map some
    let args := params ++ [motive] ++ scruts ++ branches
    mkAppOptM me.matcherName args
  trace[Diverge.def.valid] "proveMatchIsValid:\n{valid}:\n{← inferType valid}"
  pure valid

end

/- Prove that a single body (in the mutually recursive group) is valid.

   For instance, if we define the mutually recursive group [`is_even`, `is_odd`],
   we prove that `is_even.body` and `is_odd.body` are valid. -/
partial def proveSingleBodyIsValid
  (k_var : Expr) (preDef : PreDefinition) (bodyConst : Expr) :
  MetaM Expr := do
  trace[Diverge.def.valid] "proveSingleBodyIsValid: bodyConst: {bodyConst}"
  -- Lookup the definition (`bodyConst` is a const, we want to retrieve its
  -- definition to dive inside)
  let name := bodyConst.constName!
  let env ← getEnv
  let body := (env.constants.find! name).value!
  trace[Diverge.def.valid] "body: {body}"
  lambdaTelescope body fun xs body => do
  trace[Diverge.def.valid] "xs: {xs}"
  if xs.size ≠ 3 then throwError "Invalid number of lambdas: {xs} (expected 3)"
  let kk_var := xs.get! 0
  let t_var := xs.get! 1
  let x_var := xs.get! 2
  -- State the type of the theorem to prove
  trace[Diverge.def.valid] "bodyConst: {bodyConst} : {← inferType bodyConst}"
  let bodyApp ← mkAppOptM' bodyConst #[.some kk_var, .some t_var, .some x_var]
  trace[Diverge.def.valid] "bodyApp: {bodyApp}"
  let bodyApp ← mkLambdaFVars #[kk_var] bodyApp
  trace[Diverge.def.valid] "bodyApp: {bodyApp}"
  let thmTy ← mkAppM ``FixII.is_valid_p #[k_var, bodyApp]
  trace[Diverge.def.valid] "thmTy: {thmTy}"
  -- Prove that the body is valid
  trace[Diverge.def.valid] "body: {body}"
  let proof ← proveExprIsValid k_var kk_var body
  let proof ← mkLambdaFVars #[k_var, t_var, x_var] proof
  trace[Diverge.def.valid] "proveSingleBodyIsValid: proof:\n{proof}:\n{← inferType proof}"
  -- The target type (we don't have to do this: this is simply a sanity check,
  -- and this allows a nicer debugging output)
  let thmTy ← do
    let ty ← mkAppM ``FixII.is_valid_p #[k_var, bodyApp]
    mkForallFVars #[k_var, t_var, x_var] ty
  trace[Diverge.def.valid] "proveSingleBodyIsValid: thmTy\n{thmTy}:\n{← inferType thmTy}"
  -- Save the theorem
  let name := appendToName preDef.declName "body_is_valid"
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

/- Prove that the list of bodies are valid.

  For instance, if we define the mutually recursive group [`is_even`, `is_odd`],
  we prove that `Funs.Cons is_even.body (Funs.Cons is_odd.body Funs.Nil)` is
  valid. -/
partial def proveFunsBodyIsValid (paramInOutTys: Expr) (bodyFuns : Expr)
  (k_var : Expr) (bodiesValid : Array Expr) : MetaM Expr := do
  -- Create the big "and" expression, which groups the validity proof of the individual bodies
  let rec mkValidConj (i : Nat) : MetaM Expr := do
    if i = bodiesValid.size then
      -- We reached the end
      mkAppM ``FixII.Funs.is_valid_p_Nil #[k_var]
    else do
      -- We haven't reached the end: introduce a conjunction
      let valid := bodiesValid.get! i
      let valid ← mkAppM' valid #[k_var]
      mkAppM ``And.intro #[valid, ← mkValidConj (i + 1)]
  let andExpr ← mkValidConj 0
  -- Wrap in the `is_valid_p_is_valid_p` theorem, and abstract the continuation
  let isValid ← mkAppM ``FixII.Funs.is_valid_p_is_valid_p #[paramInOutTys, k_var, bodyFuns, andExpr]
  mkLambdaFVars #[k_var] isValid

/- Prove that the mut rec body (i.e., the unary body which groups the bodies
   of all the functions in the mutually recursive group and on which we will
   apply the fixed-point operator) is valid.

   We save the proof in the theorem "[GROUP_NAME]."mut_rec_body_is_valid",
   which we return.

   TODO: maybe this function should introduce k_var itself -/
def proveMutRecIsValid
  (grName : Name) (grLvlParams : List Name)
  (paramInOutTys : Expr) (bodyFuns mutRecBodyConst : Expr)
  (k_var : Expr) (preDefs : Array PreDefinition)
  (bodies : Array Expr) : MetaM Expr := do
  -- First prove that the individual bodies are valid
  let bodiesValid ←
    bodies.mapIdxM fun idx body => do
      let preDef := preDefs.get! idx
      trace[Diverge.def.valid] "## Proving that the body {body} is valid"
      proveSingleBodyIsValid k_var preDef body
  -- Then prove that the mut rec body is valid
  trace[Diverge.def.valid] "## Proving that the 'Funs' body is valid"
  let isValid ← proveFunsBodyIsValid paramInOutTys bodyFuns k_var bodiesValid
  trace[Diverge.def.valid] "Generated the term: {isValid}"
  -- Save the theorem
  let thmTy ← mkAppM ``FixII.is_valid #[mutRecBodyConst]
  let name := appendToName grName "mut_rec_body_is_valid"
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

/- Generate the final definions by using the mutual body and the fixed point operator.

   For instance:
   ```
   def is_even (i : Int) : Result Bool := mut_rec_body 0 i
   def is_odd (i : Int) : Result Bool := mut_rec_body 1 i
   ```
 -/
def mkDeclareFixDefs (mutRecBody : Expr) (paramInOutTys : Array TypeInfo) (preDefs : Array PreDefinition) :
  TermElabM (Array Name) := do
  let grSize := preDefs.size
  let defs ← preDefs.mapIdxM fun idx preDef => do
    lambdaTelescope preDef.value fun xs _ => do
    -- Retrieve the parameters info
    let type_info := paramInOutTys.get! idx.val
    -- Create the index
    let idx ← mkFinVal grSize idx.val
    -- Group the inputs into two tuples
    let (params_args, input_args) := xs.toList.splitAt type_info.num_params
    let params ← mkSigmasVal type_info.params_ty params_args
    let input ← mkProdsVal input_args
    -- Apply the fixed point
    let fixedBody ← mkAppM ``FixII.fix #[mutRecBody, idx, params, input]
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
partial def proveUnfoldingThms (isValidThm : Expr)
  (paramInOutTys : Array TypeInfo)
  (preDefs : Array PreDefinition) (decls : Array Name) : MetaM Unit := do
  let grSize := preDefs.size
  let proveIdx (i : Nat) : MetaM Unit := do
    let preDef := preDefs.get! i
    let defName := decls.get! i
    -- Retrieve the arguments
    lambdaTelescope preDef.value fun xs body => do
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
    let proof ← mkAppM ``FixII.is_valid_fix_fixed_eq #[isValidThm]
    -- Add the index
    let idx ← mkFinVal grSize i
    let proof ← mkAppM ``congr_fun #[proof, idx]
    -- Add the input arguments
    let type_info := paramInOutTys.get! i
    let (params, args) := xs.toList.splitAt type_info.num_params
    let params ← mkSigmasVal type_info.params_ty params
    let args ← mkProdsVal args
    let proof ← mkAppM ``congr_fun #[proof, params]
    let proof ← mkAppM ``congr_fun #[proof, args]
    -- Abstract all the arguments away
    let proof ← mkLambdaFVars xs proof
    trace[Diverge.def.unfold] "proveUnfoldingThms: proof: {proof}:\n{← inferType proof}"
    -- Declare the theorem
    let name := appendToName preDef.declName "unfold"
    let decl := Declaration.thmDecl {
      name
      levelParams := preDef.levelParams
      type := thmTy
      value := proof
      all := [name]
    }
    addDecl decl
    -- Add the unfolding theorem to the equation compiler
    eqnsAttribute.add preDef.declName #[name]
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
  trace[Diverge.def] ("divRecursion: defs:\n" ++ msg)

  -- Apply all the "attribute" functions (for instance, the function which
  -- registers the theorem in the simp database if there is the `simp` attribute,
  -- etc.)
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

  /- We first compute the tuples: (type parameters × input type × output type)
     - type parameters: this is a sigma type
     - input type: λ params_type => product type
     - output type: λ params_type => output type
     For instance, on the function:
     `list_nth (α : Type) (ls : List α) (i : Int) : Result α`:
     we generate:
     `(Type, λ α => List α × i, λ α => Result α)`
   -/
  let paramInOutTys : Array TypeInfo ←
    preDefs.mapM (fun preDef => do
      -- Check the universe parameters - TODO: I'm not sure what the best thing
      -- to do is. In practice, all the type parameters should be in Type 0, so
      -- we shouldn't have universe issues.
      if preDef.levelParams ≠ grLvlParams then
        throwError "Non-uniform polymorphism in the universes"
      forallTelescope preDef.type (fun in_tys out_ty => do
        let total_num_args := in_tys.size
        let (params, in_tys) ← splitInputArgs in_tys out_ty
        trace[Diverge.def] "Decomposed arguments: {preDef.declName}: {params}, {in_tys}, {out_ty}"
        let num_params := params.size
        let params_ty ← mkSigmasType params.data
        let in_ty ← mkSigmasMatchOrUnit params.data (← mkProdsType in_tys.data)
        -- Retrieve the type in the "Result"
        let out_ty ← getResultTy out_ty
        let out_ty ← mkSigmasMatchOrUnit params.data out_ty
        trace[Diverge.def] "inOutTy: {preDef.declName}: {params_ty}, {in_tys}, {out_ty}"
        pure ⟨ total_num_args, num_params, params_ty, in_ty, out_ty ⟩))
  trace[Diverge.def] "paramInOutTys: {paramInOutTys}"
  -- Turn the list of input types/input args/output type tuples into expressions
  let paramInOutTysExpr ← liftM (paramInOutTys.mapM mkInOutTyFromTypeInfo)
  let paramInOutTysExpr ← mkListLit (← inferType (paramInOutTysExpr.get! 0)) paramInOutTysExpr.toList
  trace[Diverge.def] "paramInOutTys: {paramInOutTys}"

  /- From the list of pairs of input/output types, actually compute the
     type of the continuation `k`.
     We first introduce the index `i : Fin n` where `n` is the number of
     functions in the group.
   -/
  let i_var_ty := mkFin preDefs.size
  withLocalDeclD (mkAnonymous "i" 0) i_var_ty fun i_var => do
  let param_in_out_ty ← mkAppM ``List.get #[paramInOutTysExpr, i_var]
  trace[Diverge.def] "param_in_out_ty := {param_in_out_ty} : {← inferType param_in_out_ty}"
  -- Add an auxiliary definition for `param_in_out_ty` (this is a potentially big term)
  let param_in_out_ty ← do
    let value ← mkLambdaFVars #[i_var] param_in_out_ty
    let name := appendToName grName "param_in_out_ty"
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
    let param_in_out_ty := Lean.mkConst name (levelParams.map .param)
    mkAppM' param_in_out_ty #[i_var]
  trace[Diverge.def] "param_in_out_ty (after decl) := {param_in_out_ty} : {← inferType param_in_out_ty}"
  -- Decompose between: param_ty, in_ty, out_ty
  let param_ty ← mkAppM ``Sigma.fst #[param_in_out_ty]
  let in_out_ty ← mkAppM ``Sigma.snd #[param_in_out_ty]
  let in_ty ← mkAppM ``Prod.fst #[in_out_ty]
  let out_ty ← mkAppM ``Prod.snd #[in_out_ty]
  trace[Diverge.def] "param_ty: {param_ty}"
  trace[Diverge.def] "in_ty: {in_ty}"
  trace[Diverge.def] "out_ty: {out_ty}"
  withLocalDeclD (mkAnonymous "t" 1) param_ty fun param => do
  let in_ty ← mkAppM' in_ty #[param]
  let out_ty ← mkAppM' out_ty #[param]
  trace[Diverge.def] "in_ty: {in_ty}"
  trace[Diverge.def] "out_ty: {out_ty}"

  -- Introduce the continuation `k`
  let param_ty ← mkLambdaFVars #[i_var] param_ty
  let in_ty ← mkLambdaFVars #[i_var, param] in_ty
  let out_ty ← mkLambdaFVars #[i_var, param] out_ty
  let kk_var_ty ← mkAppM ``FixII.kk_ty #[i_var_ty, param_ty, in_ty, out_ty]
  trace[Diverge.def] "kk_var_ty: {kk_var_ty}"
  withLocalDeclD (mkAnonymous "kk" 2) kk_var_ty fun kk_var => do
  trace[Diverge.def] "kk_var: {kk_var}"

  -- Replace the recursive calls in all the function bodies by calls to the
  -- continuation `k` and and generate for those bodies declarations
  trace[Diverge.def] "# Generating the unary bodies"
  let bodies ← mkDeclareUnaryBodies grLvlParams kk_var paramInOutTys preDefs
  trace[Diverge.def] "Unary bodies (after decl): {bodies}"

  -- Generate the mutually recursive body
  trace[Diverge.def] "# Generating  the mut rec body"
  let (bodyFuns, mutRecBody) ← mkDeclareMutRecBody grName grLvlParams kk_var i_var param_ty in_ty out_ty paramInOutTys bodies
  trace[Diverge.def] "mut rec body (after decl): {mutRecBody}"

  -- Prove that the mut rec body satisfies the validity criteria required by
  -- our fixed-point
  let k_var_ty ← mkAppM ``FixII.k_ty #[i_var_ty, param_ty, in_ty, out_ty]
  withLocalDeclD (mkAnonymous "k" 3) k_var_ty fun k_var => do
  trace[Diverge.def] "# Proving that the mut rec body is valid"
  let isValidThm ← proveMutRecIsValid grName grLvlParams paramInOutTysExpr bodyFuns mutRecBody k_var preDefs bodies

  -- Generate the final definitions
  trace[Diverge.def] "# Generating the final definitions"
  let decls ← mkDeclareFixDefs mutRecBody paramInOutTys preDefs

  -- Prove the unfolding theorems
  trace[Diverge.def] "# Proving the unfolding theorems"
  proveUnfoldingThms isValidThm paramInOutTys preDefs decls

  -- Generating code
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

-- The following two functions are copy-pasted from Lean.Elab.MutualDef

open private elabHeaders levelMVarToParamHeaders getAllUserLevelNames withFunLocalDecls elabFunValues
  instantiateMVarsAtHeader instantiateMVarsAtLetRecToLift checkLetRecsToLiftTypes withUsed from Lean.Elab.MutualDef

-- Comes from Term.isExample
def isExample (views : Array DefView) : Bool :=
  views.any (·.kind.isExample)

open Language in
def Term.elabMutualDef (vars : Array Expr) (views : Array DefView) : TermElabM Unit :=
  if isExample views then
    withoutModifyingEnv do
      -- save correct environment in info tree
      withSaveInfoContext do
        go
  else
    go
where
  go :=
    withAlwaysResolvedPromises views.size fun bodyPromises =>
    withAlwaysResolvedPromises views.size fun tacPromises => do
      let scopeLevelNames ← getLevelNames
      let headers ← elabHeaders views bodyPromises tacPromises
      let headers ← levelMVarToParamHeaders views headers
      let allUserLevelNames := getAllUserLevelNames headers
      withFunLocalDecls headers fun funFVars => do
        for view in views, funFVar in funFVars do
          addLocalVarInfo view.declId funFVar
          -- Modification 1:
          -- Add fake use site to prevent "unused variable" warning (if the
          -- function is actually not recursive, Lean would print this warning).
          -- Remark: we could detect this case and encode the function without
          -- using the fixed-point. In practice it shouldn't happen however:
          -- we define non-recursive functions with the `divergent` keyword
          -- only for testing purposes.
          addTermInfo' view.declId funFVar
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
            trace[Elab.definition] "{preDef.declName} : {preDef.type} :=\n{preDef.value}"
          let preDefs ← withLevelNames allUserLevelNames <| levelMVarToParamPreDecls preDefs
          let preDefs ← instantiateMVarsAtPreDecls preDefs
          let preDefs ← fixLevelParams preDefs scopeLevelNames allUserLevelNames
          for preDef in preDefs do
            trace[Elab.definition] "after eraseAuxDiscr, {preDef.declName} : {preDef.type} :=\n{preDef.value}"
          checkForHiddenUnivLevels allUserLevelNames preDefs
          addPreDefinitions preDefs -- Modification 2: we use our custom function here
          processDeriving headers

  processDeriving (headers : Array DefViewElabHeader) := do
    for header in headers, view in views do
      if let some classNamesStx := view.deriving? then
        for classNameStx in classNamesStx do
          let className ← realizeGlobalConstNoOverload classNameStx
          withRef classNameStx do
            unless (← processDefDeriving className header.declName) do
              throwError "failed to synthesize instance '{className}' for '{header.declName}'"

open Command in
def Command.elabMutualDef (ds : Array Syntax) : CommandElabM Unit := do
  let views ← ds.mapM fun d => do
    let `($mods:declModifiers divergent def $id:declId $sig:optDeclSig $val:declVal) := d
      | throwUnsupportedSyntax
    let modifiers ← elabModifiers mods
    let (binders, type) := expandOptDeclSig sig
    let deriving? := none
    let headerRef := Syntax.missing -- Not sure what to put here
    pure { ref := d, kind := DefKind.def, headerRef, modifiers,
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
    let shortName' := { view with name := Name.mkSimple shortName }.review
    let cmd ← `(mutual $mods:declModifiers divergent%$tk def $(⟨setDeclIdName id shortName'⟩):declId $sig:optDeclSig $val:declVal end)
    if ns matches .anonymous then
      Command.elabCommand cmd
    else
      Command.elabCommand <| ← `(namespace $(mkIdentFrom id ns) $cmd end $(mkIdentFrom id ns))

namespace Tests

  /- Some examples of partial functions -/

  --set_option trace.Diverge.def true
  --set_option trace.Diverge.def.genBody true
  --set_option trace.Diverge.def.valid true
  --set_option trace.Diverge.def.genBody.visit true
  --set_option trace.Diverge.def.unfold true

  divergent def list_nth {a: Type u} (ls : List a) (i : Int) : Result a :=
    match ls with
    | [] => .fail .panic
    | x :: ls => do
      if i = 0 then pure x
      else pure (← list_nth ls (i - 1))

  --set_option trace.Diverge false

  #check list_nth.unfold

  example {a: Type} (ls : List a) :
    ∀ (i : Int),
    0 ≤ i → i < ls.length →
    ∃ x, list_nth ls i = .ok x := by
    induction ls
    . intro i hpos h; simp at h; omega
    . rename_i hd tl ih
      intro i hpos h
      -- We can directly use `rw [list_nth]`
      rw [list_nth]; simp
      split <;> try simp [*]
      . tauto
      . -- We don't have to do this if we use scalar_tac
        have hneq : 0 < i := by cases i <;> rename_i a _ <;> simp_all; cases a <;> simp_all
        simp at h
        have ⟨ x, ih ⟩ := ih (i - 1) (by omega) (by omega)
        simp [ih]
        tauto

  -- Return a continuation
  divergent def list_nth_with_back {a: Type} (ls : List a) (i : Int) :
    Result (a × (a → Result (List a))) :=
    match ls with
    | [] => .fail .panic
    | x :: ls =>
      if i = 0 then return (x, (λ ret => return (ret :: ls)))
      else do
        let (x, back) ← list_nth_with_back ls (i - 1)
        return (x,
          (λ ret => do
           let ls ← back ret
           return (x :: ls)))

  #check list_nth_with_back.unfold

  mutual
    divergent def is_even (i : Int) : Result Bool :=
      if i = 0 then return true else return (← is_odd (i - 1))

    divergent def is_odd (i : Int) : Result Bool :=
      if i = 0 then return false else return (← is_even (i - 1))
  end

  #check is_even.unfold
  #check is_odd.unfold

  mutual
    divergent def foo (i : Int) : Result Nat :=
      if i > 10 then return (← foo (i / 10)) + (← bar i) else bar 10

    divergent def bar (i : Int) : Result Nat :=
      if i > 20 then foo (i / 20) else .ok 42
  end

  #check foo.unfold
  #check bar.unfold

  -- Testing dependent branching and let-bindings
  divergent def isNonZero (i : Int) : Result Bool :=
    if _h:i = 0 then return false
    else
      let b := true
      return b

  #check isNonZero.unfold

  -- Testing let-bindings
  divergent def iInBounds {a : Type} (ls : List a) (i : Int) : Result Bool :=
    let i0 := ls.length
    if i < i0
    then Result.ok True
    else Result.ok False

  #check iInBounds.unfold

  divergent def isCons
    {a : Type} (ls : List a) : Result Bool :=
    let ls1 := ls
    match ls1 with
    | [] => Result.ok False
    | _ :: _ => Result.ok True

  #check isCons.unfold

  -- Testing what happens when we use concrete arguments in dependent tuples
  divergent def test1
    (_ : Option Bool) (_ : Unit) :
    Result Unit
    :=
    test1 Option.none ()

  #check test1.unfold

  -- Testing a degenerate case
  divergent def infinite_loop : Result Unit :=
    do
    let _ ← infinite_loop
    Result.ok ()

  #check infinite_loop.unfold

  -- Testing a degenerate case
  divergent def infinite_loop1 : Result Unit :=
    infinite_loop1

  #check infinite_loop1.unfold

  /- Tests with higher-order functions -/
  section HigherOrder
    open Ex8

    inductive Tree (a : Type u) :=
    | leaf (x : a)
    | node (tl : List (Tree a))

    divergent def id {a : Type u} (t : Tree a) : Result (Tree a) :=
      match t with
      | .leaf x => .ok (.leaf x)
      | .node tl =>
        do
          let tl ← map id tl
          .ok (.node tl)

    #check id.unfold

    divergent def id1 {a : Type u} (t : Tree a) : Result (Tree a) :=
      match t with
      | .leaf x => .ok (.leaf x)
      | .node tl =>
        do
          let tl ← map (fun x => id1 x) tl
          .ok (.node tl)

    #check id1.unfold

    divergent def id2 {a : Type u} (t : Tree a) : Result (Tree a) :=
      match t with
      | .leaf x => .ok (.leaf x)
      | .node tl =>
        do
          let tl ← map (fun x => do let _ ← id2 x; id2 x) tl
          .ok (.node tl)

    #check id2.unfold

    divergent def incr (t : Tree Nat) : Result (Tree Nat) :=
      match t with
      | .leaf x => .ok (.leaf (x + 1))
      | .node tl =>
        do
          let tl ← map incr tl
          .ok (.node tl)

    -- We handle this by inlining the let-binding
    divergent def id3 (t : Tree Nat) : Result (Tree Nat) :=
      match t with
      | .leaf x => .ok (.leaf (x + 1))
      | .node tl =>
        do
          let f := id3
          let tl ← map f tl
          .ok (.node tl)

    #check id3.unfold

    /-
    -- This is not handled yet: we can only do it if we introduce "general"
    -- relations for the input types and output types (result_rel should
    -- be parameterized by something).
    divergent def id4 (t : Tree Nat) : Result (Tree Nat) :=
      match t with
      | .leaf x => .ok (.leaf (x + 1))
      | .node tl =>
        do
          let f ← .ok id4
          let tl ← map f tl
          .ok (.node tl)

    #check id4.unfold
    -/

  end HigherOrder

end Tests

end Diverge
