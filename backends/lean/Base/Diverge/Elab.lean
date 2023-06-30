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
-- set_option trace.Diverge.def.sigmas true

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

#check Array.map
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
def mkDeclareUnaryBodies (grLvlParams : List Name) (k_var : Expr)
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
            mkAppM' k_var #[i, args]
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
    let value ← mkLambdaFVars #[k_var] body
    let name := preDef.declName.append "body"
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
    -- let body ← mkAppM' body #[k_var]
    trace[Diverge.def] "individual body (after decl): {body}"
    pure body

-- Generate a unique function body from the bodies of the mutually recursive group,
-- and add it as a declaration in the context
def mkDeclareMutualBody (grName : Name) (grLvlParams : List Name)
  (i_var k_var : Expr)
  (in_ty out_ty : Expr) (inOutTys : List (Expr × Expr))
  (bodies : Array Expr) : MetaM Expr := do
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
    | _, _ => throwError "mkDeclareMutualBody: `tys` and `bodies` don't have the same length"
  let bodyFuns ← mkFuns inOutTys bodies.toList
  -- Wrap in `get_fun`
  let body ← mkAppM ``FixI.get_fun #[bodyFuns, i_var, k_var]
  -- Add the index `i` and the continuation `k` as a variables
  let body ← mkLambdaFVars #[k_var, i_var] body
  trace[Diverge.def] "mkDeclareMutualBody: body: {body}"
  -- Add the declaration
  let name := grName.append "mutrec_body"
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
  pure (Lean.mkConst name (levelParams.map .param))

-- Generate the final definions by using the mutual body and the fixed point operator.
def mkDeclareFixDefs (mutBody : Expr) (preDefs : Array PreDefinition) :
  TermElabM Unit := do
  let grSize := preDefs.size
  let _ ← preDefs.mapIdxM fun idx preDef => do
    lambdaLetTelescope preDef.value fun xs _ => do
    -- Create the index
    let idx ← mkFinVal grSize idx.val
    -- Group the inputs into a dependent tuple
    let input ← mkSigmas xs.toList
    -- Apply the fixed point
    let fixedBody ← mkAppM ``FixI.fix #[mutBody, idx, input]
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
  pure ()

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
  let k_var_ty ← mkAppM ``FixI.kk_ty #[i_var_ty, in_ty, out_ty] --
  trace[Diverge.def] "k_var_ty: {k_var_ty}"
  withLocalDeclD (.num (.str .anonymous "k") 2) k_var_ty fun k_var => do
  trace[Diverge.def] "k_var: {k_var}"

  -- Replace the recursive calls in all the function bodies by calls to the
  -- continuation `k` and and generate for those bodies declarations
  let bodies ← mkDeclareUnaryBodies grLvlParams k_var preDefs
  -- Generate the mutually recursive body
  let body ← mkDeclareMutualBody grName grLvlParams i_var k_var in_ty out_ty inOutTys.toList bodies
  trace[Diverge.def] "mut rec body (after decl): {body}"

  -- Prove that the mut rec body satisfies the validity criteria required by
  -- our fixed-point
  -- TODO

  -- Generate the final definitions
  let defs ← mkDeclareFixDefs body preDefs

  -- Prove the unfolding equations
  -- TODO

  -- Process the definitions
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
      trace[Diverge.elab] "calling divRecursion"
      withRef (preDefs[0]!.ref) do
        divRecursion preDefs
      trace[Diverge.elab] "divRecursion succeeded"
    catch ex =>
      -- If it failed, we 
      trace[Diverge.elab] "divRecursion failed"
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

#print list_nth.in_out_ty
#check list_nth.body
#print list_nth

mutual
  divergent def is_even (i : Int) : Result Bool :=
    if i = 0 then return true else return (← is_odd (i - 1))

  divergent def is_odd (i : Int) : Result Bool :=
    if i = 0 then return false else return (← is_even (i - 1))
end

example (i : Int) : is_even i = .ret (i % 2 = 0) ∧ is_odd i = .ret (i % 2 ≠ 0) := by
  induction i
  unfold is_even
  sorry    

mutual
  divergent def foo (i : Int) : Result Nat :=
    if i > 10 then return (← foo (i / 10)) + (← bar i) else bar 10

  divergent def bar (i : Int) : Result Nat :=
    if i > 20 then foo (i / 20) else .ret 42
end

end Diverge
