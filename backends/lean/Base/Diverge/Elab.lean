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

open Lean Elab Term Meta Primitives

set_option trace.Diverge.def true

/- The following was copied from the `wfRecursion` function. -/

open WF in



-- Replace the recursive calls by a call to the continuation
-- def replace_rec_calls

#check Lean.Meta.forallTelescope
#check Expr
#check withRef
#check MonadRef.withRef
#check Nat
#check Array
#check Lean.Meta.inferType
#check Nat
#check Int

#check (0, 1)
#check Prod
#check ()
#check Unit
#check Sigma

--  print_decl is_even_body
#check instOfNatNat
#check OfNat.ofNat -- @OfNat.ofNat ℕ 2 ...
#check OfNat.ofNat -- @OfNat.ofNat (Fin 2) 1 ...
#check Fin.instOfNatFinHAddNatInstHAddInstAddNatOfNat


-- TODO: is there already such a utility somewhere?
-- TODO: change to mkSigmas
def mkProds (tys : List Expr) : MetaM Expr :=
  match tys with
  | [] => do return (Expr.const ``PUnit.unit [])
  | [ty] => do return ty
  | ty :: tys => do
    let pty ← mkProds tys
    mkAppM ``Prod.mk #[ty, pty]

def divRecursion (preDefs : Array PreDefinition) : TermElabM Unit := do
  let msg := toMessageData <| preDefs.map fun pd => (pd.declName, pd.levelParams, pd.type, pd.value)
  trace[Diverge.def] ("divRecursion: defs: " ++ msg)

  -- CHANGE HERE This function should add definitions with these names/types/values ^^
  -- Temporarily add the predefinitions as axioms
  for preDef in preDefs do
    addAsAxiom preDef

  -- TODO: what is this?
  for preDef in preDefs do
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation

  -- Retrieve the name of the first definition, that we will use as the namespace
  -- for the definitions common to the group
  let def0 := preDefs[0]!
  let grName := def0.declName
  trace[Diverge.def] "group name: {grName}"

  /- Compute the type of the continuation.

     We do the following
     - we make sure all the definitions have the same universe parameters
       (we can make this more general later)
     - we group all the type parameters together, make sure all the
       definitions have the same type parameters, and enforce
       a uniform polymorphism (we can also lift this later).
       This would require generalizing a bit our indexed fixed point to
       make the output type parametric in the input.
     - we group all the non-type parameters: we parameterize the continuation
       by those
  -/
  let grLvlParams := def0.levelParams
  trace[Diverge.def] "def0 type: {def0.type}"

  -- Small utility: compute the list of type parameters
  let getTypeParams (ty: Expr) : MetaM (List Expr × List Expr × Expr) :=
    Lean.Meta.forallTelescope ty fun tys out_ty => do
      trace[Diverge.def] "types: {tys}"
/-      let (_, params) ← StateT.run (do
        for x in tys do
          let ty ← Lean.Meta.inferType x
          match ty with
          | .sort _ => do
            let st ← StateT.get
            StateT.set (ty :: st)
          | _ => do break
        ) ([] : List Expr)
      let params := params.reverse
      trace[Diverge.def] "  type parameters {params}"
      return params -/
      let rec get_params (ls : List Expr) : MetaM (List Expr × List Expr) :=
        match ls with
        | x :: tl => do
          let ty ← Lean.Meta.inferType x
          match ty with
          | .sort _ => do
            let (ty_params, params) ← get_params tl
            return (x :: ty_params, params)
          | _ => do return ([], ls)
        | _ => do return ([], [])
      let (ty_params, params) ← get_params tys.toList
      trace[Diverge.def] "  parameters: {ty_params}; {params}"
      return (ty_params, params, out_ty)
  let (grTyParams, _, _) ← do
    getTypeParams def0.type

  -- Compute the input types and the output types
  let all_tys ← preDefs.mapM fun preDef => do
    let (tyParams, params, ret_ty) ← getTypeParams preDef.type
    -- TODO: this is not complete, there are more checks to perform
    if tyParams.length ≠ grTyParams.length then
      throwError "Non-uniform polymorphism"
    return (params, ret_ty)

  -- TODO: I think there are issues with the free variables
  let (input_tys, output_tys) := List.unzip all_tys.toList
  let input_tys : List Expr ← liftM (List.mapM mkProds input_tys)

  trace[Diverge.def] "  in/out tys: {input_tys}; {output_tys}"

  -- Compute the names set
  let names := preDefs.map PreDefinition.declName
  let names := HashSet.empty.insertMany names

  --
  for preDef in preDefs do
    trace[Diverge.def] "about to explore: {preDef.declName}"
    explore_term "" preDef.value

  -- Compute the bodies

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

divergent def list_nth {a: Type} (ls : List a) (i : Int) : Result a :=
  match ls with
  | [] => .fail .panic
  | x :: ls =>
    if i = 0 then return x
    else return (← list_nth ls (i - 1))

mutual
  divergent def foo (i : Int) : Result Nat :=
    if i > 10 then return (← foo (i / 10)) + (← bar i) else bar 10

  divergent def bar (i : Int) : Result Nat :=
    if i > 20 then foo (i / 20) else .ret 42
end

end Diverge
