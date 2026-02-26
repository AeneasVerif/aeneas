/-
Prototype for `impl_def` and `@[trait_default]`.

`impl_def` allows defining structure instances that reference themselves,
as long as the recursion can be eliminated by unfolding `@[trait_default]`-marked
definitions and substituting resolved field projections.
-/
import Lean

namespace Aeneas.TraitDefault

open Lean Elab Term Meta Command
open Lean.Parser.Term Lean.Parser.Command

/-! ## Attribute -/

initialize traitDefaultAttr : TagAttribute ←
  registerTagAttribute `trait_default
    "Marks a function as a trait default value that can be unfolded by `impl_def`"

/-! ## Trace class -/

initialize registerTraceClass `Aeneas.implDef

/-! ## Helpers -/

/-- Check if an expression contains a specific free variable. -/
def exprContainsFVar (e : Expr) (fvarId : FVarId) : Bool :=
  Option.isSome <| e.find? fun
    | .fvar id => id == fvarId
    | _ => false

/-- Unfold all `@[trait_default]`-marked constants in an expression and beta-reduce. -/
partial def unfoldTraitDefaults (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Core.transform e (pre := fun e => do
    let fn := e.getAppFn
    if let .const name _ := fn then
      if traitDefaultAttr.hasTag env name then
        /- We use `TransparencyMode.all` to allow unfolding even the irreducible definitions
           (we mark some default impls as irreducible when generating the code) -/
        if let some e' ← withTransparency .all <| unfoldDefinition? e then
          return .visit e'.headBeta
    return .continue)

/-- Substitute projections of a self-reference fvar with resolved field values. -/
def substituteProjections (e : Expr) (selfFvarId : FVarId) (structName : Name)
    (resolvedFields : Std.HashMap Nat Expr) : MetaM Expr := do
  let env ← getEnv
  let some structInfo := getStructureInfo? env structName
    | return e
  let mut projMap : Std.HashMap Name Nat := {}
  for i in [:structInfo.fieldNames.size] do
    if let some projFn := structInfo.getProjFn? i then
      projMap := projMap.insert projFn i
  trace[Aeneas.implDef] "substituteProjections: projMap = {projMap.toArray.map (·.1)}"
  Core.transform e (pre := fun e => do
    match e with
    | .proj sname idx arg =>
      if sname == structName then
        let argFn := arg.consumeMData.getAppFn
        if argFn.isFVar && argFn.fvarId! == selfFvarId then
          if let some val := resolvedFields[idx]? then
            return .done val
      return .continue
    | _ =>
      -- Handle application-style projections: ProjFn (selfFvar args...)
      let fn := e.getAppFn
      let args := e.getAppArgs
      if let .const projName _ := fn then
        if args.size > 0 then
          if let some fieldIdx := projMap[projName]? then
            -- Strip mdata wrappers before checking for fvar
            let lastArg := args.back!.consumeMData
            let lastArgFn := lastArg.getAppFn
            if lastArgFn.isFVar && lastArgFn.fvarId! == selfFvarId then
              if let some val := resolvedFields[fieldIdx]? then
                return .done val
      return .continue)

/-- Resolve all fields of a structure constructor application. -/
def resolveStructFields (value : Expr) (selfFvarId : FVarId) (type : Expr) : MetaM Expr := do
  let env ← getEnv
  let typeFn := type.getAppFn
  let .const structName _ := typeFn
    | throwError "impl_def: expected type to be a structure application, got {type}"
  let some structInfo := getStructureInfo? env structName
    | throwError "impl_def: {structName} is not a structure"

  let numFields := structInfo.fieldNames.size
  let ctorFn := value.getAppFn
  let allArgs := value.getAppArgs
  let numParams := allArgs.size - numFields

  trace[Aeneas.implDef] "Structure {structName}: {numFields} fields, {numParams} params"

  let paramArgs := allArgs[:numParams].toArray
  let mut fieldValues := allArgs[numParams:].toArray
  let mut resolved : Std.HashMap Nat Expr := {}
  let mut unresolved : Array Nat := #[]

  for i in [:numFields] do
    let fieldVal := fieldValues[i]!
    if !exprContainsFVar fieldVal selfFvarId then
      resolved := resolved.insert i fieldVal
    else
      unresolved := unresolved.push i

  let mut iterCount := 0
  let maxIters := numFields + 1
  let mut progress := true
  while progress && iterCount < maxIters do
    iterCount := iterCount + 1
    progress := false
    let mut stillUnresolved : Array Nat := #[]
    for i in unresolved do
      let fieldVal := fieldValues[i]!
      -- 1. Unfold trait_default definitions
      let fieldVal' ← unfoldTraitDefaults fieldVal
      -- 2. Substitute projections with resolved values
      let fieldVal' ← substituteProjections fieldVal' selfFvarId structName resolved
      if !exprContainsFVar fieldVal' selfFvarId then
        resolved := resolved.insert i fieldVal'
        fieldValues := fieldValues.set! i fieldVal'
        progress := true
        trace[Aeneas.implDef] "  {structInfo.fieldNames[i]!} now resolved!"
      else
        stillUnresolved := stillUnresolved.push i
        fieldValues := fieldValues.set! i fieldVal'
        trace[Aeneas.implDef] "  {structInfo.fieldNames[i]!} still unresolved"
    unresolved := stillUnresolved

  if !unresolved.isEmpty then
    let unresolvedNames := unresolved.map fun i => structInfo.fieldNames[i]!
    throwError "impl_def: could not resolve recursive fields: {unresolvedNames}"

  return mkAppN ctorFn (paramArgs ++ fieldValues)

/-! ## Command elaborator -/

elab mods:declModifiers "impl_def " id:declId sig:optDeclSig val:declVal : command => do
  let modifiers ← elabModifiers mods
  let (binders, type?) := expandOptDeclSig sig
  let typeStx ← match type? with
    | some t => pure t
    | none => throwErrorAt sig "impl_def requires an explicit type annotation"

  -- Extract value term
  let valStx ←
    if val.raw.isOfKind ``Lean.Parser.Command.declValSimple then
      pure val.raw[1]
    else
      throwErrorAt val.raw "impl_def only supports `:= body` syntax"

  runTermElabM fun _sectionVars => do
    let ⟨shortDeclName, declName, levelNames, _⟩ ←
      Term.expandDeclId (← getCurrNamespace) (← getLevelNames) id modifiers

    withDeclName declName do
    withLevelNames levelNames do
    withAutoBoundImplicit do

    elabBinders binders.getArgs fun xs => do
      let type ← elabType typeStx
      Term.synthesizeSyntheticMVarsNoPostponing

      let fullType ← mkForallFVars xs type
      let fullType ← instantiateMVars fullType

      -- withAuxDecl adds a local variable so the body can reference the name being defined
      withAuxDecl shortDeclName fullType declName fun selfFvar => do
        trace[Aeneas.implDef] "impl_def: shortDeclName={shortDeclName} declName={declName} fvar={selfFvar} type={fullType}"
        let val ← elabTermEnsuringType valStx (some type)
        Term.synthesizeSyntheticMVarsNoPostponing
        let val ← instantiateMVars val

        trace[Aeneas.implDef] "Elaborated value: {val}"
        trace[Aeneas.implDef] "Value kind: {val.ctorName}"

        -- Resolve recursive structure fields
        let processedVal ← resolveStructFields val selfFvar.fvarId! type

        trace[Aeneas.implDef] "Processed value: {processedVal}"

        if exprContainsFVar processedVal selfFvar.fvarId! then
          throwError "impl_def: could not eliminate all self-references in {declName}"

        let fullVal ← mkLambdaFVars xs processedVal
        let fullVal ← instantiateMVars fullVal

        -- Collect and sort level params
        let mut s : CollectLevelParams.State := {}
        s := collectLevelParams s fullType
        s := collectLevelParams s fullVal
        let scopeLevelNames ← getLevelNames
        let allUserLevelNames := levelNames
        let levelParams ← IO.ofExcept <|
          sortDeclLevelParams scopeLevelNames allUserLevelNames s.params

        -- Create PreDefinition and add it
        let preDef : PreDefinition := {
          ref := id.raw
          kind := .def
          levelParams := levelParams
          modifiers := modifiers
          declName := declName
          binders := binders
          type := fullType
          value := fullVal
          termination := .none
        }

        let docCtx := (← getLCtx, ← getLocalInstances)
        addAndCompileNonRec docCtx preDef

end Aeneas.TraitDefault
