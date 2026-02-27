import Lean

/-!
# `impl_def` and `@[trait_default]`

## Motivation

When modelling Rust trait implementations in Lean, a trait is represented as a
structure whose fields correspond to the trait's associated types, constants, and
methods. A trait *implementation* is then a value of that structure type.

Some trait methods have **default implementations** that refer to other fields of
the same trait. For example, consider the following Rust code:

```rust
trait MyTrait {
    const N: usize;
    // P has a default implementation that depends on N
    fn p(&self) -> usize { Self::N + 3 }
}

struct Foo;

impl MyTrait for Foo {
    const N: usize = 5;
    // p is not overridden, so the default is used
}
```

Aeneas translates this into a Lean model where the trait becomes a structure and
the default method body becomes a separate definition:

```lean
structure MyTrait where
  N : Nat
  P : Nat

@[trait_default]
def MyTrait.P.default (self : MyTrait) : Nat := self.N + 3
```

When we build the concrete implementation for `Foo` we want to write:

```
impl_def MyTraitInst : MyTrait := {
  N := 5
  P := MyTrait.P.default MyTraitInst   -- refers to self!
}
```

A plain `def` would be rejected because `MyTraitInst` appears in its own body,
creating a circular definition without a clear termination measure. The `impl_def`
command resolves this circularity at elaboration time by:

1. Letting the body reference the name being defined (via a temporary local
   variable, using `withAuxDecl`).
2. After elaboration, **unfolding** every `@[trait_default]`-marked function call,
   exposing the field projections (e.g., `self.N`).
3. **Substituting** those projections with the already-resolved field values.
4. Repeating until every field is free of the self-reference.

The result is a fully concrete, non-recursive definition that Lean's kernel
accepts.

## `@[trait_default]` attribute

Mark a function with `@[trait_default]` to tell `impl_def` that it may be
unfolded during resolution. The attribute is typically placed on default method
implementations that refer to the trait instance (`self`). The unfolding works
even if the definition is also marked `@[irreducible]`.

## `impl_def` command

`impl_def` has the same surface syntax as `def`:

```
impl_def <name> <binders>? : <type> := <body>
```

It supports:
- Parameterised definitions: `impl_def Foo (n : Nat) : Bar n := { ... }`
- Declaration modifiers: `@[simp] impl_def ...`, `/-- doc -/ impl_def ...`
- Universe polymorphism (level parameters are collected automatically)

### Resolution algorithm

Given a structure with fields `f₁, …, fₙ` and a constructor application
`S.mk p₁ … pₖ v₁ … vₙ` where `vᵢ` is the value for field `fᵢ`:

1. **Partition** fields into *resolved* (no self-reference) and *unresolved*.
2. **Loop** (at most `n + 1` iterations):
   a. For each unresolved field value `vᵢ`:
      - **Unfold** all `@[trait_default]` calls (`unfoldTraitDefaults`).
      - **Substitute** projections of the self-reference with resolved values
        (`substituteProjections`).
   b. If `vᵢ` no longer mentions the self-reference, mark it resolved.
   c. Stop when no progress is made.
3. If there remains unresolved fields, report an error.

### Limitations

- Only `:= body` syntax is supported (not `where` blocks or pattern-matching
  definitions).
- The type annotation is mandatory.
- The body must elaborate to a structure constructor application.
- Every self-referential cycle must be breakable by unfolding
  `@[trait_default]` functions and substituting already-known fields.

## Trace output

Enable `set_option trace.Aeneas.implDef true` to see the resolution steps.
-/

namespace Aeneas.TraitDefault

open Lean Elab Term Meta Command
open Lean.Parser.Term Lean.Parser.Command

/-! ## Attribute -/

/-- Register the `@[trait_default]` tag attribute. Functions marked with this attribute
    are eligible for automatic unfolding by `impl_def` during field resolution. -/
initialize traitDefaultAttr : TagAttribute ←
  registerTagAttribute `trait_default
    "Marks a function as a trait default that can be unfolded by `impl_def`."

/-! ## Trace class -/

initialize registerTraceClass `Aeneas.implDef

/-! ## Helpers -/

/-- Return `true` if `e` contains the free variable `fvarId` anywhere in its sub-expressions.

    Used to decide whether a field value still depends on the self-reference and therefore
    needs further resolution. -/
def exprContainsFVar (e : Expr) (fvarId : FVarId) : Bool :=
  Option.isSome <| e.find? fun
    | .fvar id => id == fvarId
    | _ => false

/-- Recursively unfold every `@[trait_default]`-marked constant application in `e`,
    beta-reducing after each unfolding step.

    Uses `TransparencyMode.all` so that `@[irreducible]` definitions are also unfolded —
    this is needed because some generated default implementations are marked as irreducible.

    The traversal uses `.visit` (not `.done`) after unfolding so that nested
    `@[trait_default]` calls exposed by the unfolding are also processed. -/
partial def unfoldTraitDefaults (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Core.transform e (pre := fun e => do
    let fn := e.getAppFn
    if let .const name _ := fn then
      if traitDefaultAttr.hasTag env name then
        if let some e' ← withTransparency .all <| unfoldDefinition? e then
          return .visit e'.headBeta
    return .continue)

/-- Replace every projection of the self-reference free variable `selfFvarId` in `e` with
    the corresponding value from `resolvedFields`.

    Lean represents structure field access in two forms after elaboration:

    1. **Native projection** (`Expr.proj structName fieldIdx arg`):
       e.g., `Expr.proj ``MyTrait 0 selfFvar` for field index 0.

    2. **Application-style projection** (`ProjFn selfFvar`):
       e.g., `@MyTrait.N selfFvar`, where `MyTrait.N` is the projection function.
       This is the more common form after `unfoldTraitDefaults` + beta-reduction.

    Both forms are handled. The self-reference `arg`/`selfFvar` may be wrapped in
    `Expr.mdata` (metadata) by `withAuxDecl`, so we call `.consumeMData` before
    checking the free-variable identity.

    The `projMap` maps each projection function name to its field index, built from
    `StructureInfo.getProjFn?`. -/
def substituteProjections (e : Expr) (selfFvarId : FVarId) (structName : Name)
    (resolvedFields : Std.HashMap Nat Expr) : MetaM Expr := do
  let env ← getEnv
  let some structInfo := getStructureInfo? env structName
    | return e
  -- Build a map from projection function names to field indices
  let mut projMap : Std.HashMap Name Nat := {}
  for i in [:structInfo.fieldNames.size] do
    if let some projFn := structInfo.getProjFn? i then
      projMap := projMap.insert projFn i
  trace[Aeneas.implDef] "substituteProjections: projMap = {projMap.toArray.map (·.1)}"
  Core.transform e (pre := fun e => do
    match e with
    -- Case 1: native projection syntax
    | .proj sname idx arg =>
      if sname == structName then
        let argFn := arg.consumeMData.getAppFn
        if argFn.isFVar && argFn.fvarId! == selfFvarId then
          if let some val := resolvedFields[idx]? then
            return .done val
      return .continue
    | _ =>
      -- Case 2: application-style projection (e.g., `@Trait.N selfFvar`)
      let fn := e.getAppFn
      let args := e.getAppArgs
      if let .const projName _ := fn then
        if args.size > 0 then
          if let some fieldIdx := projMap[projName]? then
            let lastArg := args.back!.consumeMData
            let lastArgFn := lastArg.getAppFn
            if lastArgFn.isFVar && lastArgFn.fvarId! == selfFvarId then
              if let some val := resolvedFields[fieldIdx]? then
                return .done val
      return .continue)

/-- Resolve all fields of a structure constructor application, eliminating
    self-references.

    **Inputs:**
    - `value`: the elaborated body, expected to be a constructor application
      `S.mk p₁ … pₖ v₁ … vₙ` where `p₁ … pₖ` are the structure's type
      parameters and `v₁ … vₙ` are the field values.
    - `selfFvarId`: the free variable introduced by `withAuxDecl` to represent
      the definition being built.
    - `type`: the expected structure type (e.g., `MyTrait` or `Trait1 n Bool`),
      used to look up `StructureInfo`.

    **Algorithm:**

    1. Split constructor arguments into parameter args (`p₁…pₖ`) and field
       values (`v₁…vₙ`) using `StructureInfo.fieldNames.size`.
    2. Classify each field as *resolved* (does not mention `selfFvarId`) or
       *unresolved*.
    3. Iterate up to `n + 1` times:
       - For each unresolved field, call `unfoldTraitDefaults` then
         `substituteProjections` with the currently resolved fields.
       - If the field no longer mentions `selfFvarId`, mark it resolved.
       - Stop early if an iteration makes no progress.
    4. Error if any fields remain unresolved.
    5. Reassemble the constructor application with resolved field values. -/
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

  -- Initial classification
  for i in [:numFields] do
    let fieldVal := fieldValues[i]!
    if !exprContainsFVar fieldVal selfFvarId then
      resolved := resolved.insert i fieldVal
    else
      unresolved := unresolved.push i

  -- Fixed-point iteration
  let mut iterCount := 0
  let maxIters := numFields + 1
  let mut progress := true
  while progress && iterCount < maxIters do
    iterCount := iterCount + 1
    progress := false
    let mut stillUnresolved : Array Nat := #[]
    for i in unresolved do
      let fieldVal := fieldValues[i]!
      let fieldVal' ← unfoldTraitDefaults fieldVal
      let fieldVal' ← substituteProjections fieldVal' selfFvarId structName resolved
      if !exprContainsFVar fieldVal' selfFvarId then
        resolved := resolved.insert i fieldVal'
        fieldValues := fieldValues.set! i fieldVal'
        progress := true
        trace[Aeneas.implDef] "  {structInfo.fieldNames[i]!} resolved"
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

/-- The `impl_def` command elaborator.

    Elaboration proceeds as follows:

    1. **Parse** modifiers, identifier, binders, type annotation, and value.
    2. **Elaborate binders and type** in the standard way (`elabBinders`, `elabType`).
    3. **Introduce a temporary local variable** for the name being defined via
       `withAuxDecl`. This lets the body refer to the definition by name without
       creating an actual recursive definition.
    4. **Elaborate the body** against the expected type. At this point the body may
       contain free-variable references to the auxiliary declaration.
    5. **Resolve self-references** via `resolveStructFields`.
    6. **Abstract** over the binder variables (`mkLambdaFVars`) to produce the full
       definition value.
    7. **Collect universe level parameters** and build a `PreDefinition`.
    8. **Register** the definition with `addAndCompileNonRec`, which type-checks,
       compiles, and applies any declaration attributes (e.g., `@[simp]`). -/
elab mods:declModifiers "impl_def " id:declId sig:optDeclSig val:declVal : command => do
  let modifiers ← elabModifiers mods
  let (binders, type?) := expandOptDeclSig sig
  let typeStx ← match type? with
    | some t => pure t
    | none => throwErrorAt sig "impl_def requires an explicit type annotation"

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

      -- Introduce a local variable so the body can mention the name being defined
      withAuxDecl shortDeclName fullType declName fun selfFvar => do
        trace[Aeneas.implDef] "impl_def: declName={declName} fvar={selfFvar} type={fullType}"
        let val ← elabTermEnsuringType valStx (some type)
        Term.synthesizeSyntheticMVarsNoPostponing
        let val ← instantiateMVars val

        trace[Aeneas.implDef] "Elaborated value: {val}"

        -- Resolve recursive structure fields
        let processedVal ← resolveStructFields val selfFvar.fvarId! type

        trace[Aeneas.implDef] "Processed value: {processedVal}"

        if exprContainsFVar processedVal selfFvar.fvarId! then
          throwError "impl_def: could not eliminate all self-references in {declName}"

        let fullVal ← mkLambdaFVars xs processedVal
        let fullVal ← instantiateMVars fullVal

        -- Collect and sort universe level parameters
        let mut s : CollectLevelParams.State := {}
        s := collectLevelParams s fullType
        s := collectLevelParams s fullVal
        let scopeLevelNames ← getLevelNames
        let allUserLevelNames := levelNames
        let levelParams ← IO.ofExcept <|
          sortDeclLevelParams scopeLevelNames allUserLevelNames s.params

        -- Build and register the definition
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
