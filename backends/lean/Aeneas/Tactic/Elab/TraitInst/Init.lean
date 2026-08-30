import Lean
import Aeneas.Tactic.Elab.TraitInst.ParserSetup

/-!
# `@[trait_inst]` — Pretty-Printed Trait Instance Names

## Motivation

Aeneas generates extremely precise (long) names for Lean models of Rust trait
implementations to avoid collisions. For example:
`alloc.vec.core_clone_Clone'alloc_vec_Vec`. These are hard to read and write.

This module provides a bidirectional pretty-printing system that allows users to
write `{core.clone.Clone for alloc.vec.Vec<_>}` instead.

## Usage

```lean
-- Register a trait instance with a pretty name
@[trait_inst {core.clone.Clone for alloc.vec.Vec<_>}]
structure alloc_vec_core_clone_Clone_for_alloc_vec_Vec where ...

-- Use the pretty name to refer to it
#check {core.clone.Clone for alloc.vec.Vec<_>}
-- ^ elaborates to `alloc_vec_core_clone_Clone_for_alloc_vec_Vec`
```
-/

namespace Aeneas.TraitInst

open Lean Elab Meta Command

/-! ## Core Types -/

/-- Size parameter for Array types: either a concrete size or a wildcard. -/
inductive SizeParam where
  | lit (n : Nat)
  | hole
  deriving BEq, Hashable, Repr, Inhabited

/-- Simplified type identifier for trait instance matching.

- `name n args`: a named type (e.g., `alloc.vec.Vec` with args `[U8]`)
- `hole`: a wildcard type `_`
- `tuple tys`: a tuple type `(A, B, C)`
- `slice elem`: `Slice<T>`
- `array elem size`: `Array<T, N>` -/
inductive TypeId where
  | name (n : Name) (args : List TypeId)
  | hole
  | tuple (tys : List TypeId)
  | slice (elem : TypeId)
  | array (elem : TypeId) (size : SizeParam)
  deriving BEq, Hashable, Repr, Inhabited

/-- A trait instance identifier: trait name + self type + optional trait type arguments. -/
structure TraitInstanceId where
  traitId : Name
  selfType : TypeId
  traitArgs : List TypeId := []
  deriving BEq, Hashable, Repr, Inhabited

/-! ## Pretty-printing helpers -/

partial def SizeParam.toString : SizeParam → String
  | .lit n => s!"{n}"
  | .hole => "_"

instance : ToString SizeParam := ⟨SizeParam.toString⟩

partial def TypeId.toString : TypeId → String
  | .name n [] => n.toString
  | .name n args =>
    let argsStr := ", ".intercalate (args.map TypeId.toString)
    s!"{n}<{argsStr}>"
  | .hole => "_"
  | .tuple tys =>
    let tysStr := ", ".intercalate (tys.map TypeId.toString)
    s!"({tysStr})"
  | .slice elem => s!"Slice<{TypeId.toString elem}>"
  | .array elem size => s!"Array<{TypeId.toString elem}, {size}>"

instance : ToString TypeId := ⟨TypeId.toString⟩

def TraitInstanceId.toString : TraitInstanceId → String
  | { traitId, selfType, traitArgs := [] } =>
    s!"\{{traitId} for {selfType}}"
  | { traitId, selfType, traitArgs } =>
    let argsStr := ", ".intercalate (traitArgs.map TypeId.toString)
    s!"\{{traitId}<{argsStr}> for {selfType}}"

instance : ToString TraitInstanceId := ⟨TraitInstanceId.toString⟩

/-! ## Persistent State -/

/-- An entry in the trait instance registry. -/
structure TraitInstEntry where
  declName : Name
  instId : TraitInstanceId
  deriving Inhabited

/-- State of the trait instance registry: bidirectional maps. -/
structure TraitInstState where
  fwd : Std.HashMap TraitInstanceId Name := {}
  rev : Std.HashMap Name TraitInstanceId := {}
  deriving Inhabited

/-- Persistent environment extension storing the trait instance registry. -/
initialize traitInstExt : SimplePersistentEnvExtension TraitInstEntry TraitInstState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => {
      fwd := state.fwd.insert entry.instId entry.declName
      rev := state.rev.insert entry.declName entry.instId
    }
    addImportedFn := fun arrs =>
      let entries := arrs.flatten
      entries.foldl (fun state entry => {
        fwd := state.fwd.insert entry.instId entry.declName
        rev := state.rev.insert entry.declName entry.instId
      }) {}
  }

def findDeclByInstId (env : Environment) (instId : TraitInstanceId) : Option Name :=
  (traitInstExt.getState env).fwd[instId]?

def findInstIdByDecl (env : Environment) (declName : Name) : Option TraitInstanceId :=
  (traitInstExt.getState env).rev[declName]?

def registerTraitInstEntry (env : Environment) (declName : Name)
    (instId : TraitInstanceId) : Environment :=
  traitInstExt.addEntry env { declName, instId }

/-! ## Trace class -/

initialize registerTraceClass `Aeneas.traitInst

/-! ## Syntax -/

/-- Syntax category for dotted names like `core.clone.Clone`. -/
declare_syntax_cat traitInstName
syntax (name := tinIdent) ident : traitInstName
syntax (name := tinDotted) ident "." traitInstName : traitInstName

/-- Syntax category for types within trait instance notation. -/
declare_syntax_cat traitInstType
syntax (name := tiName) traitInstName : traitInstType
syntax (name := tiNameArgs) traitInstName "<" traitInstType,* Aeneas.TraitInst.closingAngle : traitInstType
syntax (name := tiHole) "_" : traitInstType
syntax (name := tiNum) num : traitInstType
syntax (name := tiTuple) "(" traitInstType "," ppSpace traitInstType,* ")" : traitInstType

/-- Syntax category for a trait instance identifier `{Trait for Type}`. -/
declare_syntax_cat traitInstId
syntax (name := tidBasic) "{" traitInstName ppSpace "for" ppSpace traitInstType "}" : traitInstId
syntax (name := tidArgs) "{" traitInstName "<" traitInstType,* Aeneas.TraitInst.closingAngle ppSpace "for" ppSpace traitInstType "}" : traitInstId

/-! ## Syntax → Core Type Conversion -/

/-- Prepend a string at the root of a hierarchical `Name`. -/
private def prependStr (s : String) (n : Name) : Name :=
  match n with
  | .anonymous => .str .anonymous s
  | .str parent s' => .str (prependStr s parent) s'
  | .num parent n' => .num (prependStr s parent) n'

/-- Convert a `traitInstName` syntax to a `Name`. -/
partial def elabTraitInstName (stx : Syntax) : Name :=
  if stx.isOfKind ``tinDotted then
    let s := stx[0].getId.eraseMacroScopes.getString!
    let rest := elabTraitInstName stx[2]
    prependStr s rest
  else if stx.isOfKind ``tinIdent then
    stx[0].getId.eraseMacroScopes
  else
    .anonymous

/-- Parse a `traitInstType` syntax node representing an Array size parameter. -/
private def elabSizeParam (stx : Syntax) : Except String SizeParam :=
  if stx.isOfKind ``tiHole then
    .ok .hole
  else if stx.isOfKind ``tiNum then
    .ok (.lit stx[0].toNat)
  else
    .error s!"Array size must be a number literal or _, got: {stx}"

/-- Convert a `traitInstType` syntax to a `TypeId`. -/
partial def elabTraitInstType (stx : Syntax) : Except String TypeId := do
  if stx.isOfKind ``tiName then
    let name := elabTraitInstName stx[0]
    return .name name []
  else if stx.isOfKind ``tiNameArgs then
    let name := elabTraitInstName stx[0]
    let argStxs := stx[2].getSepArgs
    -- Special-case Slice<T>
    if name == `Slice then
      if argStxs.size != 1 then
        .error "Slice expects exactly 1 type argument"
      else
        let elem ← elabTraitInstType argStxs[0]!
        return .slice elem
    -- Special-case Array<T, N>
    else if name == `Array then
      if argStxs.size != 2 then
        .error "Array expects exactly 2 arguments (element type and size)"
      else
        let elem ← elabTraitInstType argStxs[0]!
        let size ← elabSizeParam argStxs[1]!
        return .array elem size
    else
      let args ← argStxs.toList.mapM elabTraitInstType
      return .name name args
  else if stx.isOfKind ``tiHole then
    return .hole
  else if stx.isOfKind ``tiNum then
    .error "Number literals are only valid as Array size arguments"
  else if stx.isOfKind ``tiTuple then
    -- "(" traitInstType "," traitInstType,* ")"
    let first ← elabTraitInstType stx[1]
    let restStxs := stx[3].getSepArgs
    let rest ← restStxs.toList.mapM elabTraitInstType
    return .tuple (first :: rest)
  else
    .error s!"Unknown traitInstType syntax: {stx}"

/-- Convert a `traitInstId` syntax to a `TraitInstanceId`. -/
def elabTraitInstId (stx : Syntax) : Except String TraitInstanceId := do
  if stx.isOfKind ``tidBasic then
    -- "{" traitInstName "for" traitInstType "}"
    let traitName := elabTraitInstName stx[1]
    let selfType ← elabTraitInstType stx[3]
    return { traitId := traitName, selfType := selfType }
  else if stx.isOfKind ``tidArgs then
    -- "{" traitInstName "<" traitInstType,* ">" "for" traitInstType "}"
    let traitName := elabTraitInstName stx[1]
    let argStxs := stx[3].getSepArgs
    let args ← argStxs.toList.mapM elabTraitInstType
    let selfType ← elabTraitInstType stx[6]
    return { traitId := traitName, selfType := selfType, traitArgs := args }
  else
    .error s!"Unknown traitInstId syntax: {stx}"

/-! ## TypeId → Syntax Conversion (for delaboration) -/

private partial def sizeParamToSyntax (sp : SizeParam) : CoreM (TSyntax `traitInstType) := do
  match sp with
  | .hole => `(traitInstType| _)
  | .lit n =>
    let nLit := Syntax.mkNumLit (toString n)
    `(traitInstType| $nLit:num)

/-- Build a `TSepArray` by interleaving elements with a separator atom. -/
private def mkTSepArray (elems : Array (TSyntax k)) (sep : String := ",") :
    Syntax.TSepArray k sep :=
  if _h : elems.isEmpty then ⟨#[]⟩
  else
    let first : Array Syntax := #[elems[0]!.raw]
    let rest := elems.toList.drop 1
    let arr := rest.foldl (fun acc e => acc.push (mkAtom sep) |>.push e.raw) first
    ⟨arr⟩

/-- Strip a namespace prefix from a name. Returns the suffix if `n` starts with
    `prefix_`, otherwise returns `n` unchanged. -/
private def stripPrefix (prefix_ : Name) (n : Name) : Name :=
  if n == prefix_ then .anonymous
  else if prefix_ == .anonymous then n
  else
    match n with
    | .str parent s =>
      let parent' := stripPrefix prefix_ parent
      if parent' == parent then n  -- prefix not found
      else .str parent' s
    | .num parent k =>
      let parent' := stripPrefix prefix_ parent
      if parent' == parent then n
      else .num parent' k
    | .anonymous => n

/-- Make a `traitInstName` syntax from a `Name`, stripping the given namespace prefix.
    Uses a single `ident` token so Lean prints `Foo.Bar` without spaces. -/
private def mkTraitInstNameSyntaxShort (prefix_ : Name) (n : Name) :
    CoreM (TSyntax `traitInstName) := do
  let shortName := stripPrefix prefix_ n
  `(traitInstName| $(mkIdent shortName):ident)

partial def typeIdToSyntax (prefix_ : Name) (tid : TypeId) :
    CoreM (TSyntax `traitInstType) := do
  match tid with
  | .hole => `(traitInstType| _)
  | .name n [] => do
    let nameStx ← mkTraitInstNameSyntaxShort prefix_ n
    `(traitInstType| $nameStx:traitInstName)
  | .name n args => do
    let nameStx ← mkTraitInstNameSyntaxShort prefix_ n
    let argStxs ← args.mapM (typeIdToSyntax prefix_)
    let argArr := mkTSepArray argStxs.toArray
    `(traitInstType| $nameStx:traitInstName < $argArr,* >)
  | .tuple tys => do
    match tys with
    | [] => `(traitInstType| _)
    | first :: rest => do
      let firstStx ← typeIdToSyntax prefix_ first
      let restStxs ← rest.mapM (typeIdToSyntax prefix_)
      let restArr := mkTSepArray restStxs.toArray
      `(traitInstType| ( $firstStx:traitInstType , $restArr,* ))
  | .slice elem => do
    let elemStx ← typeIdToSyntax prefix_ elem
    let nameStx ← mkTraitInstNameSyntaxShort prefix_ `Slice
    let argArr := mkTSepArray #[elemStx]
    `(traitInstType| $nameStx:traitInstName < $argArr,* >)
  | .array elem size => do
    let elemStx ← typeIdToSyntax prefix_ elem
    let sizeStx ← sizeParamToSyntax size
    let nameStx ← mkTraitInstNameSyntaxShort prefix_ `Array
    let argArr := mkTSepArray #[elemStx, sizeStx]
    `(traitInstType| $nameStx:traitInstName < $argArr,* >)

def traitInstIdToSyntax (prefix_ : Name) (tid : TraitInstanceId) :
    CoreM (TSyntax `traitInstId) := do
  let nameStx ← mkTraitInstNameSyntaxShort prefix_ tid.traitId
  let selfStx ← typeIdToSyntax prefix_ tid.selfType
  match tid.traitArgs with
  | [] =>
    `(traitInstId| { $nameStx:traitInstName for $selfStx:traitInstType })
  | args => do
    let argStxs ← args.mapM (typeIdToSyntax prefix_)
    let argArr := mkTSepArray argStxs.toArray
    `(traitInstId| { $nameStx:traitInstName < $argArr,* > for $selfStx:traitInstType })

/-! ## Attribute: `@[trait_inst {Trait for Type}]` -/

syntax (name := traitInstAttr) "trait_inst " traitInstId : attr

/-- Try to resolve a raw name against the environment (works in CoreM). -/
private def tryResolveNameCore (rawName : Name) : CoreM Name := do
  try
    match (← Lean.resolveGlobalName rawName) with
    | (resolved, _) :: _ => return resolved
    | [] => return rawName
  catch _ => return rawName

/-- Resolve names in a TypeId (CoreM version). -/
private partial def resolveTypeIdCore (tid : TypeId) : CoreM TypeId := do
  match tid with
  | .name n args =>
    let n' ← tryResolveNameCore n
    let args' ← args.mapM resolveTypeIdCore
    return .name n' args'
  | .hole => return .hole
  | .tuple tys => return .tuple (← tys.mapM resolveTypeIdCore)
  | .slice elem => return .slice (← resolveTypeIdCore elem)
  | .array elem size => return .array (← resolveTypeIdCore elem) size

/-- Resolve names in a TraitInstanceId (CoreM version). -/
private def resolveTraitInstIdCore (tid : TraitInstanceId) : CoreM TraitInstanceId := do
  return {
    traitId := ← tryResolveNameCore tid.traitId
    selfType := ← resolveTypeIdCore tid.selfType
    traitArgs := ← tid.traitArgs.mapM resolveTypeIdCore
  }

initialize registerBuiltinAttribute {
  name := `traitInstAttr
  descr := "Register a definition as a trait instance with a pretty-printed identifier"
  applicationTime := .afterTypeChecking
  add := fun declName stx _attrKind => do
    -- stx = `(attr| trait_inst $tid:traitInstId)
    let tidStx := stx[1]
    match elabTraitInstId tidStx with
    | .ok rawInstId =>
      -- Resolve names against the current environment
      let instId ← resolveTraitInstIdCore rawInstId
      let env ← getEnv
      -- Check for duplicate registration
      match findDeclByInstId env instId with
      | some existingName =>
        if existingName != declName then
          throwError "trait_inst: {instId} is already registered to `{existingName}`"
      | none => pure ()
      trace[Aeneas.traitInst] "Registering {declName} as {instId}"
      modifyEnv fun env => registerTraitInstEntry env declName instId
    | .error msg =>
      throwError "trait_inst: {msg}"
}

/-! ## Term Elaboration: `{Trait for Type}` → definition name -/

/-- Try to resolve a raw name against the environment (respecting open namespaces). -/
private def tryResolveNameM (rawName : Name) : Term.TermElabM Name := do
  try
    match (← Lean.resolveGlobalName rawName) with
    | (resolved, _) :: _ => return resolved
    | [] => return rawName
  catch _ => return rawName

/-- Resolve names in a `TypeId` against the current environment. -/
private partial def resolveTypeIdM (tid : TypeId) : Term.TermElabM TypeId := do
  match tid with
  | .name n args =>
    let n' ← tryResolveNameM n
    let args' ← args.mapM resolveTypeIdM
    return .name n' args'
  | .hole => return .hole
  | .tuple tys => return .tuple (← tys.mapM resolveTypeIdM)
  | .slice elem => return .slice (← resolveTypeIdM elem)
  | .array elem size => return .array (← resolveTypeIdM elem) size

/-- Resolve names in a `TraitInstanceId` against the current environment. -/
private def resolveTraitInstIdM (tid : TraitInstanceId) : Term.TermElabM TraitInstanceId := do
  return {
    traitId := ← tryResolveNameM tid.traitId
    selfType := ← resolveTypeIdM tid.selfType
    traitArgs := ← tid.traitArgs.mapM resolveTypeIdM
  }

/-- Walk the syntax tree of a `traitInstId` and register `TermInfo` for each
    `traitInstName` node, enabling hover and go-to-definition in the IDE.
    Only annotates the outermost name node (not inner suffixes of dotted names). -/
private partial def annotateTraitInstSyntax (stx : Syntax) : Term.TermElabM Unit := do
  if stx.isOfKind ``tinIdent || stx.isOfKind ``tinDotted then
    let name := elabTraitInstName stx
    let resolved ← tryResolveNameM name
    let env ← getEnv
    if env.contains resolved then
      let lctx ← getLCtx
      Elab.pushInfoLeaf (.ofTermInfo {
        elaborator := `Aeneas.TraitInst
        stx := stx
        lctx := lctx
        expectedType? := none
        expr := mkConst resolved
      })
    return
  for child in stx.getArgs do
    annotateTraitInstSyntax child

elab:max tid:traitInstId : term => do
  match elabTraitInstId tid with
  | .ok instId =>
    let env ← getEnv
    let declName? := findDeclByInstId env instId
    let declName? ← match declName? with
      | some _ => pure declName?
      | none =>
        let resolved ← resolveTraitInstIdM instId
        pure (findDeclByInstId env resolved)
    match declName? with
    | some declName =>
      trace[Aeneas.traitInst] "Resolved {instId} to `{declName}`"
      let expr := mkConst declName
      -- Annotate the whole expression (parent TermInfo)
      discard <| Term.addTermInfo tid.raw expr
      -- Annotate inner names AFTER the outer info — as sibling leaves with
      -- smaller ranges, they win over the outer node in `smallestInfo?`
      annotateTraitInstSyntax tid.raw
      return expr
    | none =>
      throwError "trait_inst: no definition registered for {instId}"
  | .error msg =>
    throwError "trait_inst: {msg}"

/-! ## Delaboration -/

open PrettyPrinter.Delaborator in
/-- Make a `traitInstName` syntax from a `Name`, stripping the given namespace prefix.
    The ident is annotated so the Infoview renders it as interactive (hover/go-to-def). -/
private def mkAnnotatedTraitInstNameSyntax (prefix_ : Name) (n : Name) :
    Delab := do
  let shortName := stripPrefix prefix_ n
  let env ← getEnv
  let ident ← if env.contains n then
    mkAnnotatedIdent shortName (mkConst n)
  else
    pure (mkIdent shortName)
  pure ⟨(← `(traitInstName| $ident:ident)).raw⟩

open PrettyPrinter.Delaborator in
partial def typeIdToDelabSyntax (prefix_ : Name) (tid : TypeId) :
    Delab := do
  let r ← go prefix_ tid
  -- Cast from TSyntax `traitInstType to TSyntax `term
  pure ⟨r.raw⟩
where
  cast (stx : TSyntax `term) : TSyntax `traitInstType := ⟨stx.raw⟩
  castName (stx : TSyntax `term) : TSyntax `traitInstName := ⟨stx.raw⟩
  castArr (stxs : Array (TSyntax `term)) : Array (TSyntax `traitInstType) :=
    stxs.map (⟨·.raw⟩)
  go (prefix_ : Name) (tid : TypeId) : DelabM (TSyntax `traitInstType) := do
    match tid with
    | .hole => `(traitInstType| _)
    | .name n [] => do
      let nameStx ← mkAnnotatedTraitInstNameSyntax prefix_ n
      `(traitInstType| $(castName nameStx):traitInstName)
    | .name n args => do
      let nameStx ← mkAnnotatedTraitInstNameSyntax prefix_ n
      let argStxs ← args.mapM (go prefix_)
      let argArr := mkTSepArray argStxs.toArray
      `(traitInstType| $(castName nameStx):traitInstName < $argArr,* >)
    | .tuple tys => do
      match tys with
      | [] => `(traitInstType| _)
      | first :: rest => do
        let firstStx ← go prefix_ first
        let restStxs ← rest.mapM (go prefix_)
        let restArr := mkTSepArray restStxs.toArray
        `(traitInstType| ( $firstStx:traitInstType , $restArr,* ))
    | .slice elem => do
      let elemStx ← go prefix_ elem
      let nameStx ← mkAnnotatedTraitInstNameSyntax prefix_ `Slice
      let argArr := mkTSepArray #[elemStx]
      `(traitInstType| $(castName nameStx):traitInstName < $argArr,* >)
    | .array elem size => do
      let elemStx ← go prefix_ elem
      let sizeStx ← sizeParamToSyntax size
      let nameStx ← mkAnnotatedTraitInstNameSyntax prefix_ `Array
      let argArr := mkTSepArray #[elemStx, sizeStx]
      `(traitInstType| $(castName nameStx):traitInstName < $argArr,* >)

open PrettyPrinter.Delaborator in
def traitInstIdToDelabSyntax (prefix_ : Name) (tid : TraitInstanceId) :
    Delab := do
  let nameStx : TSyntax `traitInstName ← do
    let r ← mkAnnotatedTraitInstNameSyntax prefix_ tid.traitId
    pure ⟨r.raw⟩
  let selfStx : TSyntax `traitInstType ← do
    let r ← typeIdToDelabSyntax prefix_ tid.selfType
    pure ⟨r.raw⟩
  let r ← match tid.traitArgs with
  | [] =>
    `(traitInstId| { $nameStx:traitInstName for $selfStx:traitInstType })
  | args => do
    let argStxs ← args.mapM (typeIdToDelabSyntax prefix_)
    let argArr : Syntax.TSepArray `traitInstType "," := mkTSepArray (argStxs.toArray.map (⟨·.raw⟩))
    `(traitInstId| { $nameStx:traitInstName < $argArr,* > for $selfStx:traitInstType })
  pure ⟨r.raw⟩

open PrettyPrinter.Delaborator in
/-- Delaborator that pretty-prints registered trait instance definitions.
    Identifiers inside the `{...}` are annotated for hover/go-to-def in the Infoview. -/
@[delab app]
def delabTraitInstApp : Delab := do
  let e ← SubExpr.getExpr
  let fn := e.getAppFn
  guard fn.isConst
  let name := fn.constName!
  let env ← getEnv
  match findInstIdByDecl env name with
  | some instId =>
    let currNs ← getCurrNamespace
    traitInstIdToDelabSyntax currNs instId
  | none => failure

end Aeneas.TraitInst
