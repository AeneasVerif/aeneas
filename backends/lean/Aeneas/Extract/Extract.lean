import AeneasMeta.Extensions
/-! Helpers to provide informations about the models for the Rust standard library -/

open Lean

namespace Aeneas.Extract

initialize registerTraceClass `Extract

structure Field where
  rust : String
  extract : String
deriving Repr, Inhabited

instance : ToMessageData Field where
  toMessageData x := m!"\{ rust : {x.rust}, extract : {x.extract} }"

structure Variant where
  -- Name of the variant, in Rust
  rust : String
  -- Name of the variant, once extracted
  extract : String
  -- Names of the fields
  fields : Option (List String) := none
deriving Repr, Inhabited, BEq

instance : ToMessageData Variant where
  toMessageData x := m!"\{ rust : {x.rust}, extract : {x.extract}, fields: {x.fields} }"

inductive TypeBody where
/-- The constructor name and the map for the field names -/
| struct (fieldNames : List Field)
/-- For every variant, a map for the field names -/
| enum (variants : List Variant)
| opaque
deriving Repr, Inhabited

instance : ToMessageData TypeBody where
  toMessageData x :=
    match x with
    | .struct fields => m!"Struct ({fields})"
    | .enum variants => m!"Enum ({variants})"
    | .opaque => m!"Opaque"

structure TypeInfo where
  /-- The name to use for extraction -/
  extract : Option String := none
  /-- We might want to filter some of the type parameters.

      For instance, `Vec` type takes a type parameter for the allocator,
      which we want to ignore. -/
  keepParams : Option (List Bool) := none
  /-- Whenever printing the variants, should we prefix them with the type name or not?

    Generally speaking we need to (e.g., we generate `Foo.bar` instead of `bar`) but for
    some enumerations we don't (it's the case of `Option`, for which we can write `some`
    directly, rather than `Option.some`).
    -/
  prefixVariantNames : Bool := true
  body : TypeBody := .opaque
deriving Repr, Inhabited

instance : ToMessageData TypeInfo where
  toMessageData x :=
    m!"\{ extract : {x.extract},\n  keepParams : {x.keepParams},\n  body : {x.body} }"

structure ConstInfo where
  extract : Option String := none
deriving Repr, Inhabited

instance : ToMessageData ConstInfo where
  toMessageData x :=
    m!"\{ extract : {x.extract} }"

structure FunInfo where
  /-- The name to use for the extraction -/
  extract : Option String := none
  /-- We might want to filter some of the function parameters, for instance
      the `Allocator` parameter, which we actually don't use. -/
  keepParams : Option (List Bool) := none
  canFail : Bool := true
  /-- If the function can not fail, should we still lift it to the [Result]
      monad? This can make reasonings easier, as we can then use [progress]
      to do proofs in a Hoare-Logic style, rather than equational reasonings. -/
  lift : Bool := true
  /-- If this is a trait method: does this method have a default
      implementation? If yes, we might want to register it as well. -/
  hasDefault : Bool := false
deriving Repr, Inhabited

instance : ToMessageData FunInfo where
  toMessageData x :=
    m!"\{ extract : {x.extract},\n  keepParams : {x.keepParams},\n  canFail : {x.canFail},\n  lift : {x.lift},\n  hasDefault : {x.hasDefault} }"

structure TraitConst where
  rust : String
  extract : String
deriving Repr, Inhabited

instance : ToMessageData TraitConst where
  toMessageData x :=
    m!"\{ rust : {x.rust}, extract : {x.extract} }"

structure TraitType where
  rust : String
  extract : String
deriving Repr, Inhabited

instance : ToMessageData TraitType where
  toMessageData x :=
    m!"\{ rust : {x.rust}, extract : {x.extract} }"

structure TraitMethod where
  rust : String
  extract : String
deriving Repr, Inhabited

instance : ToMessageData TraitMethod where
  toMessageData x :=
    m!"\{ rust : {x.rust}, extract : {x.extract} }"

/-- A trait declaration.

For every kind of trait elements (parent clauses, consts, types and methods) we use two lists:
a list of names and a list of names augmented with additional information. Those lists should
be disjoint, and we use them only for convenience:
- if the user wants to indicate that a field stands for a type in the Rust trait declaration, they
  can simply put it in the `types` list
- if a field stands for a type *and* the Rust and Lean names are not the same, they can use the `typesInfo` list
When processing the attribute, we augment the list of names by filling the missing information and merge the two
lists. Finally, by default we consider that a field represents a method (the reason being that there tends to
be a lot more methods than elements of the other kinds).
-/
structure TraitDecl where
  extract : Option String := none
  parentClauses : List String := []
  consts : List String := []
  constsInfo : List TraitConst := []
  types : List String := []
  typesInfo : List TraitType := []
  methods : List String := []
  methodsInfo : List TraitMethod := []
  /-- The list of default methods -/
  defaultMethods : List String := []
deriving Repr, Inhabited

instance : ToMessageData TraitDecl where
  toMessageData x :=
    m!"\{ extract : {x.extract},\n  parentClauses : {x.parentClauses},
  consts : {x.consts},\n  constsInfo : {x.constsInfo},
  types : {x.types},\n  typesInfo : {x.typesInfo},
  methods : {x.methods},\n  methodsInfo : {x.methodsInfo},
  defaultMethods : {x.defaultMethods} }"

structure TraitImpl where
  extract : Option String := none
  keepParams : Option (List Bool) := none
deriving Repr, Inhabited

instance : ToMessageData TraitImpl where
  toMessageData x :=
    m!"\{ extract : {x.extract}, keepParams : {x.keepParams} }"

def getLocalFileName : AttrM String := do
  let name ← getFileName
  /- Remove the prefix (we want to get rid of the part of the path which is local
     to the machine - we do this by spotting the first occurrence of the path which
     is equal to `Aeneas`, when exploring the path by starting at the end) -/
  let elems := name.splitOn "/"
  let elems := (elems.map (String.splitOn (sep := "\\"))).flatten
  let elems := elems.filterMap (fun s => if s = "" then none else some s)
  let mut out := []
  let mut found := false
  for e in elems.reverse do
    if e = "Aeneas" then
      found := true
      break
    out := e :: out
  /- It can happen that we can't process the file, in particular when Aeneas generates models/axioms
     for external definitions when one extracts a crate outside of the Aeneas repo (in which case
     the path will not be prefixed with `Aeneas`). This is fine because in that case we will not
     need to output the list of models for the standard library, together with the paths to the
     Lean definitions, so we can simply reuse the original name. -/
  if found
  then pure (List.foldl (fun s0 s1 => s0 ++ "/" ++ s1) "Aeneas" out)
  else pure name

structure Span where
  fileName : String
  pos : Position
deriving Inhabited

/- Remark: we retrieve the span of some syntax, rather than a definition (by using `findDeclarationRange?`)
   because:
  - when processing the attribute the range is not saved in the environment yet
  - it can happen that the attribute is not added exactly on the definition, when we're mapping a Rust definition
    to a definition in the Lean standard library for instance (in that case, we write somewhere `attribute [rust_type "..."] ...`).
    When this happens, the most important information is to know where the attribute was written, not where the definition
    is (we can always jump to the definition from where the attribute is declared).

   TODO: how to retrieve the file in which a definition was defined?
   For now I can only retrieve the name of the current file and the code of `Lean/Server/Goto.lean`
   does quite a few things (in particular, does it work in non-interactive mode?). -/
def getLocalSyntaxSpan (stx : Syntax) : AttrM (Option Span) := do
  let fileName ← getLocalFileName
  let some pos := stx.getPos?
    | trace[Extract] "Could not retrieve the declaration range"; return none
  let fileMap ← getFileMap
  let pos := fileMap.toPosition pos
  pure (some ⟨ fileName, pos ⟩)

def mkExtension (α : Type) (name : Name := by exact decl_name%) :
  IO (SimpleScopedEnvExtension (String × Span × α) (Array (String × Span × α))) :=
  registerSimpleScopedEnvExtension {
    name        := name,
    initial     := #[],
    addEntry    := Array.push,
  }

structure Attribute (α : Type) where
  ext : SimpleScopedEnvExtension (String × Span × α) (Array (String × Span × α))
  attr : AttributeImpl
deriving Inhabited

def mkAttribute {α} (extName : Name)
  (attrName : Name) -- this has to be the same name as the syntax
  (descr : String) (elabInfo : Syntax → AttrM (String × α))
  (processDecl : Name → String → α → AttrM α)
   : IO (Attribute α) := do
  let ext ← mkExtension α extName
  let attr : AttributeImpl := {
    name := attrName
    descr
    add := fun declName stx attrKind => do
      let (pat, info) ← elabInfo stx
      let some span ← getLocalSyntaxSpan stx
        | throwError "Could not compute the span of the definition"
      trace[Extract] "File: {span.fileName}, pos: {span.pos}"
      let info ← processDecl declName pat info
      ScopedEnvExtension.add ext (pat, span, info) attrKind
  }
  registerBuiltinAttribute attr
  pure { ext, attr }

-- Small helper: remove the prefix `Aeneas.Std` from a name
def removeNamePrefix (n0 : Name) : AttrM Name := do
  let rec remove (n : Name) := do
    match n with
    | .str (.str .anonymous "Aeneas") "Std" => pure .anonymous
    | .str .anonymous "Lean" =>
      /- We allow mapping Rust definitions to definition from the standard Lean library -/
      pure .anonymous
    | .str pre str => pure (.str (← remove pre) str)
    | _ =>
      /- Sometimes, the definitions from the standard library don't even have the `Lean` prefix
         (happens with `core::cmp::Ordering` → `Ordering`) -/
      pure n
  remove n0

def leanNameToRust (n0 : Name) : AttrM String := do
  let rec toRust (n : Name) : AttrM String := do
    match n with
    | .anonymous => pure ""
    | .str pre suf => pure ((← toRust pre) ++ "::" ++ suf)
    | _ => throwError "Ill-formed name: `{n0}`"
  toRust n0

def fieldNameToString (n : Name) : AttrM String := do
  match n with
  | .str .anonymous field =>
    pure field
  | _ => throwError "Ill-formed field name: `{n}`"

def variantNameToString (declName n : Name) : AttrM String := do
  match n with
  | .str pre variant =>
    if pre ≠ declName then throwError "Ill-formed variant name: `{n}`"
    pure variant
  | _ => throwError "Ill-formed field name: `{n}`"

/-!
# Types
-/

/- Cheating a bit: we elaborate the optional information by using the command config elaborator.
   This allows to have nice syntax for optional fields and at a small cost. -/
declare_command_config_elab elabRustTypeInfo TypeInfo

/-- Declare that a definition models a Rust type.

The syntax is `rust_type "NAME_PATTERN" ...`. The name pattern is given by Aeneas when generating
a declaration for a missing definition: one just has to copy-paste it.

The additional options are used to fill the fields of `Aeneas.Extract.TypeInfo`.
The options are:
- `typeBody`: this allows providing information about the name of the fields (for structures)
  and variants (for enumerations), when the Rust name doesn't match the Lean name.

  For instance, the following declares that `Foo` implements `core::Foo` and that the field
  `x` (in Rust) has to be renamed to `z` in Lean. As we do not provide information about `y`,
  it means that the name is the same in Rust and Lean.
  ```
  @[rust_type "core::Foo" (typeBody := .struct [⟨"x", "z"⟩])]
  structure Foo where
    z : U32
    y : U32
  ```

  The following declares that `Bar` implements `core::Bar` and that the field `Baz` (in Rust) has to
  be renamed to `V` in Lean. As we do not provide information about `Fuz`, it means that that name is
  the same in Rust and Lean.
  ```
  @[rust_type "core::Bar" (typeBody := .enum [⟨"Baz", "V"⟩])]
  inductive Bar where
    | V | Fuz
  ```

- `keepParams`: it can happen that some type parameters are useless and omitted in the Lean model
  (for instance, the allocator parameter in `Vec::new`). If provided, `keepParams` should list the
  parameters that we want to keep (`true` means "keep").

- `prefixVariantNames`: if `true` (which is the default), it means that in the code generated by Aeneas,
  the variant names should be prefixed with the type name (e.g., `Foo.Bar` instead of `Bar`). As variant
  names can collision we should always do this to prevent ambiguities: only a few types (like `Option`)
  allow using the variant name directly.
-/
syntax (name := rustType) "rust_type" str Parser.Tactic.optConfig : attr

def elabTypeNameInfo (stx : Syntax) : AttrM (String × TypeInfo) :=
  withRef stx do
    match stx with
    | `(attr| rust_type $pat $config) => do
      let pat := pat.getString
      if pat = "" then throwError "Not a valid name pattern: {pat}"
      let info ← liftCommandElabM (elabRustTypeInfo config)
      pure (pat, info)
    | _ => Lean.Elab.throwUnsupportedSyntax

/-- This helper completes the information available in the information provided by the user by
    looking at the definition itself. -/
def processType (declName : Name) (_pat : String) (info : TypeInfo) : AttrM TypeInfo := do
  trace[Extract] "declName: {declName}"
  let env ← getEnv
  -- Retrieve the extraction name
  let extractName : String ← do
    match info.extract with
    | some name => pure name
    | none =>
      trace[Extract] "Generating the extraction name"
      pure (← (removeNamePrefix declName)).toString
  let info : TypeInfo := { info with extract := extractName }

  -- Analyze the body
  let some decl := env.findAsync? declName
      | throwError "Could not find theorem {declName}"

  match decl.constInfo.get with
  | .inductInfo const =>
    trace[Extract] "Found a type definition"
    /- Compute the information about the variants/fields -/
    let structInfo := getStructureInfo? env declName
    match structInfo with
    | none =>
      trace[Extract] "The type definition is for an enumeration"
      let variants ← do
        match info.body with
        | .enum variants => pure variants
        | .opaque => pure []
        | .struct _ => throwError "The user-provided information is for a structure while the type is an inductive"
      /- Go through the variants and retrieve their names.
         We first need to use the user provided information to compute a map from Lean name to user information. -/
      let mut providedVariants := Std.HashMap.emptyWithCapacity
      let mut rustVariants := Std.HashSet.emptyWithCapacity
      let leanVariants := Std.HashSet.ofList (← const.ctors.mapM (variantNameToString declName))
      /- We want to check the user-provided information before using it, for instance to detect name collisions -/
      for x in variants do
        if providedVariants.contains x.extract then
          throwError "A variant has been defined twice: `{x.extract}`"
        if rustVariants.contains x.rust then
          throwError "The Rust variant name `{x.rust}` is used twice"
        if ¬ leanVariants.contains x.extract then
          throwError "The user provides a mapping for a variant which is not present in the Lean definition: {x.extract}"
        providedVariants := providedVariants.insert x.extract x
        rustVariants := rustVariants.insert x.rust
      /- Now we go through the Lean variants and use the user provided information if there is, and automatically
         compute the Rust name otherwise -/
      let variants : List Variant ← List.mapM (fun ctorName => do
        let ctorName ← variantNameToString declName ctorName
        match providedVariants.get? ctorName with
        | some info => pure info
        | none => pure { rust := ctorName.capitalize, extract := ctorName }) const.ctors
      trace[Extract] "variants: {variants}"
      pure { info with body := .enum variants }
    | some structInfo =>
      trace[Extract] "The type definition is for a structure"
      /- Similar to the inductive case: we check the user-provided information before using it, for instance
         to detect name collisions. -/
      let fields ← do
        match info.body with
        | .struct fields => pure fields
        | .opaque => pure []
        | .enum _ => throwError "The user-provided information is for a variant while the type is a structure"
      /- Compute the map from Lean field name to user information while doing the sanity checks -/
      let mut providedFields := Std.HashMap.emptyWithCapacity
      let mut rustFields := Std.HashSet.emptyWithCapacity
      let leanFields := Std.HashSet.ofList (← structInfo.fieldNames.toList.mapM fieldNameToString)
      for x in fields do
        if providedFields.contains x.extract then
          throwError "A variant has been defined twice: `{x.extract}`"
        if rustFields.contains x.rust then
          throwError "The Rust variant name `{x.rust}` is used twice"
        if ¬ leanFields.contains x.extract then
          throwError "The user provides a mapping for a variant which is not present in the Lean definition: {x.extract}"
        providedFields := providedFields.insert x.extract x
        rustFields := rustFields.insert x.rust
      /- Go through the fields and either use the user provided information (if there is) or compute the Rust names
         automatically. -/
      let fields : List Field ← List.mapM (fun fieldName => do
        let fieldName ← fieldNameToString fieldName
        match providedFields.get? fieldName with
        | some info => pure info
        | none => pure { rust := fieldName, extract := fieldName }) structInfo.fieldNames.toList
      trace[Extract] "fields: {fields}"
      pure { info with body := .struct fields }
  | .axiomInfo _ =>
    trace[Extract] "Found an axiomatized type"
    pure info
  | .defnInfo _ =>
    trace[Extract] "Found a regular definition: treating it as an axiomatized type"
    pure info
  | _ => throwError "Not a type definition {declName}"

initialize rustTypes : Attribute TypeInfo ← do
  mkAttribute `rustTypesArray `rustType "Register Rust type definitions"
    elabTypeNameInfo processType

/-!
# Trait Declarations
-/

/- Cheating a bit: we elaborate the optional information by using the command config elaborator.
   This allows to have nice syntax for optional fields and at a small cost. -/
declare_command_config_elab elabRustTraitDecl TraitDecl

/-- Declare that a definition models a Rust trait declaration.

The syntax is `rust_trait "NAME_PATTERN" ...`. The name pattern is given by Aeneas when generating
a declaration for a missing definition: one just has to copy-paste it.

The additional options are used to fill the fields of `Aeneas.Extract.TraitDecl`.
The options are:
- `parentClauses`: lists the fields which model clauses coming from "parent" traits. We dub parent traits
  the traits of which the current trait is a super trait. For instance:
  ```
  trait Foo : Bar { ... }
  //          ^^^
  //          parent
  ```
  becomes in Lean:
  ```
  structure Foo (Self : T) where
    barClause : Bar ...
- `consts`, `constsInfo`: describes the constants of the trait.
  We use `consts` to list the fields which represent constants, and `constsInfo` to list those fields
  while providing renaming information (when the constant names in Rust and Lean are not the same).
  The `consts` and `constsInfo` fields should be disjoint.
- `types`, `typesInfo`: similar but for types (note that those shouldn't be used as by default we lift
  the types appearing inside of traits so that they become type parameters).
- `methods`, `methodsInfo`: similar but for methods. Note that **by default**, a field for which the user
  provides no information is considered to be a method.
- `defaultMethods`: lists the methods which have default implementations.
-/
syntax (name := rustTraitDecl) "rust_trait" str Parser.Tactic.optConfig : attr

def elabTraitDeclNameInfo (stx : Syntax) : AttrM (String × TraitDecl) :=
  withRef stx do
    match stx with
    | `(attr| rust_trait $pat $config) => do
      let pat := pat.getString
      if pat = "" then throwError "Not a valid name pattern: {pat}"
      let info ← liftCommandElabM (elabRustTraitDecl config)
      pure (pat, info)
    | _ => Lean.Elab.throwUnsupportedSyntax

/-- This helper completes the information available in the information provided by the user by
    looking at the definition itself. -/
def processTraitDecl (declName : Name) (_pat : String) (info : TraitDecl) : AttrM TraitDecl := do
  trace[Extract] "declName: {declName}"
  let env ← getEnv
  -- Retrieve the extraction name
  let extractName : String ← do
    match info.extract with
    | some name => pure name
    | none =>
      trace[Extract] "Generating the extraction name"
      pure (← (removeNamePrefix declName)).toString
  let info : TraitDecl := { info with extract := extractName }

  /- First, merge the fields `consts`/`constsInfo`, `types`/`typesInfo` and `methods`/`methodsInfo` while
     performing sanity checks -/
  let info : TraitDecl :=
    let constsInfo := info.consts.map (fun x => ⟨ x, x ⟩) ++ info.constsInfo
    let typesInfo := info.types.map (fun x => ⟨ x, x ⟩) ++ info.typesInfo
    let methodsInfo := info.methods.map (fun x => ⟨ x, x ⟩) ++ info.methodsInfo
    { info with consts := [], types := [], methods := [],
                constsInfo, typesInfo, methodsInfo }

  match getStructureInfo? env declName with
  | none =>
    -- Nothing to do
    pure info
  | some structInfo =>
    /- This is a structure: compute the missing informaton about the fields.
       If the user did not provide any information about a field, we consider it is a method by default. -/
    -- First compute maps to lookup the user information
    let userParentClauses := Std.HashSet.ofList info.parentClauses
    let userConsts := Std.HashMap.ofList (info.constsInfo.map (fun x => (x.extract, x)))
    let userTypes := Std.HashMap.ofList (info.typesInfo.map (fun x => (x.extract, x)))
    let userMethods := Std.HashMap.ofList (info.methodsInfo.map (fun x => (x.extract, x)))

    -- Go through all the fields
    let mut parentClauses := #[]
    let mut consts := #[]
    let mut types := #[]
    let mut methods := #[]
    let fields ← structInfo.fieldNames.toList.mapM fieldNameToString
    for field in fields do
      if let some info := userParentClauses.get? field then
        parentClauses := parentClauses.push info
      else if let some info := userConsts.get? field then
        consts := consts.push info
      else if let some info := userTypes.get? field then
        types := types.push info
      else if let some info := userMethods.get? field then
        methods := methods.push info
      else
        methods := methods.push ⟨ field, field ⟩
    pure { info with parentClauses := parentClauses.toList,
                     constsInfo := consts.toList,
                     typesInfo := types.toList,
                     methodsInfo := methods.toList }

initialize rustTraitDecls : Attribute TraitDecl ← do
  mkAttribute `rustTraitDeclsArray `rustTraitDecl "Register Rust trait definitions"
    elabTraitDeclNameInfo processTraitDecl

/-!
# Functions
-/

/- Cheating a bit: we elaborate the optional information by using the command config elaborator.
   This allows to have nice syntax for optional fields and at a small cost. -/
declare_command_config_elab elabRustFunInfo FunInfo

/-- Declare that a definition models a Rust function.

The syntax is `rust_fun "NAME_PATTERN" ...`. The name pattern is given by Aeneas when generating
a declaration for a missing definition: one just has to copy-paste it.

The additional options are used to fill the fields of `Aeneas.Extract.FunInfo`.
The options are:
- `keepParams`: see the comment for the `rust_type` attribute. This allows to indicate that some
  type parameters in Rust are ignored in the Lean model.
- `canFail`: `true` by default, indicates whether the function lives in the `Result` monad or not.
- `lift`: `true` by default, indicates whether the function should be lifted to the `Result` monad
  in the generated code, if the function can not fail (i.e., `canFail = false`).
  If we lift the function, Aeneas generates code like this:
  ```
  let y ← (↑(foo x) : Result ...)
  ...
  ```
-/
syntax (name := rustFun) "rust_fun" str Parser.Tactic.optConfig : attr

def elabFunNameInfo (stx : Syntax) : AttrM (String × FunInfo) :=
  withRef stx do
    match stx with
    | `(attr| rust_fun $pat $config) => do
      let pat := pat.getString
      if pat = "" then throwError "Not a valid name pattern: {pat}"
      let info ← liftCommandElabM (elabRustFunInfo config)
      pure (pat, info)
    | _ => Lean.Elab.throwUnsupportedSyntax

/-- This helper completes the information available in the information provided by the user by
    looking at the definition itself. -/
def processFun (declName : Name) (_pat : String) (info : FunInfo) : AttrM FunInfo := do
  trace[Extract] "declName: {declName}"
  -- Retrieve the extraction name
  let extractName : String ← do
    match info.extract with
    | some name => pure name
    | none =>
      trace[Extract] "Generating the extraction name"
      pure (← (removeNamePrefix declName)).toString
  --
  pure { info with extract := extractName }

initialize rustFuns : Attribute FunInfo ← do
  mkAttribute `rustFunsArray `rustFun "Register Rust Fun definitions"
    elabFunNameInfo processFun

/-!
# Trait Impls
-/

/- Cheating a bit: we elaborate the optional information by using the command config elaborator.
   This allows to have nice syntax for optional fields and at a small cost. -/
declare_command_config_elab elabRustTraitImplInfo TraitImpl

/-- Declare that a definition models a Rust trait implementation.

The syntax is `rust_trait_impl "NAME_PATTERN" ...`. The name pattern is given by Aeneas when generating
a declaration for a missing definition: one just has to copy-paste it.

The additional options are used to fill the fields of `Aeneas.Extract.TraitImpl`.
The options are:
- `keepParams`: see the comment for the `rust_type` attribute. This allows to indicate that some
  type parameters in Rust are ignored in the Lean model.
-/
syntax (name := rustTraitImpl) "rust_trait_impl" str Parser.Tactic.optConfig : attr

def elabTraitImplNameInfo (stx : Syntax) : AttrM (String × TraitImpl) :=
  withRef stx do
    match stx with
    | `(attr| rust_trait_impl $pat $config) => do
      let pat := pat.getString
      if pat = "" then throwError "Not a valid name pattern: {pat}"
      let info ← liftCommandElabM (elabRustTraitImplInfo config)
      pure (pat, info)
    | _ => Lean.Elab.throwUnsupportedSyntax

/-- This helper completes the information available in the information provided by the user by
    looking at the definition itself. -/
def processTraitImpl (declName : Name) (_pat : String) (info : TraitImpl) : AttrM TraitImpl := do
  trace[Extract] "declName: {declName}"
  -- Retrieve the extraction name
  let extract : String ← do
    match info.extract with
    | some name => pure name
    | none =>
      trace[Extract] "Generating the extraction name"
      pure (← (removeNamePrefix declName)).toString
  --
  pure { info with extract }

initialize rustTraitImpls : Attribute TraitImpl ← do
  mkAttribute `rustTraitImplsArray `rustTraitImpl "Register Rust TraitImpl definitions"
    elabTraitImplNameInfo processTraitImpl

/-!
# Consts
-/

/- Cheating a bit: we elaborate the optional information by using the command config elaborator.
   This allows to have nice syntax for optional fields and at a small cost. -/
declare_command_config_elab elabRustConstInfo ConstInfo

/-- Declare that a definition models a Rust top-level const.

The syntax is `rust_const "NAME_PATTERN"`. The name pattern is given by Aeneas when generating
a declaration for a missing definition: one just has to copy-paste it.
-/
syntax (name := rustConst) "rust_const" str Parser.Tactic.optConfig : attr

def elabConstNameInfo (stx : Syntax) : AttrM (String × ConstInfo) :=
  withRef stx do
    match stx with
    | `(attr| rust_trait_impl $pat $config) => do
      let pat := pat.getString
      if pat = "" then throwError "Not a valid name pattern: {pat}"
      let info ← liftCommandElabM (elabRustConstInfo config)
      pure (pat, info)
    | _ => Lean.Elab.throwUnsupportedSyntax

/-- This helper completes the information available in the information provided by the user by
    looking at the definition itself. -/
def processConst (declName : Name) (_pat : String) (info : ConstInfo) : AttrM ConstInfo := do
  trace[Extract] "declName: {declName}"
  -- Retrieve the extraction name
  let extract : String ← do
    match info.extract with
    | some name => pure name
    | none =>
      trace[Extract] "Generating the extraction name"
      pure (← (removeNamePrefix declName)).toString
  --
  pure { info with extract }

initialize rustConsts : Attribute ConstInfo ← do
  mkAttribute `rustConstsArray `rustConst "Register Rust top-level const definitions"
    elabConstNameInfo processConst

/-!
# Code Generation
-/

def listToString {α} [ToString α] (ls : List α) : String := Id.run do
  let mut s := "["
  let mut first := true
  for e in ls do
    if ¬ first then s := s ++ "; "
    first := false
    s := s ++ toString e
  pure (s ++ "]")

def optionToString {α} [ToString α] (x : Option α) : String :=
  match x with
  | none => "None"
  | some x => "Some " ++ toString x

def addQuotes (x : String) : String := "\"" ++ x ++ "\""

def TypeInfo.toExtract (info : TypeInfo) : MessageData :=
  let extract := info.extract.getD "ERROR_MISSING_FIELD"
  let extract := m!"\"{extract}\""
  let keepParams :=
    match info.keepParams with
    | none => m!""
    | some keepParams => m!" ~keep_params:{listToString keepParams}"
  let prefixVariantNames :=
    if info.prefixVariantNames then m!"" else m!" ~prefix_variant_names:false"
  let body :=
    match info.body with
    | .opaque => m!""
    | .enum variants =>
      m!" ~kind:(KEnum {listToString (variants.map (fun ⟨ x, y, _ ⟩ => (addQuotes x, "Some " ++ addQuotes (toString y))))})"
    | .struct fields =>
      m!" ~kind:(KStruct {listToString (fields.map (fun ⟨ x, y ⟩ => (addQuotes x, "Some " ++ addQuotes (toString y))))})"
  m!"{extract}{keepParams}{prefixVariantNames}{body}"

def ConstInfo.toExtract (info : ConstInfo) : MessageData :=
  let extract := info.extract.getD "ERROR_MISSING_FIELD"
  m!"\"{extract}\""

def FunInfo.toExtract (info : FunInfo) : MessageData :=
  let extract := info.extract.getD "ERROR_MISSING_FIELD"
  let extract := m!"\"{extract}\""
  let keepParams :=
    match info.keepParams with
    | none => m!""
    | some filter => m!" ~filter:(Some {listToString filter})"
  let canFail := if ¬ info.canFail then m!" ~can_fail:{info.canFail}" else m!""
  let lift := if ¬ info.lift then m!" ~lift:{info.lift}" else m!""
  let hasDefault := if info.hasDefault then m!" ~lift:{info.hasDefault}" else m!""
  m!"{extract}{keepParams}{canFail}{lift}{hasDefault}"

def TraitDecl.toExtract (info : TraitDecl) : MessageData :=
  let extract := info.extract.getD "ERROR_MISSING_FIELD"
  let extract := m!"\"{extract}\""
  let parentClauses :=
    match info.parentClauses with
    | [] => m!""
    | _ => m!" ~parent_clauses:{listToString (info.parentClauses.map addQuotes)}"
  let types :=
    match info.typesInfo with
    | [] => m!""
    | _ => m!" ~types:{listToString (info.typesInfo.map (fun (x : TraitType) => (addQuotes x.rust, addQuotes x.extract)))}"
  let consts :=
    match info.constsInfo with
    | [] => m!""
    | _ => m!" ~consts:{listToString (info.constsInfo.map (fun (x : TraitConst) => (addQuotes x.rust, addQuotes x.extract)))}"
  let methods :=
    match info.methodsInfo with
    | [] => m!""
    | _ => m!" ~methods:{listToString (info.methodsInfo.map (fun (x : TraitMethod) => (addQuotes x.rust, addQuotes x.extract)))}"
  let defaultMethods :=
    match info.defaultMethods with
    | [] => m!""
    | _ => m!" ~default_methods:{listToString (info.defaultMethods.map addQuotes)}"
  m!"{extract}{parentClauses}{types}{consts}{methods}{defaultMethods}"

def TraitImpl.toExtract (info : TraitImpl) : MessageData :=
  let extract := info.extract.getD "ERROR_MISSING_FIELD"
  let extract := m!"\"{extract}\""
  let keepParams :=
    match info.keepParams with
    | none => m!""
    | some filter => m!" ~filter_params:(Some {listToString filter})"
  m!"{extract}{keepParams}"

def sortDescriptors {α} [ToMessageData α] (st : Array (String × Span × α)) : IO (Array (String × Span × α)) := do
  let mut map : RBMap String (Span × α) Ord.compare := RBMap.empty
  for (pat, span, info) in st do
    match map.find? pat with
    | some (span', info') =>
      let msg := m!"Found two descriptors for the same name pattern `{pat}`:\
        \n- info1: {info}\
        \n- span1: file: {span.fileName}, line: {toString span.pos.line}\
        \n- info2: {info'}\
        \n- span2: file: {span'.fileName}, line: {toString span'.pos.line}"
      let msg ← msg.toString
      println! "Error: {msg}"
      throw (IO.userError msg)
    | none =>
      map := map.insert pat (span, info)
  pure map.toArray

/-- Helper to print the content of the descriptors -/
def write (env : Environment) (printLn : String → IO Unit) : IO Unit := do
  -- # Header
  printLn "(** THIS FILE WAS AUTOMATICALLY GENERATED FROM LEAN: DO NOT MODIFY DIRECTLY *)"
  printLn "open ExtractBuiltinCore"
  printLn ""
  -- # Types
  -- Retrieve the types, sort them by pattern and export
  let infos ← sortDescriptors (rustTypes.ext.getState env)
  printLn "let lean_builtin_types = ["
  let printSpan (span : Span) : IO Unit :=
    printLn ("  (* file: \"" ++ span.fileName ++ "\", line: " ++ toString span.pos.line ++ " *)")
  for (pat, span, info) in infos do
    printSpan span
    let msg ← m!"  mk_type \"{pat}\" {info.toExtract};".toString
    printLn msg
  printLn "]"
  printLn ""
  -- # Consts
  let infos ← sortDescriptors (rustConsts.ext.getState env)
  printLn "let lean_builtin_consts = ["
  for (pat, span, info) in infos do
    printSpan span
    let msg ← m!"  mk_trait_impl \"{pat}\" {info.toExtract};".toString
    printLn msg
  printLn "]"
  printLn ""
  -- # Funs
  let infos ← sortDescriptors (rustFuns.ext.getState env)
  printLn "let lean_builtin_funs = ["
  for (pat, span, info) in infos do
    printSpan span
    let msg ← m!"  mk_fun \"{pat}\" {info.toExtract};".toString
    printLn msg
  printLn "]"
  printLn ""
  -- # Trait Decls
  let infos ← sortDescriptors (rustTraitDecls.ext.getState env)
  printLn "let lean_builtin_trait_decls = ["
  for (pat, span, info) in infos do
    printSpan span
    let msg ← m!"  mk_trait_decl \"{pat}\" {info.toExtract};".toString
    printLn msg
  printLn "]"
  printLn ""
  -- # Trait Impls
  let infos ← sortDescriptors (rustTraitImpls.ext.getState env)
  printLn "let lean_builtin_trait_impls = ["
  for (pat, span, info) in infos do
    printSpan span
    let msg ← m!"  mk_trait_impl \"{pat}\" {info.toExtract};".toString
    printLn msg
  printLn "]"
  printLn ""

/-- Print the content of the descriptors -/
def print : MetaM Unit := do
  -- Import the environment
  let env ← getEnv
  -- Print
  write env IO.println

/-- Export the extraction information to an OCaml file -/
def writeToFile (moduleName : Name) (filename : System.FilePath) : IO Unit := do
  -- Import the environment
  let env ← Lean.importModules #[{ module := moduleName }] {} 0 (loadExts := true)
  -- Open the file
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  -- Write to the file
  write env handle.putStrLn
  -- Close the file
  handle.flush

end Aeneas.Extract
