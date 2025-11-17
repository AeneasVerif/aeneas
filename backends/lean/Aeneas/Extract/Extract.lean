import AeneasMeta.Extensions
/-! Helpers to provide informations about the models for the Rust standard library -/

open Lean

namespace Aeneas.Extract

initialize registerTraceClass `Extract

structure Field where
  rust : Option String := none
  extract : String
deriving Repr, Inhabited

instance : ToMessageData Field where
  toMessageData x := m!"\{ rust : {x.rust}, extract : {x.extract} }"

structure Variant where
  -- Name of the variant, in Rust
  rust : Option String := none
  -- Name of the variant, once extracted
  extract : String
  -- Names of the fields
  fields : Option (List String) := none
deriving Repr, Inhabited, BEq

instance : ToMessageData Variant where
  toMessageData x := m!"\{ rust : {x.rust}, extract : {x.extract}, fields: {x.fields} }"

inductive TypeBody where
-- The constructor name and the map for the field names
| struct (fieldNames : List Field)
-- For every variant, a map for the field names
| enum (variants : List Variant)
deriving Repr, Inhabited

instance : ToMessageData TypeBody where
  toMessageData x :=
    match x with
    | .struct fields => m!"Struct ({fields})"
    | .enum variants => m!"Enum ({variants})"

structure TypeInfo where
  /- The name pattern which uniquely identifies the function in Rust -/
  rust : Option String := none
  extract : Option String := none
  /-- We might want to filter some of the type parameters.

      For instance, `Vec` type takes a type parameter for the allocator,
      which we want to ignore. -/
  keepParams : Option (List Bool) := none
  body : Option TypeBody := none
deriving Repr, Inhabited

instance : ToMessageData TypeInfo where
  toMessageData x :=
    m!"\{ rust : {x.rust},\n  extract : {x.extract},\n  keepParams : {x.keepParams},\n  body : {x.body} }"

structure GlobalInfo where
  extract : Option String := none
deriving Repr, Inhabited

structure FunInfo where
  extract : String
  /-- We might want to filter some of the function parameters, for instance
      the `Allocator` parameter, which we actually don't use. -/
  filterParams : Option (List Bool) := none
  canFail : Bool := true
  /-- If the function can not fail, should we still lift it to the [Result]
      monad? This can make reasonings easier, as we can then use [progress]
      to do proofs in a Hoare-Logic style, rather than equational reasonings. -/
  lift : Bool := true
  /-- If this is a trait method: does this method have a default
      implementation? If yes, we might want to register it as well. -/
  hasDefault : Bool := false
deriving Repr, Inhabited

structure TraitConst where
  rust : Option String := none
  extract : Option String := none
deriving Repr, Inhabited

structure TraitType where
  rust : Option String := none
  extract : Option String := none
deriving Repr, Inhabited

structure TraitMethod where
  rust : Option String := none
  info : Option FunInfo := none
deriving Repr, Inhabited

structure TraitDeclInfo where
  extract : Option String := none
  constructor : Option String := none
  parentClauses : List String := []
  -- Every const has: a Rust name, an extraction name
  consts : List TraitConst := []
  -- Every type has: a Rust name, an extraction name
  types : List TraitType := []
  -- Every method has: a Rust name, information
  methods : List (String × FunInfo) := []
deriving Repr, Inhabited

structure RustTraitImplInfo where
  extractName : Option String
  filterInfo : Option (List Bool)
deriving Repr, Inhabited

def mkExtension (α : Type) (name : Name := by exact decl_name%) :
  IO (SimpleScopedEnvExtension α (Array α)) :=
  registerSimpleScopedEnvExtension {
    name        := name,
    initial     := #[],
    addEntry    := Array.push,
  }

structure Attribute (α : Type) where
  ext : SimpleScopedEnvExtension α (Array α)
  attr : AttributeImpl
deriving Inhabited

def mkAttribute {α} (extName : Name)
  (attrName : Name) -- this has to be the same name as the syntax
  (descr : String) (elabInfo : Syntax → AttrM α)
  (processDecl : Name → α → AttrM α)
   : IO (Attribute α) := do
  let ext ← mkExtension α extName
  let attr : AttributeImpl := {
    name := attrName
    descr
    add := fun declName stx attrKind => do
      let info ← elabInfo stx
      let info ← processDecl declName info
      ScopedEnvExtension.add ext info attrKind
  }
  registerBuiltinAttribute attr
  pure { ext, attr }

-- Small helper: remove the prefix `Aeneas.Std` from a name
def removeNamePrefix (n0 : Name) : AttrM Name := do
  let rec remove (n : Name) := do
    match n with
    | .str (.str .anonymous "Aeneas") "Std" => pure .anonymous
    | .str pre str => pure (.str (← remove pre) str)
    | _ => throwError "Ill-formed name: `{n0}` (the name should start with `Aeneas.Std.`)"
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
  | .str pre field =>
    if pre ≠ declName then throwError "Ill-formed variant name: `{n}`"
    pure field
  | _ => throwError "Ill-formed field name: `{n}`"

/-!
# Types
-/

/- Cheating a bit: we elaborate the optional information by using the command config elaborator.
   This allows to have nice syntax for optional fields and at a small cost. -/
declare_command_config_elab elabRustTypeInfo TypeInfo

syntax (name := rustType) "rust_type" Parser.Tactic.optConfig : attr

def elabTypeNameInfo (stx : Syntax) : AttrM TypeInfo :=
  withRef stx do
    match stx with
    | `(attr| rust_type $config) => do
      let info ← liftCommandElabM (elabRustTypeInfo config)
      pure info
    | _ => Lean.Elab.throwUnsupportedSyntax

/-- This helper completes the information available in the information provided by the user by
    looking at the definition itself. -/
def processType (declName : Name) (info : TypeInfo) : AttrM TypeInfo := do
  trace[Extract] "declName: {declName}"
  let env ← getEnv
  let some decl := env.findAsync? declName
      | throwError "Could not find theorem {declName}"
  let const ← do match decl.constInfo.get with
      | .inductInfo info => pure info
      | _ => throwError "Not a type definition {declName}"
  -- Retrieve the extraction name
  let extractName : String ← do
    match info.extract with
    | some name => pure name
    | none =>
      trace[Extract] "Generating the Rust name"
      pure (← (removeNamePrefix declName)).toString
  /- Compute the pattern, if it was not provided (we use the extraction name, that we
     convert to a Rust name without parameters) -/
  let rustPattern : String ← do
    match info.rust with
    | some pat => pure pat
    | none =>
      -- Use the Lean name
      trace[Extract] "Generating the extraction name"
      pure (← leanNameToRust (← (removeNamePrefix declName)))
  --
  let info : TypeInfo := { info with extract := extractName, rust := rustPattern }

  /- Compute the information about the variants/fields -/
  let structInfo := getStructureInfo? env declName
  match structInfo with
  | none =>
    trace[Extract] "The type definition is for an enumeration"
    let variants ← do
      match info.body with
      | .some (.enum variants) => pure variants
      | .none => pure []
      | .some (.struct _) => throwError "The user-provided information is for a structure while the type is an inductive"
    -- Go through the variants and retrieve their names
    let providedVariants := Std.HashMap.ofList (List.map (fun x => (x.extract, x)) variants)
    let variants : List Variant ← List.mapM (fun ctorName => do
      let ctorName ← variantNameToString declName ctorName
      match providedVariants.get? ctorName with
      | some info =>
        let rust := info.rust.getD info.extract
        pure { info with rust }
      | none => pure { rust := some ctorName, extract := ctorName }) const.ctors
    trace[Extract] "variants: {variants}"
    pure { info with body := some (.enum variants) }
  | some structInfo =>
    trace[Extract] "The type definition is for a structure"
    let fields ← do
      match info.body with
      | .some (.struct fields) => pure fields
      | .none => pure []
      | .some (.enum _) => throwError "The user-provided information is for a variant while the type is a structure"
    let providedFields := Std.HashMap.ofList (List.map (fun x => (x.extract, x)) fields)
    -- Go through the fields and retrieve their names
    let fields : List Field ← List.mapM (fun fieldName => do
      let fieldName ← fieldNameToString fieldName
      match providedFields.get? fieldName with
      | some info =>
        let rust := info.rust.getD info.extract.capitalize
        pure { info with rust }
      | none => pure { rust := some fieldName, extract := fieldName }) structInfo.fieldNames.toList
    trace[Extract] "fields: {fields}"
    pure { info with body := some (.struct fields) }

initialize rustTypes : Attribute TypeInfo ← do
  mkAttribute `rustTypesArray `rustType "Register Rust type definitions"
    elabTypeNameInfo processType

end Aeneas.Extract
