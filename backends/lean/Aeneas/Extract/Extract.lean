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
deriving Repr, Inhabited

instance : ToMessageData TypeBody where
  toMessageData x :=
    match x with
    | .struct fields => m!"Struct ({fields})"
    | .enum variants => m!"Enum ({variants})"

structure TypeInfo where
  /-- The name to use for extraction -/
  extract : Option String := none
  /-- We might want to filter some of the type parameters.

      For instance, `Vec` type takes a type parameter for the allocator,
      which we want to ignore. -/
  keepParams : Option (List Bool) := none
  body : Option TypeBody := none
deriving Repr, Inhabited

instance : ToMessageData TypeInfo where
  toMessageData x :=
    m!"\{ extract : {x.extract},\n  keepParams : {x.keepParams},\n  body : {x.body} }"

structure GlobalInfo where
  extract : Option String := none
deriving Repr, Inhabited

instance : ToMessageData GlobalInfo where
  toMessageData x :=
    m!"\{ extract : {x.extract} }"

structure FunInfo where
  /-- The name to use for the extraction -/
  extract : Option String := none
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

instance : ToMessageData FunInfo where
  toMessageData x :=
    m!"\{ extract : {x.extract},\n  filterParams : {x.filterParams},\n  canFail : {x.canFail},\n  lift : {x.lift},\n  hasDefault : {x.hasDefault} }"

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
  IO (SimpleScopedEnvExtension (String × α) (Array (String × α))) :=
  registerSimpleScopedEnvExtension {
    name        := name,
    initial     := #[],
    addEntry    := Array.push,
  }

structure Attribute (α : Type) where
  ext : SimpleScopedEnvExtension (String × α) (Array (String × α))
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
      let info ← processDecl declName pat info
      ScopedEnvExtension.add ext (pat, info) attrKind
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
        | .some (.enum variants) => pure variants
        | .none => pure []
        | .some (.struct _) => throwError "The user-provided information is for a structure while the type is an inductive"
      -- Go through the variants and retrieve their names
      let providedVariants := Std.HashMap.ofList (List.map (fun x => (x.extract, x)) variants)
      let variants : List Variant ← List.mapM (fun ctorName => do
        let ctorName ← variantNameToString declName ctorName
        match providedVariants.get? ctorName with
        | some info => pure info
        | none => pure { rust := ctorName, extract := ctorName }) const.ctors
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
        | some info => pure info
        | none => pure { rust := fieldName, extract := fieldName }) structInfo.fieldNames.toList
      trace[Extract] "fields: {fields}"
      pure { info with body := some (.struct fields) }
    pure info
  | .axiomInfo _ =>
    trace[Extract] "Found an axiomatized type"
    pure info
  | _ => throwError "Not a type definition {declName}"

initialize rustTypes : Attribute TypeInfo ← do
  mkAttribute `rustTypesArray `rustType "Register Rust type definitions"
    elabTypeNameInfo processType

/-!
# Functions
-/

/- Cheating a bit: we elaborate the optional information by using the command config elaborator.
   This allows to have nice syntax for optional fields and at a small cost. -/
declare_command_config_elab elabRustFunInfo FunInfo

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
# Code Generation
-/

def TypeInfo.toExtract (info : TypeInfo) : MessageData :=
  let extract := info.extract.getD "ERROR_MISSING_FIELD"
  let extract := m!"\"{extract}\""
  let keepParams :=
    match info.keepParams with
    | none => m!""
    | some keepParams => m!" ~keep_params:{keepParams}"
  let body :=
    match info.body with
    | none => m!""
    | some body =>
      match body with
      | .enum variants => m!" ~kind:{variants.map (fun ⟨ x, y, _ ⟩ => (x, some y))}"
      | .struct fields => m!" ~kind:{fields.map (fun ⟨ x, y ⟩ => (x, some y))}"
  m!"{extract}{keepParams}{body}"

def boolToString (x : Bool) : String :=
  if x then "true" else "false"

def FunInfo.toExtract (info : FunInfo) : MessageData :=
  let extract := info.extract.getD "ERROR_MISSING_FIELD"
  let extract := m!"\"{extract}\""
  let filterParams :=
    match info.filterParams with
    | none => m!""
    | some filter => m!" ~filter:{filter}"
  let canFail := if ¬ info.canFail then m!" ~can_fail:{boolToString info.canFail}" else m!""
  let lift := if ¬ info.lift then m!" ~lift:{boolToString info.lift}" else m!""
  let hasDefault := if info.hasDefault then m!" ~lift:{boolToString info.hasDefault}" else m!""
  m!"{extract}{filterParams}{canFail}{lift}{hasDefault}"

def sortDescriptors {α} [ToMessageData α] (st : Array (String × α)) : IO (Array (String × α)) := do
  let mut map : RBMap String α Ord.compare := RBMap.empty
  for (pat, info) in st do
    match map.find? pat with
    | some info' =>
      let msg := m!"Found two descriptors for the same name pattern `{pat}`:\n- info1: {info}\n- info2: {info'}"
      let msg ← msg.toString
      println! "Error: {msg}"
      throw (IO.userError msg)
    | none =>
      map := map.insert pat info
  pure map.toArray

/-- Export the extraction information to an OCaml file -/
def writeToFile (moduleName : Name) (filename : System.FilePath) : IO Unit := do
  -- Import the environment
  let env ← Lean.importModules #[{ module := moduleName }] {} 0 (loadExts := true)
  -- Open the file
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  -- # Header
  handle.putStrLn "(** THIS FILE WAS AUTOMATICALLY GENERATED FROM LEAN: DO NOT MODIFY DIRECTLY *)"
  handle.putStrLn "open ExtractBuiltinCore"
  handle.putStrLn ""
  -- # Types
  -- Retrieve the types, sort them by pattern and export
  let infos ← sortDescriptors (rustTypes.ext.getState env)
  handle.putStrLn "let lean_builtin_types = ["
  for (pat, info) in infos do
    let msg ← m!"  mk_type \"{pat}\" {info.toExtract};".toString
    handle.putStrLn msg
  handle.putStrLn "]"
  handle.putStrLn ""
  -- # Funs
  let infos ← sortDescriptors (rustFuns.ext.getState env)
  handle.putStrLn "let lean_builtin_funs = ["
  for (pat, info) in infos do
    let msg ← m!"  mk_fun \"{pat}\" {info.toExtract};".toString
    handle.putStrLn msg
  handle.putStrLn "]"
  handle.putStrLn ""
  handle.flush
  pure ()

end Aeneas.Extract
