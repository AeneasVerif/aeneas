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

def getLocalFileName : AttrM (Option String) := do
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
  if found
  then pure (some (List.foldl (fun s0 s1 => s0 ++ "/" ++ s1) "Aeneas" out))
  else pure none

structure Span where
  fileName : String
  pos : Position
deriving Inhabited

/- Remark: we retrieve the span of some syntax, rather than a definition (by using `findDeclarationRange?`)
   because when processing the attribute the range is not saved in the environment yet.

   TODO: how to retrieve the file in which a definition was defined?
   For now I can only retrieve the name of the current file and the code of `Lean/Server/Goto.lean`
   does quite a few things (in particular, does it work in non-interactive mode?). -/
def getLocalSyntaxSpan (stx : Syntax) : AttrM (Option Span) := do
  let some fileName ← getLocalFileName
    | trace[Extract] "Could not compute the local file name"; return none
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
        | none => pure { rust := ctorName, extract := ctorName }) const.ctors
      trace[Extract] "variants: {variants}"
      pure { info with body := some (.enum variants) }
    | some structInfo =>
      trace[Extract] "The type definition is for a structure"
      /- Similar to the inductive case: we check the user-provided information before using it, for instance
         to detect name collisions. -/
      let fields ← do
        match info.body with
        | .some (.struct fields) => pure fields
        | .none => pure []
        | .some (.enum _) => throwError "The user-provided information is for a variant while the type is a structure"
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
      pure { info with body := some (.struct fields) }
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
  let body :=
    match info.body with
    | none => m!""
    | some body =>
      match body with
      | .enum variants =>
        m!" ~kind:(KEnum {listToString (variants.map (fun ⟨ x, y, _ ⟩ => (addQuotes x, "Some " ++ addQuotes (toString y))))})"
      | .struct fields =>
        m!" ~kind:(KStruct {listToString (fields.map (fun ⟨ x, y ⟩ => (addQuotes x, "Some " ++ addQuotes (toString y))))})"
  m!"{extract}{keepParams}{body}"

def FunInfo.toExtract (info : FunInfo) : MessageData :=
  let extract := info.extract.getD "ERROR_MISSING_FIELD"
  let extract := m!"\"{extract}\""
  let filterParams :=
    match info.filterParams with
    | none => m!""
    | some filter => m!" ~filter:(Some {listToString filter})"
  let canFail := if ¬ info.canFail then m!" ~can_fail:{info.canFail}" else m!""
  let lift := if ¬ info.lift then m!" ~lift:{info.lift}" else m!""
  let hasDefault := if info.hasDefault then m!" ~lift:{info.hasDefault}" else m!""
  m!"{extract}{filterParams}{canFail}{lift}{hasDefault}"

def sortDescriptors {α} [ToMessageData α] (st : Array (String × Span × α)) : IO (Array (String × Span × α)) := do
  let mut map : RBMap String (Span × α) Ord.compare := RBMap.empty
  for (pat, span, info) in st do
    match map.find? pat with
    | some (_, info') =>
      let msg := m!"Found two descriptors for the same name pattern `{pat}`:\n- info1: {info}\n- info2: {info'}"
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
  -- # Funs
  let infos ← sortDescriptors (rustFuns.ext.getState env)
  printLn "let lean_builtin_funs = ["
  for (pat, span, info) in infos do
    printSpan span
    let msg ← m!"  mk_fun \"{pat}\" {info.toExtract};".toString
    printLn msg
  printLn "]"
  printLn ""

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

/-- Print the content of the descriptors -/
def print : MetaM Unit := do
  -- Import the environment
  let env ← getEnv
  -- Print
  write env IO.println

end Aeneas.Extract
