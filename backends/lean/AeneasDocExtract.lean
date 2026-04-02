/-
  AeneasDocExtract — Extract verification documentation metadata as JSON.

  This executable loads a Lean project's environment and outputs a JSON file
  containing:
  - All @[step] theorems with their function mappings
  - Sorry status (verified / specified / partially verified)
  - Pretty-printed theorem statements
  - All definitions (functions, types) from the target module with metadata

  Usage:
    lake env lean --run AeneasDocExtract.lean <ModuleName> <output.json>

  Example:
    lake env lean --run AeneasDocExtract.lean SymCrust.Properties /tmp/lean-doc.json
-/
import Aeneas

open Lean Aeneas Step Meta Widget Elab PrettyPrinter

/-- Metadata about a step theorem, extracted for documentation. -/
private structure TheoremInfo where
  funName    : Name
  thmName    : Name
  kind       : String  -- "theorem" or "axiom"
  isPrivate  : Bool
  sorryStatus : String
  ppType     : String
  annotated  : Array Json
  specBinders : Array Json     -- [{name, type, annotated_type}, ...]
  specBodyText : String
  annotatedSpecBody : Array Json
  leanSource : Option Json     -- {begin_line, begin_col, end_line, end_col}
  moduleName : Option Name     -- Lean module containing this theorem

/-- Extract the head function name from an expression `f x1 ... xn`.
    Also handles `lift (f x1 ... xn)` by unwrapping the lift.
    Note: `Std.lift` has signature `{α : Type} → α → Result α`,
    so the actual value is the second argument (index 1). -/
private def getFunName? (e : Expr) : Option Name :=
  let fn := e.getAppFn
  match fn.constName? with
  | some n =>
    if n == ``Std.lift then
      -- Unwrap: `@Std.lift α (f x1 ... xn)` → look at arg[1] (the value, not the type)
      let args := e.getAppArgs
      args[1]?.bind (·.getAppFn.constName?)
    else
      some n
  | none => none

/-- Try to extract the function name from a spec-shaped type.
    Returns `some funName` if the type is `∀ xs, spec (f x1 ... xn) P`. -/
private def extractSpecFunName? (type : Expr) : MetaM (Option Name) := do
  try
    let ty ← Utils.normalizeLetBindings type
    let fExpr ← getStepSpecFunArgsExpr ty
    return getFunName? fExpr
  catch e =>
    IO.eprintln s!"  Warning: failed to extract function name from spec: {← e.toMessageData.toString}"
    return none

/-- Classify sorry status:
    - "verified": no `sorryAx` in the proof's axiom closure
    - "specified": the theorem's value *is* `sorryAx` (proof := sorry)
    - "partially_verified": uses `sorryAx` but isn't directly sorry -/
private def classifySorryStatus (constName : Name) : CoreM String := do
  let env ← getEnv
  -- Axioms have no proof body; classify as "verified" (axiomatized)
  match env.find? constName with
  | some (.axiomInfo _) => return "verified"
  | _ => pure ()
  let axioms ← Lean.collectAxioms constName
  if !axioms.contains ``sorryAx then
    return "verified"
  else
    match env.find? constName with
    | some (.thmInfo val) =>
      if val.value.isAppOf ``sorryAx then return "specified"
      else return "partially_verified"
    | some (.defnInfo val) =>
      if val.value.isAppOf ``sorryAx then return "specified"
      else return "partially_verified"
    | _ => return "partially_verified"

/-- Resolve a constant name from an Info node if it references a constant.
    Only matches direct constants (not applications like `f x y`). -/
private def resolveConstNameFromInfo (info : Info) : Option Name :=
  match info with
  | .ofTermInfo ti => ti.expr.constName?
  | .ofDelabTermInfo dti => dti.expr.constName?
  | _ => none

/-- Extract a constant name from an application's head function. -/
private def resolveAppFnName (info : Info) : Option Name :=
  match info with
  | .ofTermInfo ti => ti.expr.getAppFn.constName?
  | .ofDelabTermInfo dti => dti.expr.getAppFn.constName?
  | _ => none

/-- Filter out noisy identifiers that render as notation (↑, +, ≤, etc.)
    and don't benefit from being clickable links. -/
private def isUsefulIdent (n : Name) : Bool :=
  -- Skip typeclass infrastructure / notation
  !(`OfNat.ofNat).isPrefixOf n &&
  !(`HAdd).isPrefixOf n &&
  !(`HSub).isPrefixOf n &&
  !(`HMul).isPrefixOf n &&
  !(`HMod).isPrefixOf n &&
  !(`HDiv).isPrefixOf n &&
  !(`HPow).isPrefixOf n &&
  !(`LE).isPrefixOf n &&
  !(`LT).isPrefixOf n &&
  !(`GE).isPrefixOf n &&
  !(`GT).isPrefixOf n &&
  !(`Eq).isPrefixOf n &&
  !(`And).isPrefixOf n &&
  !(`Or).isPrefixOf n &&
  !(`Not).isPrefixOf n &&
  !(`Inhabited).isPrefixOf n &&
  -- Skip coercion functions (render as ↑)
  n != `Aeneas.Std.UScalar.val &&
  n != `Aeneas.Std.IScalar.val

/-- Build a JSON ident node, adding "constructor_of" if the constant is a type constructor. -/
private def mkIdentJson (env : Environment) (constName : Name) (children : Array Json) : Json :=
  let baseFields : List (String × Json) := [
    ("ident", .str constName.toString),
    ("children", .arr children)
  ]
  -- If this is a constructor, record the parent inductive type
  match env.find? constName with
  | some (.ctorInfo _) =>
    let parentName := constName.getPrefix
    Json.mkObj (baseFields ++ [("constructor_of", .str parentName.toString)])
  | _ => Json.mkObj baseFields

/-- Walk a TaggedText tree and produce a JSON array of text/ident fragments.
    Text nodes: `"string"`, Identifier nodes: `{"ident": "Foo.bar", "children": [...]}`.
    Constructor identifiers additionally carry `"constructor_of": "ParentType"`. -/
private partial def taggedTextToJson (env : Environment) (infos : InfoPerPos)
    (node : TaggedText (Nat × Nat)) : IO (Array Json) := do
  match node with
  | .text s => return #[.str s]
  | .append parts =>
    let mut arr : Array Json := #[]
    for p in parts do
      arr := arr ++ (← taggedTextToJson env infos p)
    return arr
  | .tag (tagId, _) inner =>
    match infos.get? tagId with
    | some info =>
      -- Direct constant reference (e.g., U32, U32.max)
      match resolveConstNameFromInfo info with
      | some constName =>
        if isUsefulIdent constName then
          let children ← taggedTextToJson env infos inner
          return #[mkIdentJson env constName children]
        else
          taggedTextToJson env infos inner
      | none =>
        -- Application: the tag wraps `f x y` as an APPEND.
        -- The head function name is the leading text. Tag just that text,
        -- and recurse normally for arguments.
        match resolveAppFnName info with
        | some constName =>
          if isUsefulIdent constName then
            taggedAppToJson env infos constName inner
          else
            taggedTextToJson env infos inner
        | none => taggedTextToJson env infos inner
    | none => taggedTextToJson env infos inner
where
  /-- For an application tag wrapping `f x₁ ... xₙ`, find the leading text
      (the function name) and make it clickable, then recurse for the rest. -/
  taggedAppToJson (env : Environment) (infos : InfoPerPos) (fnName : Name)
      (inner : TaggedText (Nat × Nat)) : IO (Array Json) := do
    match inner with
    | .text s =>
      return #[mkIdentJson env fnName #[Json.str s]]
    | .append parts =>
      let mut result : Array Json := #[]
      let mut foundFirst := false
      for p in parts do
        if !foundFirst then
          match p with
          | .text s =>
            result := result.push (mkIdentJson env fnName #[Json.str s])
            foundFirst := true
          | _ =>
            result := result ++ (← taggedTextToJson env infos p)
            foundFirst := true
        else
          result := result ++ (← taggedTextToJson env infos p)
      return result
    | .tag _ _ =>
      taggedTextToJson env infos inner

/-- Pretty-print an expression with identifier annotations.
    Returns (plainText, annotatedJsonArray).
    Caller must ensure the Aeneas scoped namespaces are already activated. -/
private def ppExprAnnotated (e : Expr) : MetaM (String × Array Json) := do
  let env ← getEnv
  try
    let fwi ← Meta.ppExprWithInfos e
    let plainText := toString fwi.fmt
    let tt := TaggedText.prettyTagged fwi.fmt
    let annotated ← taggedTextToJson env fwi.infos tt
    return (plainText, annotated)
  catch _ =>
    -- Fallback: plain pretty-print without annotations
    try
      let fmt ← Meta.ppExpr e
      return (toString fmt, #[])
    catch _ =>
      return (toString e, #[])

/-- Plain pretty-print without annotations (fallback). -/
private def ppExprPlain (e : Expr) : MetaM (String × Array Json) := do
  let fmt ← Meta.ppExpr e
  return (toString fmt, #[])

/-- Decompose a spec theorem type into binders (named params + preconditions) and body.
    Uses `forallTelescope` to peel off all leading ∀ binders.
    Named binders get their name; auto-generated binders (from →) get "_". -/
private def decomposeSpecType (e : Expr) :
    MetaM (Array Json × String × Array Json) := do
  Meta.forallTelescope e fun xs body => do
    let mut binders : Array Json := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let userName := decl.userName
      let displayName :=
        if userName.hasMacroScopes || userName.isInternal || userName == `_ then "_"
        else toString userName
      let (typeText, typeAnnotated) ← ppExprAnnotated decl.type
      binders := binders.push (.mkObj [
        ("name", .str displayName),
        ("type", .str typeText),
        ("annotated_type", .arr typeAnnotated)
      ])
    let (bodyText, bodyAnnotated) ← ppExprAnnotated body
    return (binders, bodyText, bodyAnnotated)

/-- Run an action inside a context with Aeneas namespaces opened and activated.
    This sets up open declarations for `Aeneas.Std` and `Aeneas.Std.Result`,
    and activates scoped attributes from the `Aeneas` and `Aeneas.Std` namespaces. -/
private def withAeneasContext (action : MetaM α) : MetaM α := do
  let openDecls := [OpenDecl.simple `Aeneas.Std [], OpenDecl.simple `Aeneas.Std.Result []]
  withTheReader Core.Context (fun ctx => { ctx with openDecls }) do
    Lean.activateScoped `Aeneas
    Lean.activateScoped `Aeneas.Std
    action

/-- Classify the kind of a ConstantInfo. -/
private def classifyConstKind (info : ConstantInfo) : String :=
  match info with
  | .defnInfo _ => "def"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .thmInfo _ => "theorem"

/-- Extract step theorems from the step attribute's function map.
    This iterates ALL registered `@[step]` theorems (including stdlib),
    using the iterable map maintained by the step attribute. -/
private def extractStepTheoremsFromAttr :
    MetaM (Array TheoremInfo) := do
  let env ← getEnv
  let funMap := Step.getStepFunMap env
  withAeneasContext do
    let mut results : Array TheoremInfo := #[]
    let mut seen : Std.HashSet Name := {}
    for (funName, thmName) in funMap do
      if seen.contains thmName then continue
      seen := seen.insert thmName
      let some thmInfo := env.find? thmName | continue
      try
        let sorryStatus ← classifySorryStatus thmName
        let kind := classifyConstKind thmInfo
        let isPriv := Lean.isPrivateName thmName
        let (ppType, annotated) ← ppExprAnnotated thmInfo.type
        let (specBinders, specBodyText, annotatedSpecBody) ← decomposeSpecType thmInfo.type
        let declRanges ← Lean.findDeclarationRanges? thmName
        let leanSource := declRanges.map fun ranges =>
          let r := ranges.range
          Json.mkObj [
            ("begin_line", .num r.pos.line),
            ("begin_col", .num r.pos.column),
            ("end_line", .num r.endPos.line),
            ("end_col", .num r.endPos.column)
          ]
        let constModule := env.getModuleFor? thmName
        results := results.push {
          funName, thmName, kind, isPrivate := isPriv, sorryStatus,
          ppType, annotated, specBinders, specBodyText, annotatedSpecBody,
          leanSource, moduleName := constModule
        }
      catch e =>
        IO.eprintln s!"  Warning: error processing {thmName}: {← e.toMessageData.toString}"
    return results

/-- Extract all step theorems by iterating the environment constants.
    Returns (functionName, theoremName, sorryStatus, prettyPrintedType, annotatedJson). -/
private def extractStepTheorems (targetModule : Name) :
    MetaM (Array TheoremInfo) := do
  let env ← getEnv

  -- Collect constants from the target module and its children
  let mut moduleConstants : Array Name := #[]
  for i in [:env.header.moduleData.size] do
    let modName := env.header.moduleNames[i]!
    if modName == targetModule || targetModule.isPrefixOf modName then
      moduleConstants := moduleConstants ++ env.header.moduleData[i]!.constNames

  -- Set up Aeneas context once for all theorems
  withAeneasContext do
    let mut results : Array TheoremInfo := #[]
    for constName in moduleConstants do
      if constName.isInternal then continue
      let some info := env.find? constName | continue
      match info with
      | .thmInfo _ | .defnInfo _ | .axiomInfo _ => pure ()
      | _ => continue
      try
        let funName? ← extractSpecFunName? info.type
        match funName? with
        | some funName =>
          let sorryStatus ← classifySorryStatus constName
          let kind := classifyConstKind info
          let isPriv := Lean.isPrivateName constName
          let declRanges ← Lean.findDeclarationRanges? constName
          let leanSource := declRanges.map fun ranges =>
            let r := ranges.range
            Json.mkObj [
              ("begin_line", .num r.pos.line),
              ("begin_col", .num r.pos.column),
              ("end_line", .num r.endPos.line),
              ("end_col", .num r.endPos.column)
            ]
          results := results.push {
            funName, thmName := constName, kind, isPrivate := isPriv, sorryStatus,
            ppType := "TODO", annotated := #[],
            specBinders := #[], specBodyText := "", annotatedSpecBody := #[],
            leanSource, moduleName := env.getModuleFor? constName
          }
        | none => pure ()
      catch e =>
        IO.eprintln s!"  Warning: error processing {constName}: {← e.toMessageData.toString}"

    return results

-- ============================================================
-- Definition extraction
-- ============================================================

/-- Check if a name is internal/compiler-generated and should be skipped. -/
private def isInternalDef (n : Name) : Bool :=
  n.isInternal ||
  -- Skip match/proof/recursor/brecOn auxiliary definitions
  match n with
  | .str _ s =>
    s.startsWith "_" ||
    s == "brecOn" || s == "casesOn" || s == "recOn" || s == "rec" ||
    s == "noConfusion" || s == "noConfusionType" ||
    s == "below" || s == "ibelow" || s == "binductionOn" ||
    s == "sizeOf" || s == "sizeOf_spec" ||
    -- Skip derived/elaborated auxiliary definitions
    s == "ctorElim" || s == "ctorElimType" || s == "ctorIdx" ||
    s == "elim" || s == "read_discriminant" || s == "enumToBitVec" ||
    s.startsWith "match_" || s == "go"
  | _ => false

/-- Parse the Rust function name from an Aeneas-generated docstring.
    Docstrings have the format: `[crate::module::function]: ...`
    Returns `some "crate::module::function"` or `none`. -/
private def parseRustName (docstring : String) : Option String := do
  -- Find first '[' and matching ']'
  let openIdx ← docstring.toList.findIdx? (· == '[')
  let rest := (docstring.toList.drop (openIdx + 1))
  let closeIdx ← rest.findIdx? (· == ']')
  let content := String.ofList (rest.take closeIdx)
  let rustName := content.trimAscii.toString
  -- Strip trait prefixes
  if rustName.startsWith "Trait declaration: " then
    return (String.ofList (rustName.toList.drop "Trait declaration: ".length))
  else if rustName.startsWith "Trait implementation: " then
    return (String.ofList (rustName.toList.drop "Trait implementation: ".length))
  else
    return rustName

/-- Parse the Rust source location from a docstring.
    Format: `Source: '<file>', lines <begin_line>:<begin_col>-<end_line>:<end_col>`
    Returns `some (file, beginLine, endLine)` or `none`. -/
private def parseRustSource (docstring : String) : Option (String × Nat × Nat) := do
  -- Find "Source: '" prefix
  let chars := docstring.toList
  let srcPrefix := "Source: '".toList
  let srcIdx ← findSublistIdx chars srcPrefix
  let afterSrc := chars.drop (srcIdx + srcPrefix.length)
  -- Find closing quote for file path
  let quoteIdx ← afterSrc.findIdx? (· == '\'')
  let file := String.ofList (afterSrc.take quoteIdx)
  -- Find "lines " prefix
  let afterQuote := afterSrc.drop (quoteIdx + 1)
  let linesPrefix := "lines ".toList
  let linesIdx ← findSublistIdx afterQuote linesPrefix
  let afterLines := afterQuote.drop (linesIdx + linesPrefix.length)
  -- Parse "beginLine:beginCol-endLine:endCol"
  let dashIdx ← afterLines.findIdx? (· == '-')
  let beginPart := String.ofList (afterLines.take dashIdx)
  let endPart := String.ofList (afterLines.drop (dashIdx + 1))
  let beginLine ← (String.ofList (beginPart.toList.takeWhile Char.isDigit)).toNat?
  let endLine ← (String.ofList (endPart.toList.takeWhile Char.isDigit)).toNat?
  return (file, beginLine, endLine)

where
  /-- Find the index where a sublist first appears in a list. -/
  findSublistIdx (haystack : List Char) (needle : List Char) : Option Nat :=
    let needleLen := needle.length
    let haystackLen := haystack.length
    if needleLen > haystackLen then none
    else go haystack needle needleLen haystackLen 0
  go (haystack : List Char) (needle : List Char) (needleLen haystackLen i : Nat) : Option Nat :=
    if i + needleLen > haystackLen then none
    else
      let candidate := haystack.drop i |>.take needleLen
      if candidate == needle then some i
      else go haystack needle needleLen haystackLen (i + 1)
  termination_by haystackLen + 1 - i


/-- Collect constants from a target module, its children, and its parent modules.
    For example, if targetModule is `Demo.Properties`, this also scans `Demo`
    (which contains the auto-generated definitions). -/
private def collectModuleConstants (env : Environment) (targetModule : Name) : Array Name := Id.run do
  -- Get the top-level namespace (root component of the module name)
  -- For Demo.Properties → Demo; for Demo → Demo
  let topLevel := getTopLevel targetModule
  let mut moduleConstants : Array Name := #[]
  for i in [:env.header.moduleData.size] do
    let modName := env.header.moduleNames[i]!
    -- Include modules that share the same top-level namespace
    if getTopLevel modName == topLevel then
      moduleConstants := moduleConstants ++ env.header.moduleData[i]!.constNames
  return moduleConstants
where
  getTopLevel : Name → Name
    | .str .anonymous s => .str .anonymous s
    | .str parent _ => getTopLevel parent
    | .num .anonymous n => .num .anonymous n
    | .num parent _ => getTopLevel parent
    | .anonymous => .anonymous

/-- Count the number of top-level forall binders in an expression. -/
private def countForalls : Expr → Nat
  | .forallE _ _ body _ => 1 + countForalls body
  | _ => 0

/-- Count the number of top-level lambda binders in an expression. -/
private def countLambdas : Expr → Nat
  | .lam _ _ body _ => 1 + countLambdas body
  | _ => 0

/-- Try to unwrap a `Lean.Order.fix` (or similar fixpoint combinator) from the body.
    Given an expression like `Lean.Order.fix ... (fun f x1 ... xN => body) proof args`,
    extracts the inner body with the self-reference `f` and inner params properly handled.
    `remainingTypeParams` are type-level fvars for parameters consumed inside the fixpoint.
    Returns the unwrapped body, or the original expression if not a fixpoint. -/
private def tryUnwrapFix (e : Expr) (remainingTypeParams : Array Expr)
    (constName : Name) (topParams : Array Expr) : MetaM Expr := do
  let fn := e.getAppFn
  -- Check for fixpoint combinators (Lean.Order.fix, etc.)
  let isFix := fn.isConst && (fn.constName!.toString.endsWith ".fix" ||
    fn.constName! == ``Lean.Order.fix)
  if !isFix then return e

  let args := e.getAppArgs
  -- Find the lambda argument (the function being fixed)
  let some lamIdx := args.findIdx? (·.isLambda) | return e
  let lamArg := args[lamIdx]!

  -- Collect trailing value arguments (skip proofs)
  let trailing := args[lamIdx + 1:]
  let mut valueArgs : Array Expr := #[]
  for arg in trailing do
    let ty ← Meta.inferType arg
    if !(← Meta.isProp ty) then
      valueArgs := valueArgs.push arg

  -- Decompose: fun f x1 ... xN => body
  Meta.lambdaTelescope lamArg fun lamParams lamBody => do
    if lamParams.size < 1 then return e
    let selfRef := lamParams[0]!
    let innerParams := lamParams[1:].toArray
    -- Replace inner params with remaining type params + trailing value args
    let allReplacements := remainingTypeParams ++ valueArgs
    let mut body := lamBody
    for i in [:min innerParams.size allReplacements.size] do
      body := body.replaceFVar innerParams[i]! allReplacements[i]!
    -- Replace self-reference with the actual constant applied to already-stripped
    -- type params (so types match: f has T already specialized)
    let env ← getEnv
    let levels := env.find? constName |>.map
      (·.levelParams.map mkLevelParam) |>.getD []
    let selfRefConst := mkAppN (mkConst constName levels) topParams
    body := body.replaceFVar selfRef selfRefConst
    -- Re-abstract any unconsumed inner params back as lambdas
    if allReplacements.size < innerParams.size then
      let unconsumed := innerParams[allReplacements.size:]
      body ← Meta.mkLambdaFVars unconsumed body
    return body

/-- Extract all definitions (functions, types, etc.) from the target module
    and its sibling/parent modules. Returns a JSON array of definition objects. -/
private def extractDefinitions (targetModule : Name) : MetaM (Array Json) := do
  let env ← getEnv
  let moduleConstants := collectModuleConstants env targetModule

  -- Set up Aeneas context once for all definitions
  withAeneasContext do
    let mut results : Array Json := #[]
    for constName in moduleConstants do
      if isInternalDef constName then continue
      let some info := env.find? constName | continue
      -- Skip theorems (they're handled separately as step theorems)
      -- Skip recursors, quotients, constructors
      match info with
      | .defnInfo _ | .inductInfo _ | .opaqueInfo _ | .axiomInfo _ => pure ()
      | _ => continue
      -- Skip instance/elaboration artifacts (start with "inst")
      let nameStr := constName.toString
      if nameStr.startsWith "inst" then continue

      try
        let kind := classifyConstKind info

        -- Pretty-print type with annotations
        let (typeSig, annotatedType) ← ppExprAnnotated info.type

        -- Get docstring
        let docstring ← Lean.findDocString? env constName
        let rustName := docstring.bind parseRustName
        let rustSource := docstring.bind parseRustSource

        -- Get declaration ranges for Lean source location
        let declRanges ← Lean.findDeclarationRanges? constName
        let leanSource := declRanges.map fun ranges =>
          let r := ranges.range
          Json.mkObj [
            ("begin_line", .num r.pos.line),
            ("begin_col", .num r.pos.column),
            ("end_line", .num r.endPos.line),
            ("end_col", .num r.endPos.column)
          ]

        -- Determine which module this constant belongs to
        let constModule := env.getModuleFor? constName

        -- Extract annotated body for definitions (best-effort).
        -- Strips leading lambdas, unwraps Lean.Order.fix, and exports binder info.
        let (annotatedBody?, binderInfo?, retTypeInfo?) ← do
          match info with
          | .defnInfo di =>
            try
              let numTypeParams := countForalls info.type
              let numTopLambdas := countLambdas di.value
              let numToStrip := min numTopLambdas numTypeParams

              -- Extract binders + return type + body inside forallTelescope
              Meta.forallBoundedTelescope info.type numTypeParams fun typeParams retType => do
                -- Export binder information
                let mut binders : Array Json := #[]
                for param in typeParams do
                  let decl ← param.fvarId!.getDecl
                  let (typePP, typeAnnotated) ← ppExprAnnotated decl.type
                  let bi := decl.binderInfo
                  binders := binders.push (Json.mkObj [
                    ("name", .str decl.userName.toString),
                    ("type", .str typePP),
                    ("annotated_type", .arr typeAnnotated),
                    ("implicit", .bool (bi.isImplicit || bi.isStrictImplicit)),
                    ("inst_implicit", .bool bi.isInstImplicit)
                  ])
                -- Export annotated return type
                let (retTypePP, retTypeAnnotated) ← ppExprAnnotated retType
                let retTypeJson := Json.mkObj [
                  ("type", .str retTypePP),
                  ("annotated_type", .arr retTypeAnnotated)
                ]

                -- Extract body: strip top-level lambdas + unwrap fixpoint
                let topParams := typeParams[:numToStrip].toArray
                let remainingParams := typeParams[numToStrip:].toArray
                let strippedBody := Expr.beta di.value topParams
                let body ← tryUnwrapFix strippedBody remainingParams constName topParams
                let (_, annBody) ← ppExprAnnotated body
                pure (some annBody, some (.arr binders), some retTypeJson)
            catch e =>
              IO.eprintln s!"  Warning: failed to pretty-print body of {constName}: {← e.toMessageData.toString}"
              pure (none, none, none)
          | _ => pure (none, none, none)

        -- Build JSON
        let mut fields : Array (String × Json) := #[
          ("name", .str nameStr),
          ("kind", .str kind)
        ]
        fields := fields.push ("type_signature", .str typeSig)
        fields := fields.push ("annotated_type_signature", .arr annotatedType)

        if let some annBody := annotatedBody? then
          fields := fields.push ("annotated_body", .arr annBody)
        if let some bi := binderInfo? then
          fields := fields.push ("binders", bi)
        if let some rt := retTypeInfo? then
          fields := fields.push ("return_type", rt)

        if let some doc := docstring then
          fields := fields.push ("docstring", .str doc)
        if let some rn := rustName then
          fields := fields.push ("rust_name", .str rn)
        if let some (file, beginLine, endLine) := rustSource then
          fields := fields.push ("rust_source", Json.mkObj [
            ("file", .str file),
            ("begin_line", .num beginLine),
            ("end_line", .num endLine)
          ])
        if let some ls := leanSource then
          fields := fields.push ("lean_source", ls)
        if let some modName := constModule then
          fields := fields.push ("module", .str modName.toString)

        results := results.push (Json.mkObj fields.toList)
      catch e =>
        IO.eprintln s!"  Warning: error processing definition {constName}: {← e.toMessageData.toString}"

    return results

unsafe def main (args : List String) : IO Unit := do
  if args.length < 2 then
    IO.eprintln "Usage: lake env lean --run AeneasDocExtract.lean <ModuleName> <output.json>"
    IO.Process.exit 1

  let moduleName := args[0]!.toName
  let outputPath := args[1]!

  IO.println s!"Loading module: {moduleName}"
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := moduleName }] {} 0 (loadExts := true)

  let opts := Options.empty
    |> (·.insert `pp.unicode true)
    |> (·.insert `maxHeartbeats (8000000 : Nat))
  let ctx : Core.Context := { fileName := "", fileMap := FileMap.ofString "", options := opts }
  let state : Core.State := { env }

  -- Extract step theorems from the @[step] attribute map
  IO.println "Extracting step theorems..."
  let (attrThms, state) ← (extractStepTheoremsFromAttr).run'.toIO ctx state
  IO.println s!"  Found {attrThms.size} step theorems"

  -- Deduplicate
  let mut seen : Std.HashSet Name := {}
  let mut allTheorems := attrThms
  for t in attrThms do
    seen := seen.insert t.thmName

  IO.println "Extracting definitions..."
  let (definitions, _) ← (extractDefinitions moduleName).run'.toIO ctx state

  -- Build JSON output
  let theoremJsons : Array Json := allTheorems.map fun t =>
    let baseFields : List (String × Json) := [
      ("function", .str t.funName.toString),
      ("theorem", .str t.thmName.toString),
      ("kind", .str t.kind),
      ("is_private", .bool t.isPrivate),
      ("sorry_status", .str t.sorryStatus),
      ("statement", .str t.ppType),
      ("annotated_statement", .arr t.annotated),
      ("spec_binders", .arr t.specBinders),
      ("spec_body", .str t.specBodyText),
      ("annotated_spec_body", .arr t.annotatedSpecBody)
    ]
    let lsFields := match t.leanSource with
      | some ls => [("lean_source", ls)]
      | none => []
    let modFields := match t.moduleName with
      | some m => [("module", .str m.toString)]
      | none => []
    Json.mkObj (baseFields ++ lsFields ++ modFields)
  let json := Json.mkObj [
    ("theorems", .arr theoremJsons),
    ("definitions", .arr definitions)
  ]

  IO.FS.writeFile outputPath json.pretty
  IO.println s!"Written to {outputPath}"
