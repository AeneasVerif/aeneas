import Lean

namespace Aeneas.Meta.TraitDefault

open Lean Meta Elab Term Command

/-!
# `impl_def` — v5

Syntax change: the user now writes

    impl_def TraitInst : Trait := {
      N := 5,
      P := Trait.P.default TraitInst   -- self-reference, as in plain `def`
    }

Detection rule for a @[trait_default] call:
  • the head of the application is a @[trait_default]-marked name, AND
  • the final argument is exactly the identifier being defined (`id`)
In that case we strip the self-argument; the macro supplies the partial struct
itself (as before).  Everything else is unchanged from v4.
-/

/-!
# `trait_default` attribute
-/

initialize traitDefaultAttr : TagAttribute ←
  registerTagAttribute `trait_default
    "Mark a function as a trait method/const default implementation. We use this to trigger special elaboration of `impl_def`"

def isTraitDefault (n : Name) : CoreM Bool :=
  return traitDefaultAttr.hasTag (← getEnv) n

/-!
# `impl_def` syntax
-/

private def implDefFieldParser : Lean.Parser.Parser :=
  Lean.Parser.leadingNode `implDefField Lean.Parser.maxPrec <|
    Lean.Parser.rawIdent >>
    Lean.Parser.symbol " := " >>
    Lean.Parser.withPosition (Lean.Parser.termParser Lean.Parser.leadPrec) >>
    Lean.Parser.optional (Lean.Parser.symbol ",")

private def implDefFieldsParser : Lean.Parser.Parser :=
  Lean.Parser.leadingNode `implDefFields Lean.Parser.maxPrec <|
    Lean.Parser.manyIndent implDefFieldParser

/-!
# Helpers
-/

/-- Compute the number of *explicit* arguments of type `ty` -/
def explicitArity (ty : Expr) : Nat :=
  match ty with
  | .forallE _ _ body bi =>
    if bi.isExplicit then 1 + explicitArity body else explicitArity body
  | _ => 0

def buildStructExpr
    (structName : Name) (fieldMap : Array (Name × Expr))
    (allFieldNames : Array Name) (ty : Expr) : MetaM Expr := do
  let mut args : Array Expr := #[]
  for fname in allFieldNames do
    match fieldMap.find? (·.1 == fname) with
    | some (_, e) => args := args.push e
    | none        => args := args.push (← mkSorry ty false)
  return mkAppN (mkConst (structName ++ `mk)) args

def applyStructDefault
    (fnExpr : Expr) (arity : Nat)
    (knownFields : Array (Name × Expr)) (allFieldNames : Array Name) : MetaM Expr := do
  if arity == 0 then whnf fnExpr
  else
    let mut args  : Array Expr := #[]
    let mut count : Nat        := 0
    for fname in allFieldNames do
      if count == arity then break
      match knownFields.find? (·.1 == fname) with
      | some (_, e) => args := args.push e;                               count := count + 1
      | none        => args := args.push (← mkSorry (mkConst `Nat) false); count := count + 1
    whnf (mkAppN fnExpr args)

def applyTraitDefault
    (fnExpr : Expr) (knownFields : Array (Name × Expr))
    (allFieldNames : Array Name) (structName : Name) (ty : Expr) : MetaM Expr := do
  let selfExpr ← buildStructExpr structName knownFields allFieldNames ty
  whnf (mkApp fnExpr selfExpr)

/-!
# Classify a field-value syntax node (three outcomes)
-/
inductive FieldKind where
  /-- ordinary expression, elaborate directly -/
  | plain
  /-- @[trait_default] call with self argument -/
  | traitDefault (fn : Syntax)
  /-- @[trait_default] used WITHOUT self-arg (error) -/
  | bareTraitDefault (n : Name)

/-- Inspect `stx` and classify it relative to the definition name `defId`.
    Peels one layer of parentheses first. -/
def classifyField (defId : Name) (stx : Syntax) : TermElabM FieldKind := do
  let stx : Syntax := match stx with | `(($inner)) => inner | other => other
  -- Helper: is `f` (a Syntax node) headed by a @[trait_default] constant?
  let traitDefaultHead? (f : Syntax) : TermElabM (Option Name) :=
    try
      let e ← instantiateMVars =<< Term.elabTermAndSynthesize f none
      if let .const n _ := e.getAppFn then
        if (← isTraitDefault n) then return some n
      return none
    catch _ => return none
  match stx with
  | `($f:ident $arg:ident) =>
    -- Fast path: both head and argument are plain identifiers.
    if arg.getId == defId then
      if (← isTraitDefault f.getId) then return .traitDefault f
      -- arg matches defId but head is not @[trait_default] — fall through to
      -- elaborate normally (user just happens to pass defId as an argument).
    -- Check if the bare head (no arg match) is a @[trait_default] — missing self.
    if arg.getId != defId then
      if let some n ← traitDefaultHead? f then
        -- head is @[trait_default] but arg is not the self-ref
        -- Could be a legitimate non-self call; treat as plain.
        return .plain
    return .plain
  | `($f $arg:ident) =>
    -- General application where argument is an ident.
    if arg.getId == defId then
      if let some _ ← traitDefaultHead? f then return .traitDefault f
    return .plain
  | `($f:ident) =>
    -- Bare identifier with no argument.
    if let some n ← traitDefaultHead? f then
      return .bareTraitDefault n
    return .plain
  | _ => return .plain

/-!
# Elaborator
-/
def elabImplDef (id : TSyntax `ident) (ty : TSyntax `term)
    (fields : Array (TSyntax `ident)) (vals : Array (TSyntax `term))
    (attrs : Array Attribute := #[]) :
    CommandElabM Unit := do
  let tyExpr ← liftTermElabM <| instantiateMVars =<< Term.elabType ty
  let structName ← liftTermElabM <| do
    let .const sn _ ← whnf tyExpr | throwError "Expected a structure type"
    return sn

  let env ← getEnv
  let allFieldNames : Array Name :=
    (getStructureInfo? env structName |>.map (·.fieldNames)).getD #[]

  let defId := id.getId
  let fieldPairs : Array (Name × Syntax) :=
    (fields.zip vals).map fun (f, v) => (f.getId, v)

  -- Pre-classify; error early on bare @[trait_default] use.
  let classified ← liftTermElabM <| fieldPairs.mapM fun (fname, fstx) => do
    let k ← classifyField defId fstx
    if let .bareTraitDefault _ := k then
      throwError ("impl_def: `{n}` is marked @[trait_default] but is used " ++
        "without a self-argument.\n" ++
        "Write `{fname} := {n} {defId}` to refer to the definition being built.")
    return (fname, fstx, k)

  -- PASS 1: plain fields
  let mut knownFields : Array (Name × Expr) := #[]
  for (fname, fstx, k) in classified do
    if let .plain := k then
      let e ← liftTermElabM <| instantiateMVars =<< Term.elabTermAndSynthesize fstx none
      knownFields := knownFields.push (fname, e)

  -- PASS 2: @[trait_default] fields wit self-arg
  for (fname, _, k) in classified do
    if let .traitDefault fnStx := k then
      let fnExpr ← liftTermElabM <| instantiateMVars =<< Term.elabTermAndSynthesize fnStx none
      let reduced ← liftTermElabM <| applyTraitDefault fnExpr knownFields allFieldNames structName tyExpr
      knownFields := knownFields.push (fname, reduced)

  -- PASS 3: omitted fields with struct-level defaults
  let suppliedNames := classified.map (·.1)
  for fname in allFieldNames do
    if suppliedNames.contains fname then continue
    match getEffectiveDefaultFnForField? env structName fname with
    | none => throwError "Field `{fname}` is missing and has no default value"
    | some defFnName =>
      let fnExpr := Lean.mkConst defFnName
      let arity  := match env.find? defFnName with
        | some ci => explicitArity ci.type
        | none    => 0
      let reduced ← liftTermElabM <| applyStructDefault fnExpr arity knownFields allFieldNames
      knownFields := knownFields.push (fname, reduced)

  -- Assemble in declaration order
  let orderedFields ← liftTermElabM <| do
    let mut res : Array Expr := #[]
    for fname in allFieldNames do
      match knownFields.find? (·.1 == fname) with
      | some (_, e) => res := res.push e
      | none => throwError "Error: can't resolve field name `{fname}`"
    return res

  let finalExpr := mkAppN (mkConst (structName ++ `mk)) orderedFields
  let idName    := id.getId
  let decl ← liftTermElabM <| do
    let ty'    ← inferType finalExpr
    let final' ← instantiateMVars finalExpr
    let decl := Declaration.defnDecl {
      name := idName, levelParams := [], type := ty',
      value := final', hints := .regular 0, safety := .safe
    }
    addDecl decl
    return decl
  let opts ← getOptions
  let env ← getEnv
  let env ← liftIO <| env.enableRealizationsForConst opts idName
  setEnv env
  liftTermElabM <| do
    Term.applyAttributesAt idName attrs AttributeApplicationTime.afterTypeChecking
    compileDecl decl
    Term.applyAttributesAt idName attrs AttributeApplicationTime.afterCompilation
    logInfo m!"impl_def: defined `{idName}` successfully"

elab doc?:(Parser.Command.docComment)? attrs?:(Parser.Term.attributes)? "impl_def " id:ident " : " ty:term " := " "{" fieldsNode:implDefFieldsParser "}" : command => do
  let entries := fieldsNode.raw[0].getArgs
  let fields : Array (TSyntax `ident) := entries.map (⟨·[0]⟩)
  let vals   : Array (TSyntax `term)  := entries.map (⟨·[2]⟩)
  let attrs ← match attrs? with
    | none => pure #[]
    | some attrStx => liftTermElabM <| Elab.elabAttrs (attrStx.raw.getArg 1).getArgs
  elabImplDef id ty fields vals attrs
  if let some doc := doc? then
    let binders := Syntax.missing -- TODO
    liftTermElabM (Lean.addDocString id.getId binders doc)

end Aeneas.Meta.TraitDefault
