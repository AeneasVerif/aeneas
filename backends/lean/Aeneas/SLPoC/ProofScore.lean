import Lean

/-!
# How close are the separation-logic proofs to the ideal proof?

An engineering tool, not part of the library: it measures how much of the
separation logic the automation still leaves to the user.

Run it from `backends/lean` with

```
lake env lean --run Aeneas/SLPoC/ProofScore.lean [-o REPORT.html] [FILE.lean …]
```

With no file arguments it scores every file of `Aeneas/SLPoC/Examples`, and
writes `Aeneas/SLPoC/proof-score.html`.

## What is measured

The ideal proof of a triple never handles the separation logic manually: it
unfolds the program and uses `sl_step`, `sl_step*`, `step`, or `step*`, with
pure reasoning (`obtain`, `have`, `simp`, …) and `sl_pull` in between, and one
such block per branch of the program:

```lean
unfold f
sl_pull ⟨h, _⟩
obtain rfl : … := …
sl_step*
split
next => …ideal…
next => …ideal…
```

Each *spot* is one straight-line block of the tactic script: the block before
the first branch, plus one per branch body, recursively.  A proof with no
branch therefore has one spot, and a proof with two branches has three.  A spot
is ideal when none of its steps handles the separation logic by hand, and the
score of a file is the fraction of its spots that are ideal.

A step handles the separation logic by hand when it is one of the manual
tactics (`sl_frame`, `sl_xchange`, `sl_xpull`, `sl_xsimpl`, `sl_xapp`,
`sl_conseq`, …), or when it mentions separation-logic vocabulary: a connective
(`∗`, `↦`, `⊢`, `-∗`, `emp`, `GC`, `iprop(…)`), or a lemma or definition whose
statement is about `SLProp` (`unfold wellFormed`, `simp [nodes_snoc]`,
`exact triple_pure …`).  `sl_step`, `sl_step*`, `step`, `step*`, and `sl_pull`
are the automation itself and are free; so is any pure reasoning.  A manual
`sl_pure` is not free: an ideal proof lets stepping handle the terminal return.
Nor is `sl_step with some.spec`: explicitly naming any declaration whose
statement is about a triple steers automation manually.  A local hypothesis such
as an induction hypothesis remains free.

Only declarations whose statement is a triple are scored.  The separation-logic
lemmas a development proves on the side (`nodes_snoc`, `nodesFrom_append`, …)
are not scored, but a triple proof that *uses* one is charged for it.

## The report

A standalone HTML page — no script, style or font is fetched from anywhere.
Under the summary tables, every file is a collapsible section listing its
proofs and spots. Each spot has its number of lines of code and its code, highlighted, framed
in green when the spot is ideal and in red when it is not, with the offending
lines shaded and named underneath.  A spot shows its own code only: the nested
blocks are elided as `…` because they are spots of their own, and the comments
are left out.  The toggle at the top of the page switches between all the
spots, only the ideal ones, and only those that are not.

## How it works

The file is parsed with Lean's own parser, using the environment its `import`s
produce, so `⦃ … ⦄`, `sl_step*` and the rest are real syntax nodes rather than
text.  Only the commands that change the scope (`namespace`, `section`, `end`,
`open`, `universe`, `variable`, `set_option`) are elaborated — enough for the
scoped notation of `SepLogic` to parse — and declarations are never elaborated.
Scoring a file therefore costs about a second and works even on a file that
does not compile.

The highlighting is a by-product: the report renders the *tokens* the parser
produced, so what it colours is what Lean itself saw — an identifier is red
exactly when it resolves to a separation-logic declaration.  What lies between
two tokens is whitespace, comments, and the little syntax a tactic block holds
together with (`<;>`, `;`), of which the comments are dropped.
-/

namespace Aeneas.SLPoC.ProofScore

open Lean Elab

/-! ## Vocabulary of the separation logic -/

/-- Tokens that only occur in a separation-logic statement. -/
def slAtoms : Array String :=
  #["∗", "∗+", "↦", "⊢", "⊢+", "⊣⊢", "-∗", "-∗+", "iprop(", "⌜", "⌝",
    "emp", "GC", "∀ˢ", "⦃", "⦄"]

/-- Last components of the constants at the core of the logic.  A declaration
whose statement mentions one of them is a separation-logic declaration. -/
def slCoreNames : Array String :=
  #["SLProp", "SLPre", "SLPost", "himpl", "qimpl", "hequiv", "hempty", "hpure",
    "hgc", "hsingle", "hstar", "hexists", "hforall", "hwand", "qstar", "qwand",
    "triple", "Wp", "theta"]

/-- The `⦃ P ⦄ m ⦃⇓ v => Q ⦄` notations of `ST.lean`: a declaration that uses one
of them states a triple. -/
def specSyntaxKinds : Array Name :=
  #[`Aeneas.SLPoC.SepLogic.specSyntax, `Aeneas.SLPoC.SepLogic.specSyntaxPred,
    `Aeneas.SLPoC.SepLogic.slSpecSyntax, `Aeneas.SLPoC.SepLogic.slSpecSyntaxPred]

/-- Simp sets that configure the automation: tuning them inside a proof is
separation-logic work too. -/
def slAttrNames : Array String := #["sl_simps", "step_simps", "step_post_simps"]

/-- Tactics that handle the separation logic by hand. -/
def manualTactics : Array String :=
  #["sl_frame", "sl_frame?", "sl_xsimpl", "sl_xpull", "sl_xchange", "sl_xapp",
    "sl_xval", "sl_conseq", "sl_pull_step", "sl_pull_keep", "sl_pull_keep_step",
    "sl_norm", "sl_pull_shallow", "sl_side?", "sl_pure"]

/-- Tactics that *are* the automation: the ideal proof is made of these. -/
def idealTactics : Array String :=
  #["sl_step", "sl_step*", "step", "step*", "sl_pull"]

/-- Combinators that do not split the goal: like `<;>`, what they run belongs to
the block that runs them, not to a block of its own. -/
def inlineTactics : Array String :=
  #["try", "repeat", "repeat'", "first", "all_goals", "any_goals", "focus",
    "iterate", "fail_if_success", "checkpoint"]

/-! ## Syntax helpers -/

def lastComponent (n : Name) : String :=
  match n with
  | .str _ s => s
  | .num p _ => lastComponent p
  | .anonymous => ""

/-- Every prefix of `n`, longest first: the namespaces a name written inside
`n` is resolved against. -/
def namePrefixes (n : Name) : Array Name := Id.run do
  let mut result := #[n]
  let mut n := n
  while !n.isAnonymous do
    n := n.getPrefix
    result := result.push n
  return result

/-- The full names an identifier written as `n`, inside namespace `currNamespace`
and with `opens` open, can refer to. -/
def resolutionCandidates (currNamespace : Name) (opens : Array Name) (n : Name) : Array Name :=
  if n.getRoot == `_root_ then #[n.replacePrefix `_root_ .anonymous]
  else Id.run do
    let mut result := #[]
    for prefix' in namePrefixes currNamespace do
      result := result.push (prefix' ++ n)
      for opened in opens do
        result := result.push (prefix' ++ opened ++ n)
    return result.push n

/-- Whether an elaborated type mentions the separation logic, including through
reducible type aliases. -/
partial def exprMentionsSL (env : Environment) (e : Expr)
    (seen : NameSet := {}) : Bool :=
  (e.find? fun sub =>
    match sub with
    | .const n levels =>
      if slCoreNames.contains (lastComponent n) then
        true
      else if seen.contains n then
        false
      else
        match env.find? n with
        | some (.defnInfo info) =>
          match info.hints with
          | .abbrev =>
            exprMentionsSL env
              (info.value.instantiateLevelParams info.levelParams levels)
              (seen.insert n)
          | _ => false
        | _ => false
    | _ => false).isSome

partial def syntaxFind? (stx : Syntax) (p : Syntax → Bool) : Option Syntax :=
  if p stx then some stx
  else stx.getArgs.findSome? (syntaxFind? · p)

def isTacticSeq (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Tactic.tacticSeq ||
  stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented ||
  stx.getKind == ``Lean.Parser.Tactic.tacticSeqBracketed

/-- The individual tactics of a tactic sequence, without the separators. -/
partial def seqSteps (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Lean.Parser.Tactic.tacticSeq then
    stx.getArgs.flatMap seqSteps
  else if stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
    keep stx[0].getArgs
  else if stx.getKind == ``Lean.Parser.Tactic.tacticSeqBracketed then
    keep stx[1].getArgs
  else if stx.getKind == nullKind then
    keep stx.getArgs
  else #[stx]
where
  keep (args : Array Syntax) : Array Syntax :=
    args.filter fun a => !a.isAtom && !a.isMissing && a.getKind != nullKind

/-- The first token of a tactic, which identifies it. -/
partial def firstAtom (stx : Syntax) : String :=
  match stx with
  | .atom _ val => val.trimAscii.toString
  | .node _ _ args => args.findSome? (fun a =>
      let s := firstAtom a
      if s.isEmpty then none else some s) |>.getD ""
  | _ => ""

/-! ## Reading a file

Parsing only, with the scoping commands elaborated so that the scoped notation
of `SepLogic` is available. -/

/-- A declaration of the file, with the scope it was written in. -/
structure ParsedDecl where
  /-- Fully qualified name, `example` declarations excepted. -/
  name : Name
  /-- Name as written in the file. -/
  shortName : Name
  line : Nat
  /-- The statement, i.e. the binders and the type. -/
  signature? : Option Syntax
  /-- The proof, i.e. everything after `:=`. -/
  value? : Option Syntax
  /-- Whether this is an `abbrev`; its value may reveal an aliased `SLProp`. -/
  isAbbrev : Bool := false
  /-- Namespace the declaration is written in. -/
  currNamespace : Name
  /-- Namespaces opened above it, as an over-approximation: `section`s are
  ignored, and an `open` of a namespace this run never elaborated into
  existence still counts. -/
  opens : Array Name
  deriving Inhabited

structure ParsedFile where
  path : System.FilePath
  input : String
  fileMap : FileMap
  decls : Array ParsedDecl
  parseErrors : Array String

/-- Commands whose effect the parser needs, and which are cheap to elaborate. -/
def scopingCommands : Array Name :=
  #[``Lean.Parser.Command.namespace, ``Lean.Parser.Command.end,
    ``Lean.Parser.Command.section, ``Lean.Parser.Command.open,
    ``Lean.Parser.Command.universe, ``Lean.Parser.Command.variable,
    ``Lean.Parser.Command.set_option]

def declKinds : Array Name :=
  #[``Lean.Parser.Command.theorem, ``Lean.Parser.Command.example,
    ``Lean.Parser.Command.definition, ``Lean.Parser.Command.abbrev,
    ``Lean.Parser.Command.instance, ``Lean.Parser.Command.opaque,
    ``Lean.Parser.Command.axiom]

def declSigKinds : Array Name :=
  #[``Lean.Parser.Command.declSig, ``Lean.Parser.Command.optDeclSig,
    ``Lean.Parser.Term.typeSpec]

def declValKinds : Array Name :=
  #[``Lean.Parser.Command.declValSimple, ``Lean.Parser.Command.declValEqns,
    ``Lean.Parser.Command.whereStructInst, ``Lean.Parser.Term.byTactic]

/-- The modules `path` imports. -/
def fileImports (path : System.FilePath) : IO (Array Import) := do
  let input ← IO.FS.readFile path
  let (header, _, _) ← Parser.parseHeader (Parser.mkInputContext input path.toString)
  return Elab.headerToImports header

/-- The module a file defines, when it has been built: importing it makes the
notation and the constants the file itself introduces available. -/
def builtModule? (path : System.FilePath) : IO (Option Name) := do
  let comps := (path.withExtension "").components
  for i in [0:comps.length] do
    let some head := (comps.drop i).head? | continue
    let name := (comps.drop i).tail.foldl (fun n c => n ++ Name.mkSimple c) (Name.mkSimple head)
    let some olean ← (do try return some (← findOLean name) catch _ => return none) | continue
    if ← olean.pathExists then return some name
  return none

/-- One environment for every file to score: the initializers of the imported
modules may only be run once per process, and importing the union costs one
import instead of one per file. -/
unsafe def importUnion (files : Array System.FilePath) : IO Environment := do
  let mut imports : Array Import := #[]
  for path in files do
    let mut fileImports ← fileImports path
    if let some self ← builtModule? path then
      fileImports := fileImports.push { module := self }
    for imp in fileImports do
      unless imports.any (·.module == imp.module) do
        imports := imports.push imp
  IO.println s!"importing {imports.size} modules"
  let source := String.join (imports.toList.map fun imp => s!"import {imp.module}\n")
  let inputCtx := Parser.mkInputContext source "<imports>"
  let (header, _, messages) ← Parser.parseHeader inputCtx
  enableInitializersExecution
  let (env, messages) ← Elab.processHeader header {} messages inputCtx
  for msg in messages.toList do
    if msg.severity == .error then
      throw <| IO.userError s!"cannot import {imports.map (·.module)}: {← msg.data.toString}"
  return env

/-- Parse `path`, elaborating only the scoping commands. -/
def parseFile (env : Environment) (path : System.FilePath) : IO ParsedFile := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let mut cmdState := Command.mkState env messages {}
  let mut ps := parserState
  let mut decls : Array ParsedDecl := #[]
  let mut opens : Array Name := #[]
  repeat
    let scope := cmdState.scopes.head!
    let pmctx : Parser.ParserModuleContext :=
      { env := cmdState.env, options := scope.opts
        currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (stx, ps', messages') := Parser.parseCommand inputCtx pmctx ps cmdState.messages
    ps := ps'
    cmdState := { cmdState with messages := messages' }
    if Parser.isTerminalCommand stx then break
    if scopingCommands.contains stx.getKind then
      let cmdCtx : Command.Context :=
        { cmdPos := ps.pos, fileName := path.toString, fileMap := inputCtx.fileMap
          snap? := none, cancelTk? := none }
      -- An `open` of a namespace this run never elaborated into existence fails;
      -- the scoped notation the parser needs comes from the imports anyway.
      match ← EIO.toIO' ((Command.elabCommandTopLevel stx cmdCtx).run cmdState) with
      | .ok (_, s) => cmdState := { s with messages := messages' }
      | .error _ => pure ()
      if stx.getKind == ``Lean.Parser.Command.open then
        opens := opens ++ collectIdents stx
    else if let some decl := findDecl inputCtx.fileMap scope.currNamespace opens stx then
      decls := decls.push decl
  let parseErrors ← cmdState.messages.toList.filterMapM fun msg => do
    if msg.severity == .error then
      return some s!"{msg.pos.line}:{msg.pos.column}: {(← msg.data.toString).trimAscii.toString}"
    else return none
  return { path, input, fileMap := inputCtx.fileMap, decls,
           parseErrors := parseErrors.toArray }
where
  collectIdents (stx : Syntax) : Array Name :=
    match stx with
    | .ident _ _ n _ => #[n]
    | .node _ _ args => args.flatMap collectIdents
    | _ => #[]
  findDecl (fileMap : FileMap) (currNamespace : Name) (opens : Array Name) (stx : Syntax) :
      Option ParsedDecl := do
    let decl ← syntaxFind? stx fun s => declKinds.contains s.getKind
    let line := fileMap.toPosition (decl.getPos?.getD 0) |>.line
    let shortName :=
      match syntaxFind? decl (·.getKind == ``Lean.Parser.Command.declId) with
      | some declId => declId[0].getId
      | none => Name.mkSimple s!"example@{line}"
    return {
      name := currNamespace ++ shortName
      shortName, line
      signature? := syntaxFind? decl fun s => declSigKinds.contains s.getKind
      value? := syntaxFind? decl fun s => declValKinds.contains s.getKind
      isAbbrev := decl.getKind == ``Lean.Parser.Command.abbrev
      currNamespace, opens
    }

/-! ## Recognising separation-logic vocabulary -/

/-- Resolves the identifiers a proof mentions against the separation-logic
declarations, as they are visible from one point of the file. -/
structure Resolver where
  /-- Fully qualified names of the declarations whose statement is about the
  separation logic. -/
  slNames : NameSet
  currNamespace : Name := .anonymous
  opens : Array Name := #[]

def Resolver.isSL (r : Resolver) (n : Name) : Bool :=
  (resolutionCandidates r.currNamespace r.opens n).any r.slNames.contains

/-- Does this piece of syntax mention the separation logic?  Returns what gave
it away. -/
partial def syntaxMentionsSL (r : Resolver) (stx : Syntax) : Option String :=
  match stx with
  | .atom _ val =>
    let val := val.trimAscii.toString
    if slAtoms.contains val then some s!"the connective `{val}`"
    else if manualTactics.contains val then some s!"`{val}`"
    else none
  | .ident _ _ n _ =>
    if slAttrNames.contains (lastComponent n) then some s!"the simp set `{n}`"
    else if r.isSL n then some s!"the separation-logic declaration `{n}`"
    else none
  | .node _ k args =>
    if specSyntaxKinds.contains k then some "a triple"
    else if k.getRoot == `Aeneas && (k.toString.splitOn "SepLogic").length > 1 then
      some "separation-logic notation"
    else args.findSome? (syntaxMentionsSL r)
  | _ => none

/-- The imported constants whose statement is about the separation logic.  The
logic lives under `Aeneas`, so the rest of the environment is skipped. -/
def importedSLNames (env : Environment) : NameSet := Id.run do
  let mut names := {}
  for (n, info) in env.constants.toList do
    if n.isInternal || n.getRoot != `Aeneas then continue
    if slCoreNames.contains (lastComponent n) || exprMentionsSL env info.type then
      names := names.insert n
  return names

/-- The separation-logic declarations of the file itself, which the environment
does not know about when the file is not built (or does not build). -/
def localSLNames (file : ParsedFile) (imported : NameSet) : NameSet := Id.run do
  let mut names := imported
  for decl in file.decls do
    let r : Resolver :=
      { slNames := names, currNamespace := decl.currNamespace, opens := decl.opens }
    let signatureMentionsSL :=
      decl.signature?.any (syntaxMentionsSL r · |>.isSome)
    let aliasMentionsSL :=
      decl.isAbbrev && decl.value?.any (syntaxMentionsSL r · |>.isSome)
    if signatureMentionsSL || aliasMentionsSL then
      names := names.insert decl.name
  return names

/-- Is this declaration's statement a triple? -/
def isTriple (decl : ParsedDecl) : Bool :=
  match decl.signature? with
  | none => false
  | some sig =>
    (syntaxFind? sig fun s =>
      specSyntaxKinds.contains s.getKind ||
      (s.isIdent && lastComponent s.getId == "triple")).isSome

/-! ## Scoring a proof -/

inductive Verdict where
  | ideal
  | manual (reason : String)
  deriving Inhabited

def Verdict.isIdeal : Verdict → Bool
  | .ideal => true
  | .manual _ => false

/-- A token of the source, as the parser saw it, with the class it is
highlighted with. -/
structure Token where
  start : String.Pos.Raw
  stop : String.Pos.Raw
  cls : String
  deriving Inhabited

structure Step where
  line : Nat
  /-- First line of the step, for the list of what made a spot manual. -/
  text : String
  verdict : Verdict
  start : String.Pos.Raw
  stop : String.Pos.Raw
  /-- Ranges of the nested blocks, which are spots of their own and are elided
  from the code of this one. -/
  holes : Array (String.Pos.Raw × String.Pos.Raw)
  tokens : Array Token
  deriving Inhabited

structure Spot where
  line : Nat
  steps : Array Step
  /-- The code of the spot, highlighted, one `<div>` per line. -/
  html : String := ""
  /-- Lines of code: the lines the spot's own steps span, without the nested
  blocks, the comments and the blank lines. -/
  loc : Nat := 0
  deriving Inhabited

def Spot.isIdeal (spot : Spot) : Bool := spot.steps.all (·.verdict.isIdeal)

/-- The `<;>` combinator applies its right-hand side to every goal its left-hand
side leaves: the two sides belong to the same straight-line block, and are
scored as two steps of it. -/
partial def explode (stx : Syntax) : Array Syntax :=
  if lastComponent stx.getKind == "tactic_<;>_" then
    (explode stx[0]) ++ (explode stx[2])
  else #[stx]

/-- The tactic blocks nested in a step: the bodies of `·`, `next`, `case`, of
the alternatives of `induction`/`cases`, …  A `by` inside a term is *not* one of
them: a term-level proof belongs to the step that carries it. -/
partial def subBlocks (stx : Syntax) : Array (Array Syntax) :=
  if stx.getKind == ``Lean.Parser.Term.byTactic then #[]
  else if isTacticSeq stx then #[seqSteps stx]
  else if inlineTactics.contains (firstAtom stx) then #[]
  else stx.getArgs.flatMap subBlocks

/-- Everything needed to judge one step of a proof. -/
structure Context where
  input : String
  fileMap : FileMap
  resolver : Resolver

/-- Scan a step for separation-logic vocabulary, skipping the nested blocks,
which are scored on their own. -/
partial def scanStep (r : Resolver) (stx : Syntax) : Option String :=
  if stx.getKind == ``Lean.Parser.Term.byTactic then
    stx.getArgs.findSome? (syntaxMentionsSL r)
  else if isTacticSeq stx then none
  else if inlineTactics.contains (firstAtom stx) then
    stx.getArgs.findSome? (syntaxMentionsSL r)
  else match stx with
    | .node _ _ args => args.findSome? (scanStep r)
    | other => syntaxMentionsSL r other

partial def syntaxAfterAtom? (wanted : String) (stx : Syntax) : Option Syntax :=
  match stx with
  | .node _ _ args =>
    let direct := Id.run do
      for i in [0:args.size] do
        if let .atom _ value := args[i]! then
          if value.trimAscii.toString == wanted then
            return args[i + 1]?
      return none
    direct.orElse fun _ => args.findSome? (syntaxAfterAtom? wanted)
  | _ => none

def explicitStepTheorem? (stx : Syntax) : Option Name := do
  guard (firstAtom stx == "sl_step")
  let term ← syntaxAfterAtom? "with" stx
  let ident ← syntaxFind? term (·.isIdent)
  return ident.getId

def Context.stepText (ctx : Context) (stx : Syntax) : String := Id.run do
  let some ⟨start, stop⟩ := stx.getRange? | return ""
  let text : String := (String.Pos.Raw.extract ctx.input start stop).trimAscii.toString
  let firstLine : String := toString ((text.splitOn "\n").headD text)
  if firstLine.length > 78 then
    return toString (firstLine.take 75) ++ "…"
  if firstLine.length < text.length then
    return firstLine ++ " …"
  return firstLine

def Context.classify (ctx : Context) (stx : Syntax) : Verdict :=
  let head := firstAtom stx
  if manualTactics.contains head then
    .manual s!"`{head}` steers the separation logic by hand"
  else if let some theoremName := explicitStepTheorem? stx then
    if ctx.resolver.isSL theoremName then
      .manual s!"`sl_step with {theoremName}` names a triple lemma"
    else
      .ideal
  else if idealTactics.contains head then
    .ideal
  else match scanStep ctx.resolver stx with
    | some reason => .manual s!"mentions {reason}"
    | none => .ideal

/-- The leaves of a piece of syntax, in source order, each with the class it is
highlighted with.  Only what the parser consumed is kept, so the comments — which
are trivia — never reach the report. -/
partial def leafTokens (r : Resolver) (stx : Syntax) : Array Token :=
  match stx with
  | .node _ _ args => args.flatMap (leafTokens r)
  | .atom _ val =>
    match stx.getRange? with
    | none => #[]
    | some ⟨start, stop⟩ =>
      let val := val.trimAscii.toString
      let cls :=
        if slAtoms.contains val then "sl"
        else match val.toList.head? with
          | none => "op"
          | some c =>
            if c == '"' then "str"
            else if c.isDigit then "lit"
            else if c.isAlpha || c == '_' then "kw"
            else "op"
      #[{ start, stop, cls }]
  | .ident _ _ n _ =>
    match stx.getRange? with
    | none => #[]
    | some ⟨start, stop⟩ => #[{ start, stop, cls := if r.isSL n then "sl" else "id" }]
  | .missing => #[]

def Context.mkStep (ctx : Context) (stx : Syntax) : Step :=
  let ⟨start, stop⟩ := stx.getRange?.getD ⟨0, 0⟩
  let holes := (subBlocks stx).filterMap fun block => do
    let first ← block[0]?
    let last ← block.back?
    let ⟨start, _⟩ ← first.getRange?
    let ⟨_, stop⟩ ← last.getRange?
    return (start, stop)
  { line := ctx.fileMap.toPosition (stx.getPos?.getD 0) |>.line
    text := ctx.stepText stx
    verdict := ctx.classify stx
    start, stop, holes
    tokens := (leafTokens ctx.resolver stx).filter fun tok =>
      !holes.any fun (from', to') => from' ≤ tok.start && tok.stop ≤ to' }

/-! ## The code of a spot, highlighted

Rendering walks the tokens the parser produced rather than the source text: what
lies between two tokens is whitespace and comments, of which only the line
breaks are kept.  The nested blocks are elided, since they are spots of their
own. -/

def escapeHtml (s : String) : String :=
  s |>.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

/-- One line of the rendered code. -/
structure RenderedLine where
  lineNo : Nat
  /-- Indentation, in columns, before the first token of the line. -/
  indent : Nat := 0
  html : String := ""
  /-- Whether a token or an elision was emitted on this line. -/
  content : Bool := false
  /-- Whether a step the score holds against the spot reaches this line. -/
  manual : Bool := false
  deriving Inhabited

structure Renderer where
  lines : Array RenderedLine := #[]
  cur : RenderedLine
  /-- Whitespace waiting to be written, so that what a skipped comment leaves
  behind does not become trailing space. -/
  pending : Nat := 0
  deriving Inhabited

def Renderer.newline (r : Renderer) : Renderer :=
  { lines := r.lines.push r.cur, cur := { lineNo := r.cur.lineNo + 1 }, pending := 0 }

def Renderer.space (r : Renderer) : Renderer := { r with pending := r.pending + 1 }

def Renderer.fragment (r : Renderer) (html : String) (manual : Bool) : Renderer :=
  let r := if r.cur.content then { r with cur.html := r.cur.html ++ "".pushn ' ' r.pending }
    else { r with cur.indent := r.cur.indent + r.pending }
  { r with pending := 0, cur.html := r.cur.html ++ html, cur.content := true
           cur.manual := r.cur.manual || manual }

/-- Put back on the previous line what a line break separated from it: an
elision belongs to the line of the branch it stands for. -/
def Renderer.rejoin (r : Renderer) : Renderer :=
  if r.cur.content then r
  else match r.lines.back? with
    | none => r
    | some last => { lines := r.lines.pop, cur := last, pending := 1 }

def Renderer.finish (r : Renderer) : Renderer :=
  { r with lines := r.lines.push r.cur, cur := { lineNo := r.cur.lineNo + 1 } }

/-- Emit what lies between two tokens: the line breaks, the indentation, and the
code the tactic's own syntax tree does not contain — `<;>`, `;` — but none of
the comments. -/
def Context.gap (ctx : Context) (r : Renderer) (from' to' : String.Pos.Raw)
    (manual : Bool) : Renderer := Id.run do
  let text := (String.Pos.Raw.extract ctx.input from' to').toList.toArray
  let mut r := r
  let mut buf := ""
  let mut i := 0
  let mut depth := 0      -- nesting of `/- … -/`
  let mut lineComment := false
  while h : i < text.size do
    let c := text[i]
    let next? := text[i + 1]?
    let flush := !buf.isEmpty
    if lineComment then
      if c == '\n' then lineComment := false; r := r.newline
      i := i + 1
    else if depth > 0 then
      if c == '-' && next? == some '/' then depth := depth - 1; i := i + 2
      else if c == '/' && next? == some '-' then depth := depth + 1; i := i + 2
      else
        if c == '\n' then r := r.newline
        i := i + 1
    else if c == '-' && next? == some '-' then
      lineComment := true; i := i + 2
    else if c == '/' && next? == some '-' then
      depth := depth + 1; i := i + 2
    else if c.isWhitespace then
      if flush then r := r.fragment s!"<span class='op'>{escapeHtml buf}</span>" manual
      buf := ""
      r := if c == '\n' then r.newline else r.space
      i := i + 1
    else
      buf := buf.push c
      i := i + 1
  unless buf.isEmpty do
    r := r.fragment s!"<span class='op'>{escapeHtml buf}</span>" manual
  return r

/-- The code of a spot: its steps, with the nested blocks elided. -/
def Context.renderSpot (ctx : Context) (steps : Array Step) : String × Nat := Id.run do
  let some first := steps[0]? | return ("", 0)
  let mut r : Renderer :=
    { cur := { lineNo := (ctx.fileMap.toPosition first.start).line
               indent := (ctx.fileMap.toPosition first.start).column } }
  let mut pos := first.start
  for step in steps do
    let manual := !step.verdict.isIdeal
    r := ctx.gap r pos step.start manual
    pos := step.start
    -- The tokens and the elisions of this step, in source order.
    let events : Array (String.Pos.Raw × String.Pos.Raw × Option String) :=
      step.tokens.map (fun tok => (tok.start, tok.stop, some tok.cls)) ++
        step.holes.map (fun (from', to') => (from', to', none))
    for (start, stop, cls?) in events.qsort (fun a b => a.1 < b.1) do
      if start < pos then continue
      r := ctx.gap r pos start manual
      r := match cls? with
        | some cls =>
          let text := escapeHtml (String.Pos.Raw.extract ctx.input start stop)
          r.fragment s!"<span class='{cls}'>{text}</span>" manual
        | none => r.rejoin.fragment "<span class='elided'>…</span>" manual
      pos := stop
    r := ctx.gap r pos step.stop manual
    pos := max pos step.stop
  let lines := r.finish.lines.filter (·.content)
  -- A proof given as a term starts at the `:=` that closes the statement, far to
  -- the right of the lines that follow: do not let it set the indentation.
  let lines := match lines[0]?, lines[1:].foldl (fun d line => min d line.indent) 1000 with
    | some first, restIndent => lines.set! 0 { first with indent := min first.indent restIndent }
    | none, _ => lines
  let dedent := lines.foldl (fun d line => min d line.indent) 1000
  let html := String.join <| lines.toList.map fun line =>
    let cls := if line.manual then "line manual" else "line"
    let indent := "".pushn ' ' (line.indent - dedent)
    s!"<div class='{cls}'><span class='lno'>{line.lineNo}</span>\
      <code>{indent}{line.html}</code></div>"
  return (html, lines.size)

def Context.mkSpot (ctx : Context) (steps : Array Step) : Spot :=
  let (html, loc) := ctx.renderSpot steps
  { line := steps[0]?.map (·.line) |>.getD 0, steps, html, loc }

/-- One spot for this block, plus the spots of the blocks nested in it. -/
partial def Context.analyzeBlock (ctx : Context) (steps : Array Syntax) : Array Spot := Id.run do
  let mut here : Array Step := #[]
  let mut nested : Array Spot := #[]
  for step in steps do
    for atomic in explode step do
      here := here.push (ctx.mkStep atomic)
      for block in subBlocks atomic do
        nested := nested ++ ctx.analyzeBlock block
  return #[ctx.mkSpot here] ++ nested

structure Score where
  name : Name
  line : Nat
  spots : Array Spot
  deriving Inhabited

def Score.total (s : Score) : Nat := s.spots.size
def Score.ideal (s : Score) : Nat := s.spots.countP (·.isIdeal)
def Score.isIdeal (s : Score) : Bool := s.spots.all (·.isIdeal)

/-- Score one triple declaration.  A proof given as a term, rather than by a
tactic block, is a single spot. -/
def Context.scoreDecl (ctx : Context) (decl : ParsedDecl) : Score :=
  let spots :=
    match decl.value? >>= fun v => syntaxFind? v (·.getKind == ``Lean.Parser.Term.byTactic) with
    | some byStx => ctx.analyzeBlock (seqSteps byStx[1])
    | none =>
      match decl.value? with
      | some value => #[ctx.mkSpot #[ctx.mkStep value]]
      | none => #[]
  { name := decl.shortName, line := decl.line, spots }

/-! ## Score of a declaration, of a file -/

def Score.loc (s : Score) : Nat := s.spots.foldl (· + ·.loc) 0
def Score.idealLoc (s : Score) : Nat :=
  s.spots.foldl (fun n spot => if spot.isIdeal then n + spot.loc else n) 0

structure FileScore where
  path : System.FilePath
  scores : Array Score
  parseErrors : Array String

def FileScore.spots (f : FileScore) : Nat := f.scores.foldl (· + ·.total) 0
def FileScore.idealSpots (f : FileScore) : Nat := f.scores.foldl (· + ·.ideal) 0
def FileScore.idealProofs (f : FileScore) : Nat := f.scores.countP (·.isIdeal)
def FileScore.nonidealProofs (f : FileScore) : Nat := f.scores.size - f.idealProofs
def FileScore.loc (f : FileScore) : Nat := f.scores.foldl (· + ·.loc) 0
def FileScore.idealLoc (f : FileScore) : Nat := f.scores.foldl (· + ·.idealLoc) 0
def FileScore.nonidealLoc (f : FileScore) : Nat := f.loc - f.idealLoc
def FileScore.idealProofLoc (f : FileScore) : Nat :=
  f.scores.foldl (fun n score => if score.isIdeal then n + score.loc else n) 0
def FileScore.nonidealProofLoc (f : FileScore) : Nat :=
  f.scores.foldl (fun n score => if score.isIdeal then n else n + score.loc) 0
def FileScore.fileName (f : FileScore) : String :=
  f.path.fileName.getD f.path.toString

def scoreFile (imported : NameSet) (file : ParsedFile) : FileScore :=
  let slNames := localSLNames file imported
  let ctx : Context :=
    { input := file.input, fileMap := file.fileMap, resolver := { slNames } }
  { path := file.path
    scores := file.decls.filter isTriple |>.map fun decl =>
      { ctx with resolver.currNamespace := decl.currNamespace
                 resolver.opens := decl.opens }.scoreDecl decl
    parseErrors := file.parseErrors }

/-! ## The report -/

def percent (num den : Nat) : String :=
  if den == 0 then "n/a"
  else
    let permille := (2000 * num + den) / (2 * den)
    s!"{permille / 10}.{permille % 10}%"

def average (total count : Nat) : String :=
  if count == 0 then "n/a"
  else
    let tenths := (20 * total + count) / (2 * count)
    s!"{tenths / 10}.{tenths % 10}"

def codeList (items : Array String) : String :=
  ", ".intercalate (items.toList.map fun i => s!"<code>{escapeHtml i}</code>")

def plural (n : Nat) (one many : String) : String := if n == 1 then one else many

def style : String := "
  :root { --good: #1a7f37; --goodbg: #eaf6ec; --bad: #b3261e; --badbg: #fdecea;
          --line: #d8dee4; --dim: #6e7781; }
  * { box-sizing: border-box; }
  body { margin: 0 auto; padding: 2rem 1.5rem 6rem; max-width: 68rem; color: #1f2328;
         font: 15px/1.6 -apple-system, Segoe UI, Roboto, Helvetica, Arial, sans-serif; }
  h1 { font-size: 1.7rem; margin: 0 0 .5rem; }
  h2 { font-size: 1.25rem; margin: 2.5rem 0 .75rem; padding-bottom: .3rem;
       border-bottom: 1px solid var(--line); }
  p, li { max-width: 60rem; }
  code { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: 92%; }
  table { border-collapse: collapse; margin: .5rem 0 1rem; width: 100%; }
  th, td { border-bottom: 1px solid var(--line); padding: .3rem .6rem; text-align: right; }
  th:first-child, td:first-child { text-align: left; }
  thead th { background: #f6f8fa; }
  thead th.sortable { cursor: pointer; user-select: none; }
  thead th.sortable::after { content: ' ↕'; color: var(--dim); }
  thead th.sortable[aria-sort='ascending']::after { content: ' ↑'; color: inherit; }
  thead th.sortable[aria-sort='descending']::after { content: ' ↓'; color: inherit; }
  thead th.sortable:focus-visible { outline: 2px solid #0969da; outline-offset: -2px; }
  tbody tr.imperfect td:first-child { border-left: 3px solid var(--bad); }
  tbody tr.perfect td:first-child { border-left: 3px solid var(--good); }
  tfoot td { font-weight: 600; background: #f6f8fa; }
  table.summary-table th:nth-child(5), table.summary-table td:nth-child(5),
  table.summary-table th:last-child, table.summary-table td:last-child {
    background: #fff8c5; font-weight: 700;
  }
  .score-example { max-width: 60rem; margin: 1rem 0 1.5rem; padding: .8rem 1rem;
                   border: 1px solid var(--line); border-radius: 8px; }
  .example-proof { margin: .7rem 0; border: 1px solid var(--line); border-radius: 6px;
                   overflow: hidden; }
  .example-spot { padding: .5rem .7rem; border-left: 4px solid var(--good);
                  background: var(--goodbg); }
  .example-spot + .example-spot { border-top: 1px solid var(--line); }
  .example-spot.notideal { border-left-color: var(--bad); background: var(--badbg); }
  .example-spot .spot-label { float: right; margin-left: 1rem; color: var(--good);
                              font-weight: 600; font-family: inherit; }
  .example-spot.notideal .spot-label { color: var(--bad); }
  .example-spot pre { margin: 0; line-height: 1.4; overflow-x: auto; }
  .controls { position: sticky; top: 0; z-index: 2; display: flex; gap: 1.2rem;
              align-items: center; flex-wrap: wrap; margin: 1.5rem 0;
              padding: .7rem 1rem; border: 1px solid var(--line); border-radius: 8px;
              background: #f6f8fa; }
  .controls label { cursor: pointer; }
  details.file { margin: 2rem 0; }
  details.file > summary { cursor: pointer; padding: .35rem 0; font-size: 1.25rem;
                           font-weight: 600; border-bottom: 1px solid var(--line); }
  .decl { border: 1px solid var(--line); border-radius: 8px; margin: .5rem 0;
          padding: .2rem .8rem; }
  .decl > .decl-head { padding: .45rem 0; font-weight: 600; }
  .decl > .decl-head .sub { font-weight: 400; color: var(--dim); }
  .spot { border-radius: 6px; margin: .7rem 0 1rem; padding: .5rem .8rem;
          border-left: 4px solid var(--good); background: var(--goodbg); }
  .spot.notideal { border-left-color: var(--bad); background: var(--badbg); }
  .spot > .head { font-size: .85rem; color: var(--dim); margin-bottom: .4rem; }
  .verdict { font-weight: 600; color: var(--good); }
  .spot.notideal .verdict { color: var(--bad); }
  div.code { padding: .5rem .2rem; overflow-x: auto; background: #fff;
             border: 1px solid var(--line); border-radius: 6px;
             font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
             font-size: 13px; line-height: 1.5; }
  div.code .line { white-space: pre; }
  div.code .line.manual { background: #fbe9e7; }
  div.code .lno { display: inline-block; width: 3.4rem; padding-right: .8rem;
                  text-align: right; color: var(--dim); user-select: none; }
  .kw { color: #8250df; }
  .op { color: #57606a; }
  .id { color: #1f2328; }
  .lit { color: #0550ae; }
  .str { color: #0a3069; }
  .sl { color: #b3261e; font-weight: 600; }
  .elided { color: var(--dim); }
  ul.why { margin: .5rem 0 .2rem; padding-left: 1.2rem; font-size: .9rem; }
  ul.why .lno { color: var(--dim); }
  .warn { border-left: 4px solid #bf8700; background: #fff8e5; padding: .6rem .8rem;
          border-radius: 6px; }
  body[data-filter=ideal] .spot.notideal, body[data-filter=notideal] .spot.ideal,
  body[data-filter=ideal] .decl[data-ideal='0'],
  body[data-filter=notideal] .decl[data-notideal='0'],
  body[data-filter=ideal] details.file[data-ideal='0'],
  body[data-filter=notideal] details.file[data-notideal='0'] { display: none; }
"

def script : String := "
  const body = document.body;
  function apply(filter) {
    body.dataset.filter = filter;
  }
  for (const input of document.querySelectorAll('input[name=filter]'))
    input.addEventListener('change', () => apply(input.value));

  function cellValue(row, column) {
    const text = row.cells[column].textContent.trim();
    const missing = text.toLowerCase() === 'n/a';
    const numeric = /^-?[0-9]+(?:[.][0-9]+)?%?$/.test(text);
    return {
      text,
      missing,
      number: numeric ? Number(text.replace('%', '')) : null
    };
  }
  function sortTable(header, column) {
    const table = header.closest('table');
    const tbody = table.tBodies[0];
    const ascending = header.getAttribute('aria-sort') !== 'ascending';
    for (const other of table.tHead.rows[0].cells)
      other.setAttribute('aria-sort', 'none');
    header.setAttribute('aria-sort', ascending ? 'ascending' : 'descending');
    const rows = Array.from(tbody.rows, (row, order) => ({row, order}));
    rows.sort((left, right) => {
      const a = cellValue(left.row, column);
      const b = cellValue(right.row, column);
      if (a.missing !== b.missing)
        return a.missing ? 1 : -1;
      let result;
      if (a.number !== null && b.number !== null)
        result = a.number - b.number;
      else
        result = a.text.localeCompare(b.text, undefined,
          {numeric: true, sensitivity: 'base'});
      if (result === 0)
        return left.order - right.order;
      return ascending ? result : -result;
    });
    tbody.append(...rows.map(entry => entry.row));
  }
  for (const table of document.querySelectorAll('table')) {
    const headers = table.tHead?.rows[0]?.cells ?? [];
    Array.from(headers).forEach((header, column) => {
      header.classList.add('sortable');
      header.tabIndex = 0;
      header.setAttribute('aria-sort', 'none');
      header.title = 'Sort by this column';
      header.addEventListener('click', () => sortTable(header, column));
      header.addEventListener('keydown', event => {
        if (event.key === 'Enter' || event.key === ' ') {
          event.preventDefault();
          sortTable(header, column);
        }
      });
    });
  }
  function openFileReport(hash) {
    if (!hash) return;
    const target = document.getElementById(decodeURIComponent(hash.slice(1)));
    if (target?.matches('details.file'))
      target.open = true;
  }
  for (const link of document.querySelectorAll(\"a[href^='#']\"))
    link.addEventListener('click', () => openFileReport(link.hash));
  openFileReport(location.hash);
  apply('all');
"

def renderSpot (spot : Spot) : String := Id.run do
  let cls := if spot.isIdeal then "ideal" else "notideal"
  let verdict := if spot.isIdeal then "ideal" else "not ideal"
  let mut out := s!"<div class='spot {cls}'>\
    <div class='head'>Spot at line {spot.line} — <span class='verdict'>{verdict}</span> — \
    {spot.loc} {plural spot.loc "line" "lines"} of code</div>\
    <div class='code'>{spot.html}</div>"
  let manual := spot.steps.filter (!·.verdict.isIdeal)
  unless manual.isEmpty do
    out := out ++ "<ul class='why'>"
    for step in manual do
      let reason := match step.verdict with | .ideal => "" | .manual reason => reason
      out := out ++ s!"<li><span class='lno'>{step.line}</span> \
        <code>{escapeHtml step.text}</code> — {reason}</li>"
    out := out ++ "</ul>"
  return out ++ "</div>"

def renderFile (f : FileScore) : String := Id.run do
  let notIdealSpots := f.spots - f.idealSpots
  let mut out := s!"<details class='file' id='{f.path}' data-ideal='{f.idealSpots}' \
    data-notideal='{notIdealSpots}'><summary><code>{escapeHtml f.fileName}</code></summary>"
  unless f.parseErrors.isEmpty do
    out := out ++ s!"<p class='warn'>{f.parseErrors.size} parse \
      {plural f.parseErrors.size "error" "errors"}: the file defines notation of its own and \
      has not been built, so some of its declarations are missing here \
      ({escapeHtml (", ".intercalate f.parseErrors.toList)}).</p>"
  if f.scores.isEmpty then
    return out ++ "<p>No triple to score in this file.</p></details>"
  out := out ++ "<table><thead><tr><th>Declaration</th><th>Line</th><th>Spots</th>\
    <th>Ideal</th><th>Score</th><th>LOC</th><th>Ideal LOC</th></tr></thead><tbody>"
  for s in f.scores do
    let cls := if s.isIdeal then "perfect" else "imperfect"
    out := out ++ s!"<tr class='{cls}'><td><code>{escapeHtml s.name.toString}</code></td>\
      <td>{s.line}</td><td>{s.total}</td><td>{s.ideal}</td>\
      <td>{percent s.ideal s.total}</td><td>{s.loc}</td><td>{s.idealLoc}</td></tr>"
  out := out ++ s!"</tbody><tfoot><tr><td>{f.idealProofs} of {f.scores.size} proofs ideal \
    throughout</td><td></td><td>{f.spots}</td><td>{f.idealSpots}</td>\
    <td>{percent f.idealSpots f.spots}</td><td>{f.loc}</td><td>{f.idealLoc}</td></tr>\
    </tfoot></table>"
  for s in f.scores do
    let notIdeal := s.total - s.ideal
    out := out ++ s!"<div class='decl' data-ideal='{s.ideal}' \
      data-notideal='{notIdeal}'>\
      <div class='decl-head'><code>{escapeHtml s.name.toString}</code> \
      <span class='sub'>— line {s.line}, {s.ideal}/{s.total} spots ideal, \
      {s.loc} {plural s.loc "line" "lines"} of code</span></div>"
    for spot in s.spots.qsort (·.line < ·.line) do
      out := out ++ renderSpot spot
    out := out ++ "</div>"
  return out ++ "</details>"

def renderReport (files : Array FileScore) : String := Id.run do
  let spots := files.foldl (· + ·.spots) 0
  let idealSpots := files.foldl (· + ·.idealSpots) 0
  let mut out := s!"<!DOCTYPE html>\n<html lang='en'><head><meta charset='utf-8'>\
    <meta name='viewport' content='width=device-width, initial-scale=1'>\
    <title>Ideal separation-logic proof score</title><style>{style}</style></head>\
    <body data-filter='all'><h1>Ideal separation-logic proof score</h1>"
  out := out ++ "<p>Regenerate with <code>lake env lean --run \
    Aeneas/SLPoC/ProofScore.lean</code> from <code>backends/lean</code>.  A <em>spot</em> is one \
    straight-line block of a proof: the block before the first branch, then one per branch body, \
    recursively.  A spot is ideal when it steers the separation logic nowhere by hand — only \
    <code>sl_step</code>, <code>sl_pull</code>, and pure reasoning.  The code below is the \
    spot's own, with the nested blocks elided as <span class='elided'>…</span> because they are \
    spots of their own, and without the comments.  See the module docstring of \
    <code>Aeneas/SLPoC/ProofScore.lean</code> for the details.</p>"
  out := out ++ s!"<h2>Rules</h2><ul>\
    <li>free: {codeList idealTactics}, pure reasoning, and <code>unfold</code> of a program;</li>\
    <li>manual: {codeList manualTactics};</li>\
    <li>manual: any other step mentioning a separation-logic connective \
    ({codeList slAtoms}), a simp set of the automation ({codeList slAttrNames}), or a \
    declaration whose statement is about <code>SLProp</code>.</li></ul>"
  out := out ++ "<div class='score-example'><strong>One branching proof, split into \
    3 spots</strong><div class='example-proof'>\
    <div class='example-spot'><span class='spot-label'>Spot 1 — ideal</span>\
    <pre><code>unfold f\nsl_step*\nsplit</code></pre></div>\
    <div class='example-spot'><span class='spot-label'>Spot 2 — ideal</span>\
    <pre><code>· have h : n = n := rfl\n  simp only [h]\n  sl_step*</code></pre></div>\
    <div class='example-spot notideal'><span class='spot-label'>Spot 3 — not ideal</span>\
    <pre><code>· sl_xchange h\n  sl_step*</code></pre></div></div>\
    The prefix before <code>split</code> is one spot, and each branch is another: \
    <strong>3 spots total</strong>. <strong>Pure reasoning is allowed:</strong> the \
    <code>have</code> and <code>simp</code> in Spot 2 do not lower its score. The manual \
    <code>sl_xchange</code> makes Spot 3 nonideal, giving a spot score of \
    <strong>2 / 3 = 66.7%</strong>; the whole proof is not an ideal proof.</div>"
  out := out ++ "<h2>Summary</h2><table class='summary-table'><thead><tr>\
    <th>File</th><th>Triples</th>\
    <th>Spots</th><th>Ideal spots</th><th>Score</th>\
    <th>Avg Ideal Spot LOC</th><th>Avg Nonideal Spot LOC</th><th>Ideal Proofs</th>\
    <th>Avg Ideal Proof LOC</th><th>Avg Nonideal Proof LOC</th>\
    <th>Avg Proof LOC</th></tr></thead><tbody>"
  let mut proofs := 0
  let mut idealProofs := 0
  let mut idealProofLoc := 0
  let mut nonidealProofLoc := 0
  for f in files do
    out := out ++ s!"<tr><td><a href='#{f.path}'><code>{escapeHtml f.fileName}</code></a></td>\
      <td>{f.scores.size}</td><td>{f.spots}</td><td>{f.idealSpots}</td>\
      <td>{percent f.idealSpots f.spots}</td>\
      <td>{average f.idealLoc f.idealSpots}</td>\
      <td>{average f.nonidealLoc (f.spots - f.idealSpots)}</td>\
      <td>{f.idealProofs}</td>\
      <td>{average f.idealProofLoc f.idealProofs}</td>\
      <td>{average f.nonidealProofLoc f.nonidealProofs}</td>\
      <td>{average f.loc f.scores.size}</td></tr>"
    proofs := proofs + f.scores.size
    idealProofs := idealProofs + f.idealProofs
    idealProofLoc := idealProofLoc + f.idealProofLoc
    nonidealProofLoc := nonidealProofLoc + f.nonidealProofLoc
  out := out ++ s!"</tbody><tfoot><tr><td>Total</td><td>{proofs}</td><td>{spots}</td>\
    <td>{idealSpots}</td><td>{percent idealSpots spots}</td>\
    <td>{average (files.foldl (· + ·.idealLoc) 0) idealSpots}</td>\
    <td>{average (files.foldl (· + ·.nonidealLoc) 0) (spots - idealSpots)}</td>\
    <td>{idealProofs}</td>\
    <td>{average idealProofLoc idealProofs}</td>\
    <td>{average nonidealProofLoc (proofs - idealProofs)}</td>\
    <td>{average (files.foldl (· + ·.loc) 0) proofs}</td>\
    </tr></tfoot></table>"
  out := out ++ s!"<div class='controls'><strong>Show</strong>\
    <label><input type='radio' name='filter' value='all' checked> every spot \
    ({spots})</label>\
    <label><input type='radio' name='filter' value='ideal'> only the ideal ones \
    ({idealSpots})</label>\
    <label><input type='radio' name='filter' value='notideal'> only those that are not \
    ({spots - idealSpots})</label></div>"
  for f in files do
    out := out ++ renderFile f
  return out ++ s!"<script>{script}</script></body></html>\n"

/-! ## Entry point -/

structure Options where
  files : Array System.FilePath := #[]
  out : System.FilePath := "Aeneas/SLPoC/proof-score.html"

def usage : String :=
  "usage: lake env lean --run Aeneas/SLPoC/ProofScore.lean [-o REPORT.html] [FILE.lean …]"

partial def parseArgs (args : List String) (opts : Options := {}) : Except String Options :=
  match args with
  | [] => .ok opts
  | "-o" :: out :: rest => parseArgs rest { opts with out }
  | "--out" :: out :: rest => parseArgs rest { opts with out }
  | "-h" :: _ => .error usage
  | "--help" :: _ => .error usage
  | arg :: rest =>
    if arg.startsWith "-" then .error s!"unknown option `{arg}`\n{usage}"
    else parseArgs rest { opts with files := opts.files.push arg }

def defaultFiles : IO (Array System.FilePath) := do
  let dir : System.FilePath := "Aeneas/SLPoC/Examples"
  let entries ← dir.readDir
  let files := entries.filterMap fun e =>
    if e.fileName.endsWith ".lean" then some e.path else none
  return files.qsort (·.toString < ·.toString)

unsafe def main (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args with
    | .ok opts => pure opts
    | .error msg => IO.eprintln msg; return 1
  initSearchPath (← findSysroot)
  let files ← if opts.files.isEmpty then defaultFiles else pure opts.files
  let env ← importUnion files
  let imported := importedSLNames env
  let mut scores := #[]
  for path in files do
    IO.println s!"scoring {path}"
    let file ← parseFile env path
    scores := scores.push (scoreFile imported file)
  IO.FS.writeFile opts.out (renderReport scores)
  let spots := scores.foldl (· + ·.spots) 0
  let idealSpots := scores.foldl (· + ·.idealSpots) 0
  IO.println s!"{idealSpots}/{spots} spots ideal ({percent idealSpots spots}); \
    wrote {opts.out}"
  return 0

end Aeneas.SLPoC.ProofScore

unsafe def main (args : List String) : IO UInt32 := Aeneas.SLPoC.ProofScore.main args
