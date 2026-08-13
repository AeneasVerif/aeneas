import Lean

/-!
# How close are the separation-logic proofs to the ideal proof?

An engineering tool, not part of the library: it measures how much of the
separation logic the automation still leaves to the user.

Run it from `backends/lean` with

```
lake env lean --run Aeneas/SLPoC/ProofScore.lean [-o REPORT.md] [FILE.lean …]
```

With no file arguments it scores every file of `Aeneas/SLPoC/Examples`, and
writes `Aeneas/SLPoC/proof-score.md`.

## What is measured

The ideal proof of a triple never mentions the separation logic: it unfolds the
program and calls `sl_step*` or the guarded terminal `sl_pure`, with pure
reasoning (`obtain`, `have`, `simp`, …) and `sl_pull` in between, and one such
block per branch of the program:

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
`exact triple_pure …`).  `sl_step`, `sl_step*`, `sl_pure`, and `sl_pull` are
the automation itself and are free; so is any pure reasoning.

Only declarations whose statement is a triple are scored.  The separation-logic
lemmas a development proves on the side (`nodes_snoc`, `nodesFrom_append`, …)
are not scored, but a triple proof that *uses* one is charged for it.

## How it works

The file is parsed with Lean's own parser, using the environment its `import`s
produce, so `⦃ … ⦄`, `sl_step*` and the rest are real syntax nodes rather than
text.  Only the commands that change the scope (`namespace`, `section`, `end`,
`open`, `universe`, `variable`, `set_option`) are elaborated — enough for the
scoped notation of `SepLogic` to parse — and declarations are never elaborated.
Scoring a file therefore costs about a second and works even on a file that
does not compile.
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
    "sl_side?", "step", "step*"]

/-- Tactics that *are* the automation: the ideal proof is made of these. -/
def idealTactics : Array String := #["sl_step", "sl_pure", "sl_pull"]

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

def exprMentionsSL (e : Expr) : Bool :=
  (e.find? fun sub =>
    match sub with
    | .const n _ => slCoreNames.contains (lastComponent n)
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
    if slCoreNames.contains (lastComponent n) || exprMentionsSL info.type then
      names := names.insert n
  return names

/-- The separation-logic declarations of the file itself, which the environment
does not know about when the file is not built (or does not build). -/
def localSLNames (file : ParsedFile) (imported : NameSet) : NameSet := Id.run do
  let mut names := imported
  for decl in file.decls do
    let some sig := decl.signature? | continue
    let r : Resolver :=
      { slNames := imported, currNamespace := decl.currNamespace, opens := decl.opens }
    if (syntaxMentionsSL r sig).isSome then
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

structure Step where
  line : Nat
  text : String
  verdict : Verdict
  deriving Inhabited

structure Spot where
  line : Nat
  steps : Array Step
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
  else if idealTactics.contains head then
    .ideal
  else match scanStep ctx.resolver stx with
    | some reason => .manual s!"mentions {reason}"
    | none => .ideal

def Context.mkStep (ctx : Context) (stx : Syntax) : Step :=
  { line := ctx.fileMap.toPosition (stx.getPos?.getD 0) |>.line
    text := ctx.stepText stx
    verdict := ctx.classify stx }

/-- One spot for this block, plus the spots of the blocks nested in it. -/
partial def Context.analyzeBlock (ctx : Context) (steps : Array Syntax) : Array Spot := Id.run do
  let mut here : Array Step := #[]
  let mut nested : Array Spot := #[]
  for step in steps do
    for atomic in explode step do
      here := here.push (ctx.mkStep atomic)
      for block in subBlocks atomic do
        nested := nested ++ ctx.analyzeBlock block
  let line := here[0]?.map (·.line) |>.getD 0
  return #[{ line, steps := here }] ++ nested

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
      | some value => #[{ line := decl.line, steps := #[ctx.mkStep value] }]
      | none => #[]
  { name := decl.shortName, line := decl.line, spots }

structure FileScore where
  path : System.FilePath
  scores : Array Score
  parseErrors : Array String

def FileScore.spots (f : FileScore) : Nat := f.scores.foldl (· + ·.total) 0
def FileScore.idealSpots (f : FileScore) : Nat := f.scores.foldl (· + ·.ideal) 0
def FileScore.idealProofs (f : FileScore) : Nat := f.scores.countP (·.isIdeal)

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

def escape (s : String) : String := s.replace "|" "\\|"

def codeList (items : Array String) : String :=
  ", ".intercalate (items.toList.map fun i => s!"`{escape i}`")

def renderFile (f : FileScore) : String := Id.run do
  let mut out := s!"## `{f.path}`\n\n"
  unless f.parseErrors.isEmpty do
    out := out ++ s!"⚠ {f.parseErrors.size} parse errors, listed at the end of this section: \
      the file defines notation of its own and has not been built, so some of its \
      declarations are missing here.\n\n"
  if f.scores.isEmpty then
    out := out ++ "No triple to score in this file.\n\n"
  else
    out := out ++ "| Declaration | Line | Spots | Ideal | Score |\n"
    out := out ++ "|---|---:|---:|---:|---:|\n"
    for s in f.scores do
      out := out ++ s!"| `{s.name}` | {s.line} | {s.total} | {s.ideal} | \
        {percent s.ideal s.total} |\n"
    out := out ++ s!"| **Total** | | **{f.spots}** | **{f.idealSpots}** | \
      **{percent f.idealSpots f.spots}** |\n\n"
    out := out ++ s!"{f.idealProofs} of {f.scores.size} proofs are ideal throughout.\n\n"
    out := out ++ "### Proofs, spot by spot\n\n"
    for s in f.scores do
      out := out ++ s!"#### `{s.name}` (line {s.line}) — {s.ideal}/{s.total} spots ideal\n\n"
      for spot in s.spots.qsort (·.line < ·.line) do
        let verdict := if spot.isIdeal then "ideal" else "not ideal"
        out := out ++ s!"Spot at line {spot.line} — {verdict}:\n\n"
        out := out ++ "| Line | Step | Verdict |\n|---:|---|---|\n"
        for step in spot.steps do
          let verdict := match step.verdict with
            | .ideal => "ideal"
            | .manual reason => s!"**manual**: {escape reason}"
          out := out ++ s!"| {step.line} | `{escape step.text}` | {verdict} |\n"
        out := out ++ "\n"
  unless f.parseErrors.isEmpty do
    out := out ++ "### Parse errors\n\n"
    for e in f.parseErrors do
      out := out ++ s!"- {escape e}\n"
    out := out ++ "\n"
  return out

def renderReport (files : Array FileScore) : String := Id.run do
  let mut out := "# Ideal separation-logic proof score\n\n"
  out := out ++ "Regenerate with `lake env lean --run Aeneas/SLPoC/ProofScore.lean` from \
    `backends/lean`.  A *spot* is one straight-line block of a proof: the block before the \
    first branch, then one per branch body, recursively.  A spot is ideal when it steers the \
    separation logic nowhere by hand — only `sl_step`, `sl_pure`, `sl_pull`, and pure reasoning.  See the \
    module docstring of `Aeneas/SLPoC/ProofScore.lean` for the details.\n\n"
  out := out ++ "## Rules\n\n"
  out := out ++ s!"- free: {codeList idealTactics}, pure reasoning, and `unfold` of a \
    program;\n"
  out := out ++ s!"- manual: {codeList manualTactics};\n"
  out := out ++ s!"- manual: any other step mentioning a separation-logic connective \
    ({codeList slAtoms}), a simp set of the automation ({codeList slAttrNames}), or a \
    declaration whose statement is about `SLProp`.\n\n"
  out := out ++ "## Summary\n\n"
  out := out ++ "| File | Triples | Ideal proofs | Spots | Ideal spots | Score |\n"
  out := out ++ "|---|---:|---:|---:|---:|---:|\n"
  let mut spots := 0
  let mut idealSpots := 0
  let mut proofs := 0
  let mut idealProofs := 0
  for f in files do
    out := out ++ s!"| `{f.path}` | {f.scores.size} | {f.idealProofs} | {f.spots} | \
      {f.idealSpots} | {percent f.idealSpots f.spots} |\n"
    spots := spots + f.spots
    idealSpots := idealSpots + f.idealSpots
    proofs := proofs + f.scores.size
    idealProofs := idealProofs + f.idealProofs
  out := out ++ s!"| **Total** | **{proofs}** | **{idealProofs}** | **{spots}** | \
    **{idealSpots}** | **{percent idealSpots spots}** |\n\n"
  for f in files do
    out := out ++ renderFile f
  return out

/-! ## Entry point -/

structure Options where
  files : Array System.FilePath := #[]
  out : System.FilePath := "Aeneas/SLPoC/proof-score.md"

def usage : String :=
  "usage: lake env lean --run Aeneas/SLPoC/ProofScore.lean [-o REPORT.md] [FILE.lean …]"

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
