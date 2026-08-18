import AeneasMeta.RustSource
import Lean.Server.Requests
import Lean.Server.GoTo

/-! # "Go to Rust definition"

We extend the `textDocument/definition` and `textDocument/hover` LSP requests so that, whenever the
declaration under the cursor carries a `@[rust_source]` attribute the editor also offers to jump to
the Rust item it was extracted from.
-/

open Lean Lsp Server RequestM

namespace Aeneas.RustSource

/-- The range of a Rust item, in LSP coordinates.

`Span` uses the `rustc` conventions (1-based lines, 0-based columns) while LSP counts both from
0. -/
def Span.toLspRange (s : Span) : Range :=
  { start := ⟨s.begLine - 1, s.begCol⟩, «end» := ⟨s.endLine - 1, s.endCol⟩ }

/-- The module in which `declName` was declared, or `none` if it is the module being elaborated. -/
def declModule? (env : Environment) (declName : Name) : Option Name :=
  env.getModuleIdxFor? declName |>.map (env.allImportedModuleNames[·]!)

/-- Compute the path of the Rust file `span` points to, for the declaration `declName`.

The paths stored in the spans are relative to the directory Charon was called from, which
`resolveSpanFile?` locates by looking for the Rust sources around the Lean file the declaration
comes from. -/
def rustFilePath? (env : Environment) (doc : DocumentMeta) (declName : Name) (span : Span) :
    IO (Option System.FilePath) := do
  let mod := declModule? env declName |>.getD doc.mod
  -- `documentUriFromModule?` searches the source search path, which does not necessarily know
  -- about the file currently being edited (it may not even have been saved yet).
  let some uri ← (if mod == doc.mod then pure (some doc.uri) else documentUriFromModule? mod)
    | return none
  let some leanPath := System.Uri.fileUriToPath? uri
    | return none
  let some leanDir := leanPath.parent
    | return none
  resolveSpanFile? env mod leanDir span

/-- If the identifier at `hoverPos` is a constant which was generated from a Rust item, return that
item's file and span, together with the range of the identifier itself.

We read the constant out of the `TermInfo` at the cursor instead of keying off the result of the
underlying go-to-definition request: this way it also works when the cursor is on the declaration
name, whose location link is a binder and carries no `ident?`. -/
def rustSourceAt? (doc : DocumentMeta) (snap : Snapshots.Snapshot) (hoverPos : String.Pos.Raw)
    (includeStop : Bool) :
    IO (Option (System.FilePath × Span × Option Lean.Syntax.Range)) := do
  let some result ← snap.infoTree.hoverableInfoAtM? (m := IO) hoverPos (includeStop := includeStop)
    | return none
  let .ofTermInfo ti := result.info
    | return none
  let .const declName _ := ti.expr.consumeMData
    | return none
  let some span := getSpan? snap.env declName
    | return none
  let some path ← rustFilePath? snap.env doc declName span
    | return none
  return some (path, span, result.info.range?)

initialize
  chainLspRequestHandler
      "textDocument/definition"
      TextDocumentPositionParams
      (Array LeanLocationLink)
      fun params oldTask => do
    let doc ← readDoc
    let text := doc.meta.text
    let hoverPos := text.lspPosToUtf8Pos params.position
    bindRequestTaskCostly oldTask fun oldLinks =>
      withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
        (notFoundX := pure oldLinks) fun snap => do
          let some (path, span, range?) ←
              rustSourceAt? doc.meta snap hoverPos (includeStop := true)
            | return oldLinks
          let targetRange := span.toLspRange
          let link : LeanLocationLink := {
            originSelectionRange? := range?.map (·.toLspRange text)
            targetUri := System.Uri.pathToUri path
            targetRange
            -- Editors scroll to the selection range, and it has to be included in `targetRange`.
            targetSelectionRange := ⟨targetRange.start, targetRange.start⟩
            -- `ident? := none` makes the watchdog forward our URI verbatim, which is what we want
            -- since it does not point to a Lean module.
            ident? := none
            isDefault := false
          }
          return oldLinks.push link

initialize
  chainLspRequestHandler
      "textDocument/hover"
      HoverParams
      (Option Hover)
      fun params oldTask => do
    let doc ← readDoc
    let text := doc.meta.text
    let hoverPos := text.lspPosToUtf8Pos params.position
    bindRequestTaskCostly oldTask fun old =>
      withWaitFindSnap doc (fun s => s.endPos > hoverPos)
        (notFoundX := pure old) fun snap => do
          let some (path, span, range?) ← rustSourceAt? doc.meta snap hoverPos (includeStop := false)
            | return old
          -- Lean renders hovers as Markdown, so a `file://` link is directly navigable: this gives
          -- us the "jump to the Rust source" affordance without needing any client-side support.
          let uri := System.Uri.pathToUri path
          let note :=
            s!"\n\n---\n\nExtracted from `{span.file}`, \
               [lines {span.begLine}:{span.begCol}-{span.endLine}:{span.endCol}]\
               ({uri}#L{span.begLine})"
          match old with
          | some h =>
            return some { h with
              contents := { h.contents with value := h.contents.value ++ note } }
          | none =>
            return some {
              contents := { kind := .markdown, value := note }
              range? := range?.map (·.toLspRange text)
            }

end Aeneas.RustSource
