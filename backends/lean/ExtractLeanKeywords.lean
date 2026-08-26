import Aeneas

/-!
# Extract Lean keywords

This utility reads the parser token table of the fully-imported `Aeneas`
environment and keeps the identifier-shaped tokens. The result is written to an
OCaml file.
-/

open Lean Parser

/-! ## Config -/

/-- The module whose fully-imported environment we read tokens from. -/
def sourceModule : Name := `Aeneas

/-- Output path for the generated OCaml file (relative to `backends/lean`). -/
def outputFile : System.FilePath := "../../src/extract/LeanKeywords.ml"

/-- Header comment for the generated OCaml file. -/
def ocamlHeader : String :=
"(* Auto-generated. See [backends/lean/ExtractLeanKeywords.lean]. *)
"

/-! ## Extract -/

/-- A string is identifier-shaped if it is a valid Lean identifier atom: an
    `isIdFirst` character followed by `isIdRest` characters. -/
def isIdShaped (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdFirst c && cs.all isIdRest

/-- The identifier-shaped tokens of `env`'s parser token table, sorted. -/
def extractKeywords (env : Environment) : Array String :=
  (getTokenTable env).values.filter isIdShaped
    |>.qsort (fun a b => compare a b matches .lt)

/-! ## Render -/

/-- Render the keywords as an OCaml list literal. -/
def renderOCamlList (keywords : Array String) : String :=
  let entries := String.join (keywords.toList.map (fun k => s!"    \"{k}\";\n"))
  s!"[\n{entries}  ]"

/-- Render the full OCaml file. -/
def renderOCamlFile (keywords : Array String) : String :=
  s!"{ocamlHeader}\nlet lean_keywords : string list =\n  {renderOCamlList keywords}\n"

/-! ## Entry point -/

def main : IO Unit := do
  unsafe Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := sourceModule }] {} 0 (loadExts := true)
  let keywords := extractKeywords env
  IO.FS.writeFile outputFile <| renderOCamlFile keywords
  IO.println s!"Wrote {keywords.size} Lean keywords to {outputFile}"
