import Lean
import Aeneas

/-!
# Summarize an Aeneas formalization project

Reads `translation.json`, filters the Lean environment, and maps every extracted Rust declaration to
spec theorems referencing it.

Usage: `lake exe summarize <translation.json> <Module> [<Module> ...]`
-/

open Lean Meta

namespace AeneasSummary

/-- A spec for a declaration that is not in the monad is usually of the form `ok c ⦃ .. ⦄` or
`lift c ⦃ .. ⦄`, so we peel those to avoid triggering on `Result.ok` or `Std.lift`. -/
partial def peelLift (e : Expr) : Expr :=
  match_expr e with
  | Aeneas.Std.Result.ok _ a => peelLift a
  | Aeneas.Std.lift _ a => peelLift a
  | _ => e

open Aeneas in
/-- The declaration that a statement of the shape `∀ xs, Hs → spec (f args) P` is about. -/
def specTarget? (ty : Expr) : MetaM (Option Name) := do
  try
    let (prog, _) ← Step.getStepSpecFunArgsExpr =<< Utils.normalizeLetBindings ty
    match (peelLift prog).getAppFn with
    | .const c _ => return some c
    | _ => return none
  catch _ =>
    return none

/-- Specs for opaque primitives are sometimes stated as axioms rather than theorems. -/
def isSpecCarrier : ConstantInfo → Bool
  | .thmInfo _ | .axiomInfo _ => true
  | _ => false

/-- One extracted declaration from `translation.json`. -/
structure Decl where
  rustName : String
  leanName : Name
deriving Inhabited

/-- One manifest entry, or `none` if it is not crate-local. -/
def getDecl? (e : Json) : Except String (Option Decl) := do
  unless ← e.getObjValAs? Bool "is_local" do return none
  let rustName ← e.getObjValAs? String "rust_name"
  let leanName ← e.getObjValAs? String "lean_name"
  return some { rustName, leanName := leanName.toName }

/-- The `functions` and `globals` of the manifest. -/
def getDecls (j : Json) : Array Decl := Id.run do
  let mut out : Array Decl := #[]
  for key in ["functions", "globals"] do
    let .ok entries := j.getObjValAs? (Array Json) key | continue
    for e in entries do
      if let .ok (some d) := getDecl? e then
        out := out.push d
  return out

/-- Resolve a `lean_name` to a constant. Aeneas records the name relative to the namespace it was
emitting in, so for hand-written models in `FunsExternal.lean` it can lack the crate prefix. -/
def resolveLeanName? (env : Environment) (crate : Name) (n : Name) : Option Name :=
  if (env.find? n).isSome then
    some n
  else if (env.find? (crate ++ n)).isSome then
    some (crate ++ n)
  else
    none

/-- Map each Rust declaration to the spec theorems about it. This is done using either the fact the
theorem is of `spec` form referencing the Rust declaration, or the name is of the form
`<rust_decl_name>_spec`.
-/
def collect (roots : Array Name) (decls : Array Decl) (crate : Name) :
    MetaM (Std.HashMap String (Array Name)) := do
  let env ← getEnv
  let mut rustNameOf : Std.HashMap Name String := {}
  let mut specs : Std.HashMap String (Array Name) := {}

  for d in decls do
    unless specs.contains d.rustName do
      specs := specs.insert d.rustName #[]
    if let some c := resolveLeanName? env crate d.leanName then
      rustNameOf := rustNameOf.insert c d.rustName

  -- is a spec theorem referencing the rust decl
  for modName in env.header.moduleNames do
    unless roots.any (fun r => r == modName || r.isPrefixOf modName) do continue
    let some idx := env.getModuleIdx? modName | continue
    for c in env.header.moduleData[idx.toNat]!.constNames do
      if c.isInternalDetail then continue
      let some ci := env.find? c | continue
      unless isSpecCarrier ci do continue
      let some tgt ← specTarget? ci.type | continue
      let some rustName := rustNameOf.get? tgt | continue
      specs := specs.insert rustName ((specs.getD rustName #[]).push c)

  -- is named `<rust_decl_name>_spec`
  for d in decls do
    let some c := resolveLeanName? env crate d.leanName | continue
    for suffix in ["_spec", "_spec'"] do
      let cand := c.appendAfter suffix
      if let some ci := env.find? cand then
        if isSpecCarrier ci then
          specs := specs.insert d.rustName ((specs.getD d.rustName #[]).push cand)

  return specs

/-- Where the summary is written, relative to the current directory. -/
def OUT_PATH : System.FilePath := "aeneas-summary.json"

def USAGE : String :=
  "Usage: lake exe summarize <translation.json> <Module> [<Module> ...]\n\
   \n\
   Writes `aeneas-summary.json`, a JSON object mapping each extracted Rust declaration\n\
   to the list of spec theorems about it."

end AeneasSummary

open AeneasSummary in
def main (args : List String) : IO UInt32 := do
  let jsonPath :: rootArg :: restArgs := args | .eprintln USAGE; return 1
  let roots := ((rootArg :: restArgs).map String.toName).toArray

  unsafe Lean.enableInitializersExecution -- needed to read the `@[step]` attribute extension
  Lean.initSearchPath (← Lean.findSysroot)
  let translateJson ← IO.FS.readFile jsonPath
  let .ok j := Json.parse translateJson | .eprintln "JSON parse error"; return 1
  let .ok crate := j.getObjValAs? String "crate" | .eprintln "unexpected JSON shape"; return 1
  let decls := getDecls j

  let env ← importModules (roots.map ({ module := · })) {} (loadExts := true)
  let (result, _) ← (collect roots decls crate.toName).run'.toIO
    -- Not a Lean source file, so there is no `fileName`/`fileMap` to give
    -- `maxHeartbeats := 0` disables the limit
    { fileName := "<AeneasSummary>", fileMap := default, maxHeartbeats := 0 } { env }

  -- A theorem that is both spec-shaped and named `<decl>_spec` is found by both passes.
  let summary := Json.mkObj <| result.toList.map fun (rustName, thms) =>
    (rustName, Json.arr <| thms.sortDedup.map (Json.str ·.toString))
  IO.FS.writeFile OUT_PATH (summary.pretty ++ "\n")

  return 0
