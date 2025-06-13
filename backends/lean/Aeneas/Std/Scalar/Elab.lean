import Lean

namespace Aeneas.Std.ScalarElab

open Lean Elab Command Term Meta


initialize registerTraceClass `ScalarElabSubst
initialize registerTraceClass `ScalarElab

/-!

# Generic Scalar Definitions/Theorems
The following defines elaborators to factor out scalar definitions and theorems.
We do this because we often need to write a lot of very similar definitions for
all the scalars kinds. For instance:

```
theorem U8.add_bv_spec {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
  ∃ z, x + y = ok z ∧ (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv :=
  UScalar.add_bv_spec (by scalar_tac)

theorem U16.add_bv_spec {x y : U16} (hmax : x.val + y.val ≤ U16.max) :
  ∃ z, x + y = ok z ∧ (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv :=
  UScalar.add_bv_spec (by scalar_tac)

... -- etc.
```

Instead, we want to write something like this:
```
uscalar theorem «%S».add_bv_spec {x y : «%S»} (hmax : x.val + y.val ≤ «%S».max) :
  ∃ z, x + y = ok z ∧ (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv :=
  UScalar.add_bv_spec (by scalar_tac)
```

and have all the theorems generated at once.

The way we make it work is extremely simple: we simply define a syntax `uscalar command`
which triggers an elaboration by which, for each scalar type, we recursively explore the
syntax of the command, and generate a command where we replaced all the name segments "%S"
with either "U8", or "U16", etc.

# Keywords
- `«%S»`: identifier to be replaced with a scalar name (e.g., `U8`, `U16`, etc.)
- `'S`: string to be replaced with a scalar name (e.g., `Clone'S ~> CloneU8`, etc.)
- `%BitWidth`: term to be replaced with a scalar bitwidth (e.g., `8`, `16`, ..., `System.Platform.numBits`)
- `%Size`: term to be replaced with a size (in bytes)

-/

/- The following contains private definitions copy-pasted from `Lean.Elab.Command` -/
namespace Declaration
  /-- Return `true` if `stx` is a `Command.declaration`, and it is a definition that always has a name. -/
  private def isNamedDef (stx : Syntax) : Bool :=
    if !stx.isOfKind ``Lean.Parser.Command.declaration then
      false
    else
      let decl := stx[1]
      let k := decl.getKind
      k == ``Lean.Parser.Command.abbrev ||
      k == ``Lean.Parser.Command.definition ||
      k == ``Lean.Parser.Command.theorem ||
      k == ``Lean.Parser.Command.opaque ||
      k == ``Lean.Parser.Command.axiom ||
      k == ``Lean.Parser.Command.inductive ||
      k == ``Lean.Parser.Command.classInductive ||
      k == ``Lean.Parser.Command.structure

  /-- Return `true` if `stx` is an `instance` declaration command -/
  private def isInstanceDef (stx : Syntax) : Bool :=
    stx.isOfKind ``Lean.Parser.Command.declaration &&
    stx[1].getKind == ``Lean.Parser.Command.instance

  /-- Return `some name` if `stx` is a definition named `name` -/
  def getDefName? (stx : Syntax) : Option Name := do
    if isNamedDef stx then
      let (id, _) := expandDeclIdCore stx[1][1]
      some id
    else if isInstanceDef stx then
      let optDeclId := stx[1][3]
      if optDeclId.isNone then none
      else
        let (id, _) := expandDeclIdCore optDeclId[0]
        some id
    else
      none
end Declaration

def isSubstring (sub str : List Char) : Option (List Char) :=
  match sub, str with
  | [], _ => some str
  | hd :: sub, hd' :: str =>
    if hd == hd' then isSubstring sub str
    else none
  | _, _ => none

partial def elabString (ty : String) (str : String) : String :=
  let rec replace (str : List Char) :=
    match isSubstring "'S".data str with
    | some str => ty.data ++ replace str
    | none =>
      match str with
      | [] => []
      | c :: str => c :: replace str
  ⟨ replace str.data ⟩

def elabSpecialName (ty : String) (n : Name) : CommandElabM Name := do
  trace[ScalarElabSubst] "elabSpecialName: {n}"
  match n with
  | .anonymous => pure .anonymous
  | .str pre str =>
    trace[ScalarElabSubst] "elabSpecialName: str case: {str}"
    let str := if str == "%S" then ty else elabString ty str
    pure (.str (← elabSpecialName ty pre) str)
  | .num pre i => pure (.num (← elabSpecialName ty pre) i)

def elabSource (info : SourceInfo) : SourceInfo := info
  /-match info with
  | .original _leading pos _trailing endPos =>
    .synthetic pos endPos true
  | _ => info-/

partial def elabSpecial (ty : String) (bw size : Syntax) (stx : Syntax) : CommandElabM Syntax := do
  trace[ScalarElabSubst] "elabSpecial: stx: {stx}"
  match stx with
  | .missing => pure .missing
  -- Special case for %BitWidth
  | .node _ _ #[.atom _ "%BitWidth"] =>
    pure bw
  | .node _ _ #[.atom _ "%Size"] =>
    pure size
  | .node info kind args =>
    trace[ScalarElabSubst] "elabSpecial: node: {stx}"
    let info := elabSource info
    let args ← args.mapM (elabSpecial ty bw size)
    pure (.node info kind args)
  | .atom info val =>
    trace[ScalarElabSubst] "elabSpecial: atom: {val}"
    let info := elabSource info
    if val == "%BitWidth" then
      trace[ScalarElabSubst] "elabSpecial: replaced `%BitWidth`"
      pure bw
    else pure (.atom info val)
  | .ident info rawVal val preresolved =>
    trace[ScalarElabSubst] "elabSpecial: ident: {stx}"
    let info := elabSource info
    let val ← elabSpecialName ty val
    pure (.ident info rawVal val preresolved)

def elabCommand (tysBws : List (String × Syntax × Syntax)) (stx : Syntax) (cmd : TSyntax `command) : CommandElabM Unit := do
  let elabOne (tyBw : String × Syntax × Syntax) : CommandElabM (TSyntax `command) := do
    let (ty, bw, size) := tyBw
    ---let cmd0 := cmd
    let cmd ← elabSpecial ty bw size cmd
    trace[ScalarElab] "Final declaration for {ty}:\n{cmd}"
    let cmd ← liftMacroM (expandNamespacedDeclaration cmd)
    --let cmd : TSyntax `Command := { cmd1 with raw := cmd }
    pure ⟨ cmd ⟩
    /-
    --elabCommandTopLevel cmd
    Command.elabCommand cmd
    --Lean.Elab.Command.elabDeclaration cmd
    /- For some reason, the goto definition doesn't work if the command defines a theorem -/
    trace[ScalarElab] "stx range: {Option.isSome (← Lean.Elab.getDeclarationRange? stx)}"
    trace[ScalarElab] "cmd range: {Option.isSome (← Lean.Elab.getDeclarationRange? cmd0)}"
    --let some range ← Lean.Elab.getDeclarationRange? stx
    -- | throwError "Unreachable"
    /-trace[ScalarElab] "{range.pos}"
    if let some name := Declaration.getDefName? cmd1 then do
      -- Note that the name retrieved from the syntax is not the full name: we still need to resolve it
      if let some e ← liftTermElabM (Term.resolveId? (← `(ident|$(mkIdent name))) (withInfo := true)) then
        let name := e.constName!
        trace[ScalarElab] "Add declaration range for name: {name}"
        addDeclarationRangesFromSyntax name stx[0]
      else throwError "Unreachable"
    else throwError "Unrechable"-/ -/
  --for ty in tys do
  --  elabOne ty
  --
  let cmdl ← tysBws.mapM elabOne
  let cmdl := cmdl.reverse
  match cmdl with
  | cmd :: cmdl =>
    let cmd ← List.foldlM (fun cmd0 cmd1 => `($cmd0:command $cmd1:command)) cmd cmdl
    Command.elabCommand cmd
  | _ => throwError "Unreachable"

scoped syntax "%BitWidth" : term
scoped syntax "%Size" : term

scoped syntax (name := uscalarCommand) "uscalar" command : command

@[command_elab uscalarCommand]
def uscalarCommandImpl : CommandElab := fun stx => do
  trace[ScalarElab] "uscalar_command (stx): {stx}"
  match stx with
  | `(uscalarCommand| uscalar $cmd) =>
    elabCommand [("U8", ←`(8), ←`(1)), ("U16", ←`(16), ←`(2)), ("U32", ←`(32), ←`(4)),
                 ("U64", ←`(64), ←`(8)), ("U128", ←`(128), ←`(16)),
                 ("Usize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))] stx cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := uscalarNoUsizeCommand) "uscalar_no_usize" command : command

@[command_elab uscalarNoUsizeCommand]
def uscalarNoUsizeCommandImpl : CommandElab := fun stx => do
  trace[ScalarElab] "uscalar_no_usize_command (stx): {stx}"
  match stx with
  | `(uscalarNoUsizeCommand| uscalar_no_usize $cmd) =>
    elabCommand [("U8", ←`(8), ←`(1)), ("U16", ←`(16), ←`(2)), ("U32", ←`(32), ←`(4)),
                 ("U64", ←`(64), ←`(8)), ("U128", ←`(128), ←`(16))] stx cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := iscalarCommand) "iscalar" command : command

@[command_elab iscalarCommand]
def iscalarCommandImpl : CommandElab := fun stx => do
  trace[ScalarElab] "iscalar_command (stx): {stx}"
  match stx with
  | `(iscalarCommand| iscalar $cmd) =>
    elabCommand [("I8", ←`(8), ←`(1)), ("I16", ←`(16), ←`(2)), ("I32", ←`(32), ←`(4)),
                 ("I64", ←`(64), ←`(8)), ("I128", ←`(128), ←`(16)),
                 ("Isize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))] stx cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := iscalarNoIsizeCommand) "iscalar_no_isize" command : command

@[command_elab iscalarNoIsizeCommand]
def iscalarNoIsizeNoIsizeCommandImpl : CommandElab := fun stx => do
  trace[ScalarElab] "iscalar_no_usize_command (stx): {stx}"
  match stx with
  | `(iscalarNoIsizeCommand| iscalar_no_isize $cmd) =>
    elabCommand [("I8", ←`(8), ←`(1)), ("I16", ←`(16), ←`(2)), ("I32", ←`(32), ←`(4)),
                 ("I64", ←`(64), ←`(8)), ("I128", ←`(128), ←`(16))] stx cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := scalarCommand) "scalar" command : command

@[command_elab scalarCommand]
def scalarCommandImpl : CommandElab := fun stx => do
  trace[ScalarElab] "scalar_command (stx): {stx}"
  match stx with
  | `(scalarCommand| scalar $cmd) =>
    elabCommand [("U8", ←`(8), ←`(1)), ("U16", ←`(16), ←`(2)), ("U32", ←`(32), ←`(4)),
                 ("U64", ←`(64), ←`(8)), ("U128", ←`(128), ←`(16)),
                 ("Usize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8)),
                 ("I8", ←`(8), ←`(1)), ("I16", ←`(16), ←`(2)), ("I32", ←`(32), ←`(4)),
                 ("I64", ←`(64), ←`(8)), ("I128", ←`(128), ←`(16)),
                 ("Isize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))] stx cmd
  | _ => throwUnsupportedSyntax

end Aeneas.Std.ScalarElab
