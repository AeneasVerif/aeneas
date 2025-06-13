import Lean

namespace Aeneas.Std.ElabScalar

open Lean Elab Command Term Meta

initialize registerTraceClass `ElabScalar

/-!

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

-/

def elabSpecialName (ty : String) (n : Name) : CommandElabM Name := do
  trace[ElabScalar] "elabSpecialName: {n}"
  match n with
  | .anonymous => pure .anonymous
  | .str pre str =>
    trace[ElabScalar] "elabSpecialName: str case: {str}"
    let str := if str == "%S" then ty else str
    pure (.str (← elabSpecialName ty pre) str)
  | .num pre i => pure (.num (← elabSpecialName ty pre) i)

partial def elabSpecial (ty : String) (stx : Syntax) : CommandElabM Syntax := do
  match stx with
  | .missing => pure .missing
  | .node info kind args =>
    let args ← args.mapM (elabSpecial ty)
    pure (.node info kind args)
  | .atom info val => pure (.atom info val)
  | .ident info rawVal val preresolved =>
    let val ← elabSpecialName ty val
    pure (.ident info rawVal val preresolved)

def elabCommand (tys : List String) (cmd : Syntax) : CommandElabM Unit := do
  let elabOne (ty : String) := do
    let cmd ← elabSpecial ty cmd
    trace[ElabScalar] "Final declaration for {ty}:\n{cmd}"
    elabDeclaration cmd
  for ty in tys do
    elabOne ty

syntax (name := uscalarCommand) "uscalar" command : command

@[command_elab uscalarCommand]
def uscalarCommandImpl : CommandElab := fun stx => do
  trace[ElabScalar] "uscalar_command (stx): {stx}"
  match stx with
  | `(uscalarCommand| uscalar $cmd) =>
    elabCommand ["U8", "U16", "U32", "U64", "U128", "Usize"] cmd
  | _ => throwUnsupportedSyntax

syntax (name := iscalarCommand) "iscalar" command : command

@[command_elab iscalarCommand]
def iscalarCommandImpl : CommandElab := fun stx => do
  trace[ElabScalar] "iscalar_command (stx): {stx}"
  match stx with
  | `(iscalarCommand| iscalar $cmd) =>
    elabCommand ["I8", "I16", "I32", "I64", "I128", "Isize"] cmd
  | _ => throwUnsupportedSyntax

syntax (name := scalarCommand) "scalar" command : command

@[command_elab scalarCommand]
def scalarCommandImpl : CommandElab := fun stx => do
  trace[ElabScalar] "scalar_command (stx): {stx}"
  match stx with
  | `(scalarCommand| scalar $cmd) =>
    elabCommand ["U8", "U16", "U32", "U64", "U128", "Usize",
                 "I8", "I16", "I32", "I64", "I128", "Isize"] cmd
  | _ => throwUnsupportedSyntax

end Aeneas.Std.ElabScalar
