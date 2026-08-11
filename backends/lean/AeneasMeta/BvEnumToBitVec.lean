/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Enums

/-!
# Eagerly realizing `bv_decide`'s enum conversion constants

`bv_decide` / `bv_tac` reason about *enum inductives* (parameter-free inductives
whose constructors are all nullary) by lazily synthesising a handful of
auxiliary constants the first time a goal mentions such an enum:

* `<Enum>.enumToBitVec`            — the `Enum → BitVec n` encoding,
* `<Enum>.enumToBitVec_le`         — its range bound,
* `<Enum>.eq_iff_enumToBitVec_eq`  — injectivity as an `↔`.

These are *reserved names* realised per-`.olean` via `realizeConst`. The
realisation is keyed on the enum type alone, so two **sibling** modules (neither
importing the other) that each run `bv_decide` on the same enum will each
realise their own copy. A third module importing both siblings then fails with

```
environment already contains '<Enum>.enumToBitVec'
```

The collision only manifests on the *joint* import — building either sibling
alone succeeds — which makes it an annoying, parallelism-breaking,
order-dependent failure.

The fix is to realise the constants **once, in a common ancestor** module, so
every descendant reuses the single copy. This file provides two ways to do
that ahead of time:

* the `#define_bv_decide_toBitVec <Type>` command, for types you do not own
  (e.g. `PUnit`, or a type from another library);
* the `deriving BvEnumToBitVec` clause, for enums you are defining yourself.

Both eagerly realise all three constants for the given enum in the current
module, turning the lazy per-use realisation into a single deterministic one.
-/

namespace Aeneas

open Lean Meta Elab
open Lean.Elab.Tactic.BVDecide.Frontend.Normalize

/-- Marker class enabling `deriving BvEnumToBitVec` on an enum inductive.

Deriving it (or invoking `#define_bv_decide_toBitVec`) eagerly realises
`bv_decide`'s `enumToBitVec` / `enumToBitVec_le` / `eq_iff_enumToBitVec_eq`
constants for the type in the current module, so that downstream modules reuse
that single copy instead of racing to realise their own (which collides on
joint import). The class itself carries no data; it exists only so the
`deriving` machinery has a name to resolve. -/
class BvEnumToBitVec (α : Sort u) : Prop

/-- Eagerly realise `bv_decide`'s three enum conversion constants
(`enumToBitVec`, `enumToBitVec_le`, `eq_iff_enumToBitVec_eq`) for `declName` in
the current environment. `declName` must be an enum inductive (parameter-free,
all constructors nullary), otherwise the underlying `bv_decide` realisers throw.

Idempotent: if the constants are already present (e.g. realised by an imported
module) the realisers reuse them rather than failing. -/
def realizeBvEnumToBitVec (declName : Name) : CoreM Unit := do
  unless ← isEnumType declName do
    throwError m!"{.ofConstName declName} is not an enum inductive \
      (parameter-free with only nullary constructors); \
      `bv_decide` only synthesises `enumToBitVec` for such types."
  enableRealizationsForConst declName
  let act : MetaM Unit := do
    discard <| getEnumToBitVecFor declName
    discard <| getEnumToBitVecLeFor declName
    discard <| getEqIffEnumToBitVecEqFor declName
  discard <| act.run' {} {}

/-- `#define_bv_decide_toBitVec T` eagerly realises `bv_decide`'s enum
conversion constants for the enum inductive `T` in the current module.

Place it in a module that is a common ancestor of every site that runs
`bv_decide` on `T`; descendants then reuse the single realised copy instead of
each realising their own (which collides on joint import). Use this for types
you do not own (e.g. `PUnit`); for enums you are defining, prefer
`deriving BvEnumToBitVec`. -/
syntax (name := defineBvDecideToBitVec)
  "#define_bv_decide_toBitVec " ident : command

open Lean.Elab.Command in
@[command_elab defineBvDecideToBitVec]
def elabDefineBvDecideToBitVec : CommandElab := fun stx =>
  match stx with
  | `(#define_bv_decide_toBitVec $id:ident) =>
    liftCoreM do
      let declName ← realizeGlobalConstNoOverloadWithInfo id
      realizeBvEnumToBitVec declName
  | _ => throwUnsupportedSyntax

open Lean.Elab.Command in
/-- `deriving` handler for `BvEnumToBitVec`: realises `bv_decide`'s enum
conversion constants for each derived type and registers a marker instance. -/
def mkBvEnumToBitVecInstance (declNames : Array Name) : CommandElabM Bool := do
  for declName in declNames do
    liftCoreM <| realizeBvEnumToBitVec declName
    let typeId := mkIdent declName
    elabCommand (← `(command| instance : BvEnumToBitVec $typeId := ⟨⟩))
  return true

initialize
  registerDerivingHandler ``BvEnumToBitVec mkBvEnumToBitVecInstance

end Aeneas
