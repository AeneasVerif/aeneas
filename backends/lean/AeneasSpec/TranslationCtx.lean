module

public import AeneasSpec.Item
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Relation

/-!
# What is translated

A `TranslationCtx` is everything Aeneas translates: the items of a crate, the external items they
use, and the dependencies between them (cf. Aeneas's `translated_crate`).

-/

@[expose] public section

namespace Aeneas.Spec

/-- Everything that is translated: the items of the crate together with the external items it
depends on. -/
structure TranslationCtx where
  /-- The name of the crate being translated (cf. Charon's `crate_name`). -/
  crateName : String
  /-- The items. -/
  items : Finset RustItem
  /-- `deps.Adj i j` means that item `i : items` depends on item `j : items`, as the items are
  translated: the signature always counts, the body only if it is present (`transparent`). An item
  whose body is missing has no dependencies coming from that body. A trait declaration does not
  depend on its default methods: they are separate functions, which depend on the trait. -/
  deps : Digraph items

/-- An item belongs to the crate being translated. -/
def TranslationCtx.IsLocal (ctxt : TranslationCtx) (item : RustItem) : Prop :=
  item.crate? = some ctxt.crateName

namespace TranslationCtx

variable (ctxt : TranslationCtx)

/-- `i` and `j` are mutually dependent: each depends, directly or not, on the other. -/
def MutuallyDependent (i j : ctxt.items) : Prop :=
  Relation.TransGen ctxt.deps.Adj i j ∧ Relation.TransGen ctxt.deps.Adj j i

/-- `i` is recursive: it depends, directly or not, on itself. -/
def Recursive (i : ctxt.items) : Prop :=
  Relation.TransGen ctxt.deps.Adj i i

/-- Crate `a` uses crate `b`: an item of `a` depends on an item of the other crate `b`. -/
def CrateDeps (a b : String) : Prop :=
  a ≠ b ∧ ∃ i j : ctxt.items, ctxt.deps.Adj i j ∧ i.val.crate? = some a ∧ j.val.crate? = some b

/-- Aeneas needs to write the item: every item except those already in Aeneas's library. -/
def NeedsWriting (i : ctxt.items) : Prop :=
  i.val.opacity ≠ .external

instance : DecidablePred ctxt.NeedsWriting := fun i =>
  inferInstanceAs (Decidable (i.val.opacity ≠ .external))

/-- Restrictions on dependencies guaranteed by Rust, these are enforced by rustc. -/
structure RustDepRules : Prop where
  /-- Crates do not depend on each other in a cycle. In particular, an item from another crate
  never depends on an item of the crate being translated. -/
  crateAcyclic : ∀ a, ¬ Relation.TransGen ctxt.CrateDeps a a
  -- TODO: supertraits are not cyclic (needs supertrait edges).
  -- TODO: `const`s are not cyclic, `static`s may be (needs `const`/`static` for globals).

/-- Restrictions on dependencies imposed by Aeneas. -/
structure AeneasDepRules : Prop where
  /-- Mutually dependent items have the same kind: for example, a type and a function cannot be
  mutually recursive. -/
  noMixedRecursion : ∀ i j : ctxt.items, ctxt.NeedsWriting i →
    ctxt.MutuallyDependent i j → i.val.kind = j.val.kind
  /-- Globals are not recursive. -/
  noRecursiveGlobals : ∀ i : ctxt.items, ctxt.NeedsWriting i →
    i.val.kind = .globalDecl → ¬ ctxt.Recursive i
  /-- Trait declarations are not recursive. -/
  noRecursiveTraitDecls : ∀ i : ctxt.items, ctxt.NeedsWriting i →
    i.val.kind = .traitDecl → ¬ ctxt.Recursive i
  /-- Trait implementations are not recursive. -/
  noRecursiveTraitImpls : ∀ i : ctxt.items, ctxt.NeedsWriting i →
    i.val.kind = .traitImpl → ¬ ctxt.Recursive i
  /-- Items in Aeneas's library depend only on items in Aeneas's library: whatever depends on an
  item that needs writing needs writing too. -/
  needsWritingOfDep : ∀ i j : ctxt.items, ctxt.deps.Adj i j → ctxt.NeedsWriting j →
    ctxt.NeedsWriting i

/-- The dependencies satisfy both Rust's and Aeneas's restrictions. -/
structure WellFormed : Prop where
  rust : ctxt.RustDepRules
  aeneas : ctxt.AeneasDepRules

end TranslationCtx

end Aeneas.Spec
