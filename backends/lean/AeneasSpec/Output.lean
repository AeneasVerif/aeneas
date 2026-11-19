module

public import AeneasSpec.TranslationCtx

/-!
# What Aeneas writes, and what Lean requires of it

## Main definitions

* `Output`: a set of Lean files, each with its imports and its declarations in order.
* `Output.LeanValid`: what Lean requires of the files, independent of how they are chosen.
-/

@[expose] public section

namespace Aeneas.Spec

/-- What Aeneas writes: a set of Lean files, identified by `FileId` (naming the files is a separate
step). Each file has a set of imports, and contains a list of blocks, each a list of items. A block
is a single declaration, or a `mutual` block when it has several items. -/
structure Output (ctxt : TranslationCtx) (FileId : Type*) where
  /-- The files written. -/
  files : Finset FileId
  /-- The files each file imports. -/
  imports : FileId → Finset FileId
  /-- The items written in each file, in order, grouped into blocks. -/
  blocks : FileId → List (List ctxt.items)

namespace Output

variable {ctxt : TranslationCtx} {FileId : Type*} (out : Output ctxt FileId)

/-- File `f` imports file `g` directly. -/
def Imports (f g : FileId) : Prop :=
  g ∈ out.imports f

/-- Item `i` is written in file `f`. -/
def InFile (i : ctxt.items) (f : FileId) : Prop :=
  f ∈ out.files ∧ i ∈ (out.blocks f).flatten

/-- Item `i` is in block number `k` of file `f`. -/
def InBlock (i : ctxt.items) (f : FileId) (k : Nat) : Prop :=
  f ∈ out.files ∧ ∃ h : k < (out.blocks f).length, i ∈ (out.blocks f)[k]

/-- What Lean requires of the written files. -/
structure LeanValid : Prop where
  /-- Files only import files that are written. -/
  imports_subset : ∀ f ∈ out.files, out.imports f ⊆ out.files
  /-- Imports have no cycle: no file imports itself, directly or through other files. -/
  imports_acyclic : ∀ f, ¬ Relation.TransGen out.Imports f f
  /-- Every block has at least one item. -/
  blocks_nonempty : ∀ f ∈ out.files, ∀ b ∈ out.blocks f, b ≠ []
  /-- No item is written twice in a file. -/
  nodup : ∀ f ∈ out.files, (out.blocks f).flatten.Nodup
  /-- No item is written in two files. -/
  unique_file : ∀ i f g, out.InFile i f → out.InFile i g → f = g
  /-- Exactly the items that need writing are written. -/
  complete : ∀ i : ctxt.items, (∃ f, out.InFile i f) ↔ ctxt.NeedsWriting i
  /-- Every dependency is visible: it is in the same file, in the same block or an earlier one, or
  in a file imported directly or through other files (Lean imports are transitive). Dependencies on
  items in Aeneas's library are not constrained: they are not written. -/
  deps_visible : ∀ i j : ctxt.items, ∀ f g k l, out.InBlock i f k → out.InBlock j g l →
    ctxt.deps.Adj i j → (f = g ∧ l ≤ k) ∨ Relation.TransGen out.Imports f g
  /-- Items share a block only if they are mutually dependent: `mutual` blocks are no larger than
  needed. (Mutually dependent items must share a block: this follows from `deps_visible` and
  `imports_acyclic`.) -/
  mutual_exact : ∀ i j : ctxt.items, ∀ f k, out.InBlock i f k → out.InBlock j f k →
    i = j ∨ ctxt.MutuallyDependent i j
  /-- Items in the same block have the same kind: a `mutual` block cannot, for example, mix
  inductive types with definitions. -/
  mutual_same_kind : ∀ i j : ctxt.items, ∀ f k, out.InBlock i f k → out.InBlock j f k →
    i.val.kind = j.val.kind

end Output

end Aeneas.Spec
