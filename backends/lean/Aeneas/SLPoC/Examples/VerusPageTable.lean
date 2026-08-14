import Aeneas.SLPoC.Step

/-!
# Verus sequential page-table kernel

This file ports an exact-key, uniform leaf-only subset of the extractable
sequential kernel in
`syswonder/verified-pt` from
`src/imp/paging/pt_exec.rs` (`is_table_empty`, `walk`, `insert`, `remove`,
`prune`, `query`, `map`, and `unmap`) together with the recursive
`PTTreeNode`/`NodeEntry` model from `src/imp/tree/node.rs` (`visit`, `insert`,
`remove`, `prune`, and `path_mappings`).

Every table has four entries.  `maxDepth` and `validPath` describe the intended
four-level architecture subset, but they are advisory: the executable
operations, pure model, and proofs are total for every finite path and therefore
have no implementation-level depth bound.  Mappings exist only at the exact
final key.  An early leaf on a longer path deliberately makes `query` return
`none` and cannot be removed by `unmap`; this differs from upstream huge-page
and aligned-tail removal semantics.  Huge pages, address alignment,
architecture traits, PTE flags/attributes, physical-memory bounds, and
physical-frame ownership tokens are otherwise abstracted.

Unlike an opaque-map encoding, each reachable intermediate table is a distinct
typed SLPoC heap allocation.  The executable code performs pointer reads,
updates, allocation, and `free`; recursive ownership tracks reachable child
tables.  SLPoC triples are affine, however, so these postconditions do not by
themselves establish exact global heap deltas, exact reclamation, or absence of
leaks.  Such claims would require an operational-trace theorem or a non-affine
logic.  Structural recursion on the finite path supplies Lean termination.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace VerusPageTable

/-! # Executable definitions -/

inductive Index where
  | i0 | i1 | i2 | i3
deriving DecidableEq, Repr

abbrev Path := List Index

/-- Advisory substitute for the intended source architecture's finite
`level_count`; it does not bound execution. -/
def maxDepth : Nat := 4

/-- Intended architectural virtual-address subset.  It is advisory: the
executable definitions, model, and proofs remain total at arbitrary finite
path depth. -/
def validPath (path : Path) : Prop :=
  path ≠ [] ∧ path.length ≤ maxDepth

structure Frame where
  base : Nat
deriving DecidableEq, Repr

mutual
  inductive Entry where
    | empty
    | leaf (frame : Frame)
    | table (child : Ptr Table)

  structure Table where
    slot0 : Entry
    slot1 : Entry
    slot2 : Entry
    slot3 : Entry
end

namespace Entry

def isEmpty : Entry → Bool
  | .empty => true
  | _ => false

end Entry

namespace Table

/-- A freshly allocated intermediate page-table page. -/
def empty : Table :=
  ⟨.empty, .empty, .empty, .empty⟩

/-- Read one of the four page-table slots. -/
def get (table : Table) : Index → Entry
  | .i0 => table.slot0
  | .i1 => table.slot1
  | .i2 => table.slot2
  | .i3 => table.slot3

/-- Replace one of the four page-table slots. -/
def set (table : Table) : Index → Entry → Table
  | .i0, entry => { table with slot0 := entry }
  | .i1, entry => { table with slot1 := entry }
  | .i2, entry => { table with slot2 := entry }
  | .i3, entry => { table with slot3 := entry }

/-- The executable form of `is_table_empty`. -/
def isEmpty (table : Table) : Bool :=
  table.slot0.isEmpty && table.slot1.isEmpty &&
    table.slot2.isEmpty && table.slot3.isEmpty

end Table

/-- Follow table pointers and return the leaf at exactly `path`.  Encountering
an empty slot, an early leaf, or a final subtable returns `none`. -/
def queryAux : Ptr Table → Path → St (Option Frame)
  | _, [] => pure none
  | tablePtr, index :: rest => do
      let table ← read tablePtr
      match rest, table.get index with
      | [], .leaf frame => pure (some frame)
      | _ :: _, .table child => do
          let result ← queryAux child rest
          pure result
      | _, _ => pure none

/-- Public exact-path lookup. -/
def query (root : Ptr Table) (path : Path) : St (Option Frame) :=
  queryAux root path

/-- Insertion behavior matching the upstream algorithm within this exact-key,
uniform leaf-only subset.  It allocates absent intermediate tables and returns
`false` without change when a leaf or final slot is already occupied. -/
def mapAux : Ptr Table → Path → Frame → St Bool
  | _, [], _ => pure false
  | tablePtr, index :: rest, frame => do
      let table ← read tablePtr
      match rest, table.get index with
      | [], .empty =>
          update tablePtr (table.set index (.leaf frame))
          pure true
      | [], _ => pure false
      | _ :: _, .table child => do
          let inserted ← mapAux child rest frame
          pure inserted
      | _ :: _, .empty =>
          let child ← alloc Table.empty
          update tablePtr (table.set index (.table child))
          let inserted ← mapAux child rest frame
          pure inserted
      | _ :: _, .leaf _ => pure false

/-- Insert one mapping, creating the missing path of table allocations. -/
def map (root : Ptr Table) (path : Path) (frame : Frame) : St Bool :=
  mapAux root path frame

/-- Clear one leaf only at the exact final key and return the removed frame.
Empty slots, early leaves on longer paths, and final subtables report `none`.
In particular, this intentionally omits upstream huge-page/aligned-tail
removal. -/
def removeAux : Ptr Table → Path → St (Option Frame)
  | _, [] => pure none
  | tablePtr, index :: rest => do
      let table ← read tablePtr
      match rest, table.get index with
      | [], .leaf frame =>
          update tablePtr (table.set index .empty)
          pure (some frame)
      | _ :: _, .table child => do
          let removed ← removeAux child rest
          pure removed
      | _, _ => pure none

/-- Read the source `is_table_empty` test from one table allocation. -/
def isTableEmpty (tablePtr : Ptr Table) : St Bool := do
  let table ← read tablePtr
  pure table.isEmpty

/-- Bottom-up source `prune`.  The result reports whether the current table is
empty; callers use it to free a child, while the public root is never freed. -/
def pruneAux : Ptr Table → Path → St Bool
  | tablePtr, [] => isTableEmpty tablePtr
  | tablePtr, [_] => isTableEmpty tablePtr
  | tablePtr, index :: next :: rest => do
      let table ← read tablePtr
      match table.get index with
      | .table child =>
          let childEmpty ← pruneAux child (next :: rest)
          if childEmpty then
            free child
            let table' := table.set index .empty
            update tablePtr table'
            pure table'.isEmpty
          else
            pure table.isEmpty
      | _ => pure table.isEmpty

/-- Execute bottom-up `free` calls for intermediate tables found empty on
`path`; keep the root. -/
def prune (root : Ptr Table) (path : Path) : St Unit := do
  let _ ← pruneAux root path
  pure ()

/-- Leaf-only `unmap`: remove an exact-key leaf and, only on success, run the
bottom-up empty-table pruning code. -/
def unmap (root : Ptr Table) (path : Path) : St (Option Frame) := do
  let removed ← removeAux root path
  if removed.isSome then
    prune root path
  pure removed

/-! # Ghost state, specifications and proofs -/

mutual
  /-- Pure recursive counterpart of an executable entry. -/
  inductive ModelEntry where
    | empty
    | leaf (frame : Frame)
    | table (child : ModelTable)

  /-- Pure four-way recursive page-table tree, with unbounded finite depth. -/
  structure ModelTable where
    slot0 : ModelEntry
    slot1 : ModelEntry
    slot2 : ModelEntry
    slot3 : ModelEntry
end

namespace ModelEntry

def isEmpty : ModelEntry → Bool
  | .empty => true
  | _ => false

end ModelEntry

namespace ModelTable

def empty : ModelTable :=
  ⟨.empty, .empty, .empty, .empty⟩

def get (table : ModelTable) : Index → ModelEntry
  | .i0 => table.slot0
  | .i1 => table.slot1
  | .i2 => table.slot2
  | .i3 => table.slot3

def set (table : ModelTable) : Index → ModelEntry → ModelTable
  | .i0, entry => { table with slot0 := entry }
  | .i1, entry => { table with slot1 := entry }
  | .i2, entry => { table with slot2 := entry }
  | .i3, entry => { table with slot3 := entry }

def isEmpty (table : ModelTable) : Bool :=
  table.slot0.isEmpty && table.slot1.isEmpty &&
    table.slot2.isEmpty && table.slot3.isEmpty

/-- Pure exact-path lookup, corresponding to `PTTreeNode.visit` ending at a
frame at the full path length. -/
def lookup : ModelTable → Path → Option Frame
  | _, [] => none
  | table, index :: rest =>
      match rest, table.get index with
      | [], .leaf frame => some frame
      | _ :: _, .table child => child.lookup rest
      | _, _ => none

/-- Pure counterpart of source `PTTreeNode.insert`. -/
def insert : ModelTable → Path → Frame → ModelTable × Bool
  | table, [], _ => (table, false)
  | table, index :: rest, frame =>
      match rest, table.get index with
      | [], .empty => (table.set index (.leaf frame), true)
      | [], _ => (table, false)
      | _ :: _, .table child =>
          let (child', inserted) := child.insert rest frame
          (table.set index (.table child'), inserted)
      | _ :: _, .empty =>
          let (child, inserted) := empty.insert rest frame
          (table.set index (.table child), inserted)
      | _ :: _, .leaf _ => (table, false)

/-- Pure counterpart of source `PTTreeNode.remove`, refined to return the
removed frame instead of only `Ok`/`Err`. -/
def remove : ModelTable → Path → ModelTable × Option Frame
  | table, [] => (table, none)
  | table, index :: rest =>
      match rest, table.get index with
      | [], .leaf frame => (table.set index .empty, some frame)
      | _ :: _, .table child =>
          let (child', removed) := child.remove rest
          (table.set index (.table child'), removed)
      | _, _ => (table, none)

/-- Pure counterpart of source `PTTreeNode.prune`; the Boolean says whether
the returned current table is empty. -/
def prune : ModelTable → Path → ModelTable × Bool
  | table, [] => (table, table.isEmpty)
  | table, [_] => (table, table.isEmpty)
  | table, index :: next :: rest =>
      match table.get index with
      | .table child =>
          let (child', childEmpty) := child.prune (next :: rest)
          let table' :=
            if childEmpty then table.set index .empty
            else table.set index (.table child')
          (table', table'.isEmpty)
      | _ => (table, table.isEmpty)

/-- Exact pure model of the high-level source `unmap`. -/
def unmap (table : ModelTable) (path : Path) :
    ModelTable × Option Frame :=
  let (table', removed) := table.remove path
  match removed with
  | none => (table', none)
  | some frame => ((table'.prune path).1, some frame)

theorem prune_result_isEmpty (table : ModelTable) (path : Path) :
    (table.prune path).2 = (table.prune path).1.isEmpty := by
  cases path with
  | nil => rfl
  | cons index rest =>
      cases rest with
      | nil => rfl
      | cons next rest =>
          simp only [prune]
          cases table.get index <;> rfl

end ModelTable

mutual
  /-- Ownership relation for one concrete/model entry pair.  A table entry
recursively owns the separately allocated child table it points to. -/
  def entryOwn : Entry → ModelEntry → SLProp
    | .empty, .empty => emp
    | .leaf concrete, .leaf model => ⌜concrete = model⌝
    | .table child, .table model => tableOwn child model
    | _, _ => ⌜False⌝

  /-- Recursive ownership tracking one table cell and its reachable child
  tables.  Because triples are affine, this predicate describes the resources
  retained by the proof rather than excluding unrelated or leaked cells from
  the global heap. -/
  def tableOwn (pointer : Ptr Table) : ModelTable → SLProp
    | ⟨model0, model1, model2, model3⟩ =>
        hexists fun concrete : Table =>
          iprop(
            pointer ↦ concrete ∗
            entryOwn concrete.slot0 model0 ∗
            entryOwn concrete.slot1 model1 ∗
            entryOwn concrete.slot2 model2 ∗
            entryOwn concrete.slot3 model3)
end

/-- Ownership of the four entries, excluding the table cell itself. -/
def entriesOwn (concrete : Table) (model : ModelTable) : SLProp :=
  iprop(
    entryOwn concrete.slot0 model.slot0 ∗
    entryOwn concrete.slot1 model.slot1 ∗
    entryOwn concrete.slot2 model.slot2 ∗
    entryOwn concrete.slot3 model.slot3)

/-- The unselected three-entry frame used while operating on one slot. -/
def entriesExcept (index : Index) (concrete : Table)
    (model : ModelTable) : SLProp :=
  match index with
  | .i0 =>
      iprop(
        entryOwn concrete.slot1 model.slot1 ∗
        entryOwn concrete.slot2 model.slot2 ∗
        entryOwn concrete.slot3 model.slot3)
  | .i1 =>
      iprop(
        entryOwn concrete.slot0 model.slot0 ∗
        entryOwn concrete.slot2 model.slot2 ∗
        entryOwn concrete.slot3 model.slot3)
  | .i2 =>
      iprop(
        entryOwn concrete.slot0 model.slot0 ∗
        entryOwn concrete.slot1 model.slot1 ∗
        entryOwn concrete.slot3 model.slot3)
  | .i3 =>
      iprop(
        entryOwn concrete.slot0 model.slot0 ∗
        entryOwn concrete.slot1 model.slot1 ∗
        entryOwn concrete.slot2 model.slot2)

/-! ## Ownership fold/unfold lemmas -/

/-- Unfold one recursive table node into its concrete table cell and four
entry resources. -/
theorem tableOwn_unfold (pointer : Ptr Table) (model : ModelTable) :
    tableOwn pointer model ⊢
      hexists fun concrete : Table =>
        iprop(pointer ↦ concrete ∗ entriesOwn concrete model) := by
  cases model
  unfold tableOwn entriesOwn
  sl_frame

/-- Fold a concrete table cell and its four related entries into recursive
ownership. -/
theorem tableOwn_fold (pointer : Ptr Table) (concrete : Table)
    (model : ModelTable) :
    iprop(pointer ↦ concrete ∗ entriesOwn concrete model) ⊢
      tableOwn pointer model := by
  cases model
  unfold tableOwn entriesOwn
  sl_frame

/-- Select one entry while framing the other three. -/
theorem entriesOwn_select (index : Index) (concrete : Table)
    (model : ModelTable) :
    entriesOwn concrete model ⊢
      iprop(
        entryOwn (concrete.get index) (model.get index) ∗
        entriesExcept index concrete model) := by
  cases index <;> unfold entriesOwn entriesExcept Table.get ModelTable.get <;>
    sl_frame

/-- Put an unchanged selected entry back with its three-entry frame. -/
theorem entriesOwn_unselect (index : Index) (concrete : Table)
    (model : ModelTable) :
    iprop(
      entryOwn (concrete.get index) (model.get index) ∗
      entriesExcept index concrete model) ⊢
    entriesOwn concrete model := by
  cases index <;> unfold entriesOwn entriesExcept Table.get ModelTable.get <;>
    sl_frame

/-- Reassemble all four entries after replacing the selected concrete/model
pair. -/
theorem entriesOwn_replace (index : Index) (concrete : Table)
    (model : ModelTable) (newConcrete : Entry) (newModel : ModelEntry) :
    iprop(
      entryOwn newConcrete newModel ∗
      entriesExcept index concrete model) ⊢
    entriesOwn (concrete.set index newConcrete)
      (model.set index newModel) := by
  cases index <;>
    unfold entriesOwn entriesExcept Table.set ModelTable.set <;>
    sl_frame

/-- Slot-oriented unfold lemma used by the executable proofs. -/
theorem tableOwn_select (pointer : Ptr Table) (index : Index)
    (model : ModelTable) :
    tableOwn pointer model ⊢
      hexists fun concrete : Table =>
        iprop(
          pointer ↦ concrete ∗
          entryOwn (concrete.get index) (model.get index) ∗
          entriesExcept index concrete model) := by
  cases model
  unfold tableOwn
  sl_xpull
  refine himpl_hexists_r x ?_
  cases index <;>
    unfold Table.get ModelTable.get entriesExcept <;>
    sl_frame

/-- Fold an unchanged selected slot back into recursive ownership. -/
theorem tableOwn_unselect (pointer : Ptr Table) (index : Index)
    (concrete : Table) (model : ModelTable) :
    iprop(
      pointer ↦ concrete ∗
      entryOwn (concrete.get index) (model.get index) ∗
      entriesExcept index concrete model) ⊢
    tableOwn pointer model := by
  cases model
  unfold tableOwn
  refine himpl_hexists_r concrete ?_
  cases index <;>
    unfold Table.get ModelTable.get entriesExcept <;>
    sl_frame

/-- Fold a table whose selected concrete/model slot was replaced. -/
theorem tableOwn_replace (pointer : Ptr Table) (index : Index)
    (concrete : Table) (model : ModelTable)
    (newConcrete : Entry) (newModel : ModelEntry) :
    iprop(
      pointer ↦ concrete.set index newConcrete ∗
      entryOwn newConcrete newModel ∗
      entriesExcept index concrete model) ⊢
    tableOwn pointer (model.set index newModel) := by
  cases index with
  | i0 =>
      cases model
      unfold tableOwn entriesExcept
      simp only [Table.set, ModelTable.set]
      refine himpl_hexists_r { concrete with slot0 := newConcrete } ?_
      sl_frame
  | i1 =>
      cases model
      unfold tableOwn entriesExcept
      simp only [Table.set, ModelTable.set]
      refine himpl_hexists_r { concrete with slot1 := newConcrete } ?_
      sl_frame
  | i2 =>
      cases model
      unfold tableOwn entriesExcept
      simp only [Table.set, ModelTable.set]
      refine himpl_hexists_r { concrete with slot2 := newConcrete } ?_
      sl_frame
  | i3 =>
      cases model
      unfold tableOwn entriesExcept
      simp only [Table.set, ModelTable.set]
      refine himpl_hexists_r { concrete with slot3 := newConcrete } ?_
      sl_frame

@[simp] theorem Table.set_get (table : Table) (index : Index) :
    table.set index (table.get index) = table := by
  cases index <;> cases table <;> rfl

@[simp] theorem ModelTable.set_get (table : ModelTable) (index : Index) :
    table.set index (table.get index) = table := by
  cases index <;> cases table <;> rfl

@[simp] theorem ModelTable.get_set_same (table : ModelTable)
    (index : Index) (entry : ModelEntry) :
    (table.set index entry).get index = entry := by
  cases index <;> rfl

theorem ModelTable.get_set_of_ne (table : ModelTable)
    (index other : Index) (entry : ModelEntry) (hne : other ≠ index) :
    (table.set index entry).get other = table.get other := by
  cases index <;> cases other <;> simp_all [ModelTable.set, ModelTable.get]

theorem ModelTable.lookup_set_of_ne (table : ModelTable)
    (index other : Index) (entry : ModelEntry) (rest : Path)
    (hne : other ≠ index) :
    (table.set index entry).lookup (other :: rest) =
      table.lookup (other :: rest) := by
  simp only [ModelTable.lookup,
    ModelTable.get_set_of_ne table index other entry hne]

@[simp] theorem ModelTable.lookup_set_empty_same (table : ModelTable)
    (index : Index) (rest : Path) :
    (table.set index .empty).lookup (index :: rest) = none := by
  simp [ModelTable.lookup]

@[simp] theorem ModelTable.lookup_set_table_same (table : ModelTable)
    (index next : Index) (rest : Path) (child : ModelTable) :
    (table.set index (.table child)).lookup (index :: next :: rest) =
      child.lookup (next :: rest) := by
  simp [ModelTable.lookup]

theorem ModelTable.lookup_table_of_get (table : ModelTable)
    (index next : Index) (rest : Path) (child : ModelTable)
    (hget : table.get index = .table child) :
    table.lookup (index :: next :: rest) =
      child.lookup (next :: rest) := by
  simp [ModelTable.lookup, hget]

/-- Replace the selected slot when the new concrete entry is already known to
be the old concrete entry. -/
theorem tableOwn_replace_of_get (pointer : Ptr Table) (index : Index)
    (concrete : Table) (model : ModelTable)
    (newConcrete : Entry) (newModel : ModelEntry)
    (hget : concrete.get index = newConcrete) :
    iprop(
      pointer ↦ concrete ∗
      entryOwn newConcrete newModel ∗
      entriesExcept index concrete model) ⊢
    tableOwn pointer (model.set index newModel) := by
  have hReplace :=
    tableOwn_replace pointer index concrete model newConcrete newModel
  have hset : concrete.set index newConcrete = concrete := by
    rw [← hget, Table.set_get]
  simpa only [hset] using hReplace

/-- Replacing a slot with a frame related to itself needs no additional
spatial resource. -/
theorem tableOwn_replace_leaf (pointer : Ptr Table) (index : Index)
    (concrete : Table) (model : ModelTable) (frame : Frame) :
    iprop(
      pointer ↦ concrete.set index (.leaf frame) ∗
      entriesExcept index concrete model) ⊢
    tableOwn pointer (model.set index (.leaf frame)) := by
  refine himpl_trans
    (Q := iprop(
      pointer ↦ concrete.set index (.leaf frame) ∗
      entryOwn (.leaf frame) (.leaf frame) ∗
      entriesExcept index concrete model)) ?_
    (tableOwn_replace pointer index concrete model _ _)
  · simp only [entryOwn]
    sl_frame

/-- Replacing a slot with empty needs no additional spatial resource. -/
theorem tableOwn_replace_empty (pointer : Ptr Table) (index : Index)
    (concrete : Table) (model : ModelTable) :
    iprop(
      pointer ↦ concrete.set index .empty ∗
      entriesExcept index concrete model) ⊢
    tableOwn pointer (model.set index .empty) := by
  refine himpl_trans
    (Q := iprop(
      pointer ↦ concrete.set index .empty ∗
      entryOwn .empty .empty ∗
      entriesExcept index concrete model)) ?_
    (tableOwn_replace pointer index concrete model _ _)
  · simp only [entryOwn]
    sl_frame

/-- An empty concrete table owns the empty pure tree without owning any child
allocation. -/
theorem empty_tableOwn (pointer : Ptr Table) :
    pointer ↦ Table.empty ⊢ tableOwn pointer ModelTable.empty := by
  refine himpl_trans
    (Q := iprop(
      pointer ↦ Table.empty ∗
      entriesOwn Table.empty ModelTable.empty)) ?_
    (tableOwn_fold pointer Table.empty ModelTable.empty)
  · simp only [entriesOwn, Table.empty, ModelTable.empty, entryOwn]
    sl_frame

/-- Related entries agree on whether they are empty. -/
theorem entryOwn_isEmpty (concrete : Entry) (model : ModelEntry) :
    entryOwn concrete model ⊢
      iprop(
        ⌜concrete.isEmpty = model.isEmpty⌝ ∗
        entryOwn concrete model) := by
  cases concrete <;> cases model <;>
    simp only [entryOwn, Entry.isEmpty, ModelEntry.isEmpty] <;>
    sl_frame

/-- Related table entries compute the same emptiness test. -/
theorem entriesOwn_isEmpty (concrete : Table) (model : ModelTable) :
    entriesOwn concrete model ⊢
      iprop(
        ⌜concrete.isEmpty = model.isEmpty⌝ ∗
        entriesOwn concrete model) := by
  unfold entriesOwn
  sl_xchange (entryOwn_isEmpty concrete.slot0 model.slot0)
  sl_xchange (entryOwn_isEmpty concrete.slot1 model.slot1)
  sl_xchange (entryOwn_isEmpty concrete.slot2 model.slot2)
  sl_xchange (entryOwn_isEmpty concrete.slot3 model.slot3)
  sl_xpull
  simp only [Table.isEmpty, ModelTable.isEmpty, *]
  sl_frame

/-- The same emptiness relation in the slot-oriented decomposition used by
the recursive algorithms. -/
theorem selectedEntries_isEmpty (index : Index) (concrete : Table)
    (model : ModelTable) :
    iprop(
      entryOwn (concrete.get index) (model.get index) ∗
      entriesExcept index concrete model) ⊢
    iprop(
      ⌜concrete.isEmpty = model.isEmpty⌝ ∗
      entryOwn (concrete.get index) (model.get index) ∗
      entriesExcept index concrete model) := by
  cases index <;>
    unfold Table.get ModelTable.get entriesExcept Table.isEmpty
      ModelTable.isEmpty
  all_goals
    simp only
    sl_xchange (entryOwn_isEmpty concrete.slot0 model.slot0)
    sl_xchange (entryOwn_isEmpty concrete.slot1 model.slot1)
    sl_xchange (entryOwn_isEmpty concrete.slot2 model.slot2)
    sl_xchange (entryOwn_isEmpty concrete.slot3 model.slot3)
    sl_xpull
    simp_all
    sl_frame

/-- Emptiness relation after replacing the selected entry while framing the
unchanged three entries. -/
theorem replacedEntries_isEmpty (index : Index) (concrete : Table)
    (model : ModelTable) (newConcrete : Entry) (newModel : ModelEntry) :
    iprop(
      entryOwn newConcrete newModel ∗
      entriesExcept index concrete model) ⊢
    iprop(
      ⌜(concrete.set index newConcrete).isEmpty =
        (model.set index newModel).isEmpty⌝ ∗
      entryOwn newConcrete newModel ∗
      entriesExcept index concrete model) := by
  cases index with
  | i0 =>
      unfold Table.set ModelTable.set entriesExcept Table.isEmpty
        ModelTable.isEmpty
      simp only
      sl_xchange (entryOwn_isEmpty newConcrete newModel)
      sl_xchange (entryOwn_isEmpty concrete.slot1 model.slot1)
      sl_xchange (entryOwn_isEmpty concrete.slot2 model.slot2)
      sl_xchange (entryOwn_isEmpty concrete.slot3 model.slot3)
      sl_xpull
      simp_all
      sl_frame
  | i1 =>
      unfold Table.set ModelTable.set entriesExcept Table.isEmpty
        ModelTable.isEmpty
      simp only
      sl_xchange (entryOwn_isEmpty newConcrete newModel)
      sl_xchange (entryOwn_isEmpty concrete.slot0 model.slot0)
      sl_xchange (entryOwn_isEmpty concrete.slot2 model.slot2)
      sl_xchange (entryOwn_isEmpty concrete.slot3 model.slot3)
      sl_xpull
      simp_all
      sl_frame
  | i2 =>
      unfold Table.set ModelTable.set entriesExcept Table.isEmpty
        ModelTable.isEmpty
      simp only
      sl_xchange (entryOwn_isEmpty newConcrete newModel)
      sl_xchange (entryOwn_isEmpty concrete.slot0 model.slot0)
      sl_xchange (entryOwn_isEmpty concrete.slot1 model.slot1)
      sl_xchange (entryOwn_isEmpty concrete.slot3 model.slot3)
      sl_xpull
      simp_all
      sl_frame
  | i3 =>
      unfold Table.set ModelTable.set entriesExcept Table.isEmpty
        ModelTable.isEmpty
      simp only
      sl_xchange (entryOwn_isEmpty newConcrete newModel)
      sl_xchange (entryOwn_isEmpty concrete.slot0 model.slot0)
      sl_xchange (entryOwn_isEmpty concrete.slot1 model.slot1)
      sl_xchange (entryOwn_isEmpty concrete.slot2 model.slot2)
      sl_xpull
      simp_all
      sl_frame

theorem replacedEntries_isEmpty_of_get (index : Index) (concrete : Table)
    (model : ModelTable) (newConcrete : Entry) (newModel : ModelEntry)
    (hget : concrete.get index = newConcrete) :
    iprop(
      entryOwn newConcrete newModel ∗
      entriesExcept index concrete model) ⊢
    iprop(
      ⌜concrete.isEmpty = (model.set index newModel).isEmpty⌝ ∗
      entryOwn newConcrete newModel ∗
      entriesExcept index concrete model) := by
  have hRelation :=
    replacedEntries_isEmpty index concrete model newConcrete newModel
  have hset : concrete.set index newConcrete = concrete := by
    rw [← hget, Table.set_get]
  simpa only [hset] using hRelation

/-- Move a pure fact in the middle of a spatial assertion to the front so it
can be introduced as an ordinary Lean hypothesis. -/
theorem pure_middle_front (fact : Prop) (left right : SLProp) :
    iprop(left ∗ ⌜fact⌝ ∗ right) ⊢
      iprop(⌜fact⌝ ∗ left ∗ right) := by
  sl_frame

theorem pure_front_middle (fact : Prop) (left right : SLProp) :
    iprop(⌜fact⌝ ∗ left ∗ right) ⊢
      iprop(left ∗ ⌜fact⌝ ∗ right) := by
  sl_frame

/-! ## Exact functional specifications

These triples exactly relate results and reachable ownership to the pure model.
Their affine postconditions do not assert exact global allocation or
reclamation deltas.
-/

/-- Recursive walk/query returns exactly the pure-model lookup and preserves
the complete recursive ownership predicate. -/
@[step]
theorem queryAux.spec (pointer : Ptr Table) (model : ModelTable)
    (path : Path) :
    ⦃ tableOwn pointer model ⦄ queryAux pointer path
      ⦃⇓ result =>
        ⌜result = model.lookup path⌝ ∗
        tableOwn pointer model⦄ := by
  induction path generalizing pointer model with
  | nil =>
      simp only [queryAux, ModelTable.lookup]
      sl_step*
  | cons index rest ih =>
      simp only [queryAux, ModelTable.lookup]
      sl_xchange (tableOwn_select pointer index model)
      sl_pull concrete
      sl_step
      cases rest with
      | nil =>
          cases hConcrete : concrete.get index <;>
            cases hModel : model.get index <;>
            simp only [entryOwn]
          · have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · rename_i concreteFrame modelFrame
            sl_xchange (pure_middle_front (concreteFrame = modelFrame)
              (pointer ↦ concrete) (entriesExcept index concrete model))
            simp only [hstar_hempty_r_eq]
            sl_pull_keep
            rename_i hFrame
            subst concreteFrame
            have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            simp only [eq_self]
            sl_xchange (pure_front_middle True
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_xchange hFold
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame
      | cons next rest =>
          cases hConcrete : concrete.get index <;>
            cases hModel : model.get index <;>
            simp only [entryOwn]
          · have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · rename_i concreteFrame modelFrame
            sl_xchange (pure_middle_front (concreteFrame = modelFrame)
              (pointer ↦ concrete) (entriesExcept index concrete model))
            simp only [hstar_hempty_r_eq]
            sl_pull_keep
            rename_i hFrame
            subst concreteFrame
            have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            simp only [eq_self]
            sl_xchange (pure_front_middle True
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_xchange hFold
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · rename_i child childModel
            sl_step with ih child childModel
            have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame

/-- Public query has the same exact lookup equation. -/
@[step]
theorem query.spec (root : Ptr Table) (model : ModelTable) (path : Path) :
    ⦃ tableOwn root model ⦄ query root path
      ⦃⇓ result =>
        ⌜result = model.lookup path⌝ ∗
        tableOwn root model⦄ := by
  unfold query
  sl_step*

/-- `mapAux` exactly implements pure insertion: its Boolean is the pure
success flag, and recursive ownership tracks every reachable table in the
result, including newly allocated tables on the successful path.  This is not
an exact global heap-delta or leak-freedom theorem. -/
@[step]
theorem mapAux.spec (pointer : Ptr Table) (model : ModelTable)
    (path : Path) (frame : Frame) :
    ⦃ tableOwn pointer model ⦄ mapAux pointer path frame
      ⦃⇓ inserted =>
        ⌜inserted = (model.insert path frame).2⌝ ∗
        tableOwn pointer (model.insert path frame).1⦄ := by
  induction path generalizing pointer model with
  | nil =>
      simp only [mapAux, ModelTable.insert]
      sl_step*
  | cons index rest ih =>
      simp only [mapAux, ModelTable.insert]
      sl_xchange (tableOwn_select pointer index model)
      sl_pull concrete
      sl_step
      cases rest with
      | nil =>
          cases hConcrete : concrete.get index <;>
            cases hModel : model.get index <;>
            simp only [entryOwn]
          · sl_step
            sl_pure
            sl_xchange
              (tableOwn_replace_leaf pointer index concrete model frame)
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame
      | cons next rest =>
          cases hConcrete : concrete.get index <;>
            cases hModel : model.get index <;>
            simp only [entryOwn]
          · sl_step as ⟨ child ⟩
            sl_xchange (empty_tableOwn child)
            sl_step
            sl_step with ih child ModelTable.empty
            sl_pure
            sl_xchange (tableOwn_replace pointer index concrete model
              (.table child)
              (.table (ModelTable.empty.insert (next :: rest) frame).1))
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · rename_i child childModel
            sl_step with ih child childModel
            sl_pure
            sl_xchange (tableOwn_replace_of_get pointer index concrete model
              (.table child)
              (.table (childModel.insert (next :: rest) frame).1)
              hConcrete)
            sl_frame

/-- Public map has the same exact functional specification for the leaf-only
subset. -/
@[step]
theorem map.spec (root : Ptr Table) (model : ModelTable)
    (path : Path) (frame : Frame) :
    ⦃ tableOwn root model ⦄ map root path frame
      ⦃⇓ inserted =>
        ⌜inserted = (model.insert path frame).2⌝ ∗
        tableOwn root (model.insert path frame).1⦄ := by
  unfold map
  sl_step*

/-- Recursive removal returns exactly the removed frame and preserves recursive
ownership related to the pure tree with that final leaf cleared. -/
@[step]
theorem removeAux.spec (pointer : Ptr Table) (model : ModelTable)
    (path : Path) :
    ⦃ tableOwn pointer model ⦄ removeAux pointer path
      ⦃⇓ removed =>
        ⌜removed = (model.remove path).2⌝ ∗
        tableOwn pointer (model.remove path).1⦄ := by
  induction path generalizing pointer model with
  | nil =>
      simp only [removeAux, ModelTable.remove]
      sl_step*
  | cons index rest ih =>
      simp only [removeAux, ModelTable.remove]
      sl_xchange (tableOwn_select pointer index model)
      sl_pull concrete
      sl_step
      cases rest with
      | nil =>
          cases hConcrete : concrete.get index <;>
            cases hModel : model.get index <;>
            simp only [entryOwn]
          · have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · rename_i concreteFrame modelFrame
            sl_xchange (pure_middle_front (concreteFrame = modelFrame)
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_step
            sl_xchange
              (tableOwn_replace_empty pointer index concrete model)
            sl_step*
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame
      | cons next rest =>
          cases hConcrete : concrete.get index <;>
            cases hModel : model.get index <;>
            simp only [entryOwn]
          · have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · rename_i child childModel
            sl_step with ih child childModel
            sl_pure
            sl_xchange (tableOwn_replace_of_get pointer index concrete model
              (.table child)
              (.table (childModel.remove (next :: rest)).1)
              hConcrete)
            sl_frame

/-- The executable table-emptiness scan is exact and preserves the complete
recursive ownership predicate. -/
@[step]
theorem isTableEmpty.spec (pointer : Ptr Table) (model : ModelTable) :
    ⦃ tableOwn pointer model ⦄ isTableEmpty pointer
      ⦃⇓ empty =>
        ⌜empty = model.isEmpty⌝ ∗
        tableOwn pointer model⦄ := by
  unfold isTableEmpty
  sl_xchange (tableOwn_select pointer .i0 model)
  sl_pull concrete
  sl_step
  sl_xchange (selectedEntries_isEmpty .i0 concrete model)
  sl_xchange (pure_middle_front
    (concrete.isEmpty = model.isEmpty)
    (pointer ↦ concrete)
    (iprop(
      entryOwn (concrete.get .i0) (model.get .i0) ∗
      entriesExcept .i0 concrete model)))
  simp only [hstar_hempty_r_eq]
  sl_pull_keep
  rename_i hEmpty
  sl_pure
  sl_xchange (tableOwn_unselect pointer .i0 concrete model)
  simp only [hEmpty]
  sl_frame

theorem Table.eq_empty_of_isEmpty (table : Table)
    (h : table.isEmpty = true) :
    table = Table.empty := by
  cases table with
  | mk slot0 slot1 slot2 slot3 =>
      cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
        simp_all [Table.isEmpty, Entry.isEmpty, Table.empty]

theorem ModelTable.eq_empty_of_isEmpty (table : ModelTable)
    (h : table.isEmpty = true) :
    table = ModelTable.empty := by
  cases table with
  | mk slot0 slot1 slot2 slot3 =>
      cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
        simp_all [ModelTable.isEmpty, ModelEntry.isEmpty, ModelTable.empty]

/-- For a model-empty reachable table, expose that no child ownership remains
and verify the executable `free` of its table cell.  Affineness means this does
not characterize the complete global heap delta. -/
theorem freeModelEmpty.spec (pointer : Ptr Table) (model : ModelTable)
    (hModelEmpty : model.isEmpty = true) :
    ⦃ tableOwn pointer model ⦄ free pointer ⦃⇓ emp⦄ := by
  sl_xchange (tableOwn_select pointer .i0 model)
  sl_pull concrete
  sl_xchange (selectedEntries_isEmpty .i0 concrete model)
  sl_xchange (pure_middle_front
    (concrete.isEmpty = model.isEmpty)
    (pointer ↦ concrete)
    (iprop(
      entryOwn (concrete.get .i0) (model.get .i0) ∗
      entriesExcept .i0 concrete model)))
  simp only [hstar_hempty_r_eq]
  sl_pull hEmpty
  have hConcreteEmpty : concrete.isEmpty = true := by
    rw [hEmpty, hModelEmpty]
  have hConcrete := Table.eq_empty_of_isEmpty concrete hConcreteEmpty
  have hModel := model.eq_empty_of_isEmpty hModelEmpty
  subst concrete
  subst model
  simp only [Table.empty, ModelTable.empty, Table.get, ModelTable.get,
    entriesExcept, entryOwn, hstar_hempty_r_eq]
  sl_step*

/-- `pruneAux` exactly follows the pure bottom-up prune model.  The executable
true branch performs `free`, while the postcondition tracks only children still
reachable in the resulting model.  It does not prove exact reclamation or
exclude leaked/unrelated heap cells. -/
@[step]
theorem pruneAux.spec (pointer : Ptr Table) (model : ModelTable)
    (path : Path) :
    ⦃ tableOwn pointer model ⦄ pruneAux pointer path
      ⦃⇓ empty =>
        ⌜empty = (model.prune path).2⌝ ∗
        tableOwn pointer (model.prune path).1⦄ := by
  induction path generalizing pointer model with
  | nil =>
      simp only [pruneAux, ModelTable.prune]
      sl_step*
  | cons index rest ih =>
      cases rest with
      | nil =>
          simp only [pruneAux, ModelTable.prune]
          sl_step*
      | cons next rest =>
          simp only [pruneAux, ModelTable.prune]
          sl_xchange (tableOwn_select pointer index model)
          sl_pull concrete
          sl_step
          cases hConcrete : concrete.get index <;>
            cases hModel : model.get index <;>
            simp only [entryOwn]
          · have hRelation :=
              selectedEntries_isEmpty index concrete model
            simp only [hConcrete, hModel, entryOwn] at hRelation
            sl_xchange hRelation
            have hFront := pure_middle_front
              (concrete.isEmpty = model.isEmpty)
              (pointer ↦ concrete)
              (iprop(
                entryOwn (concrete.get index) (model.get index) ∗
                entriesExcept index concrete model))
            simp only [hConcrete, hModel, entryOwn] at hFront
            sl_xchange hFront
            simp only [hstar_hempty_r_eq]
            sl_pull_keep
            rename_i hEmpty
            have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            simp only [hEmpty]
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · have hRelation :=
              selectedEntries_isEmpty index concrete model
            simp only [hConcrete, hModel, entryOwn] at hRelation
            sl_xchange hRelation
            have hFront := pure_middle_front
              (concrete.isEmpty = model.isEmpty)
              (pointer ↦ concrete)
              (iprop(
                entryOwn (concrete.get index) (model.get index) ∗
                entriesExcept index concrete model))
            simp only [hConcrete, hModel, entryOwn] at hFront
            sl_xchange hFront
            simp only [hstar_hempty_r_eq]
            sl_pull_keep
            rename_i hEmpty
            have hFold := tableOwn_unselect pointer index concrete model
            simp only [hConcrete, hModel, entryOwn] at hFold
            sl_pure
            sl_xchange hFold
            simp only [hEmpty]
            sl_frame
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · sl_xchange (pure_middle_front False
              (pointer ↦ concrete) (entriesExcept index concrete model))
            sl_pull
            contradiction
          · rename_i child childModel
            sl_step with ih child childModel
            split
            · rename_i hChildEmpty
              let child' :=
                (childModel.prune (next :: rest)).1
              have hPrunedEmpty : child'.isEmpty = true := by
                dsimp [child']
                rw [← ModelTable.prune_result_isEmpty childModel
                  (next :: rest)]
                exact hChildEmpty
              sl_step with freeModelEmpty.spec child child' hPrunedEmpty
              sl_step
              have hRelation := replacedEntries_isEmpty index concrete model
                .empty .empty
              simp only [entryOwn, hstar_hempty_l_eq] at hRelation
              sl_xchange hRelation
              have hFront := pure_middle_front
                ((concrete.set index .empty).isEmpty =
                  (model.set index .empty).isEmpty)
                (pointer ↦ concrete.set index .empty)
                (iprop(
                  entryOwn .empty .empty ∗
                  entriesExcept index concrete model))
              simp only [entryOwn, hstar_hempty_l_eq] at hFront
              sl_xchange hFront
              simp only [hstar_hempty_r_eq]
              sl_pull_keep
              rename_i hParentEmpty
              sl_pure
              sl_xchange
                (tableOwn_replace_empty pointer index concrete model)
              simp_all
              sl_frame
            · rename_i hChildNonempty
              let child' :=
                (childModel.prune (next :: rest)).1
              have hRelation := replacedEntries_isEmpty_of_get index
                concrete model (.table child) (.table child') hConcrete
              sl_xchange hRelation
              sl_xchange (pure_middle_front
                (concrete.isEmpty =
                  (model.set index (.table child')).isEmpty)
                (pointer ↦ concrete)
                (iprop(
                  entryOwn (.table child) (.table child') ∗
                  entriesExcept index concrete model)))
              simp only [hstar_hempty_r_eq]
              sl_pull_keep
              rename_i hParentEmpty
              sl_pure
              sl_xchange (tableOwn_replace_of_get pointer index concrete model
                (.table child) (.table child') hConcrete)
              simp_all [child']
              sl_frame

/-- Public prune keeps recursive ownership of the root and all children
reachable in the pure pruned tree. -/
@[step]
theorem prune.spec (root : Ptr Table) (model : ModelTable) (path : Path) :
    ⦃ tableOwn root model ⦄ prune root path
      ⦃⇓ tableOwn root (model.prune path).1⦄ := by
  unfold prune
  sl_step*

/-- High-level leaf-only unmap returns exactly the exact-key removed frame,
clears that mapping, and retains recursive ownership related to the pure
pruned result. -/
@[step]
theorem unmap.spec (root : Ptr Table) (model : ModelTable) (path : Path) :
    ⦃ tableOwn root model ⦄ unmap root path
      ⦃⇓ removed =>
        ⌜removed = (model.unmap path).2⌝ ∗
        tableOwn root (model.unmap path).1⦄ := by
  unfold unmap ModelTable.unmap
  sl_step with removeAux.spec root model path
  cases hRemove : model.remove path with
  | mk model' removed =>
      cases removed with
      | none =>
          simp only [Option.isSome_none, Bool.false_eq_true,
            ↓reduceIte]
          sl_step*
      | some frame =>
          simp only [Option.isSome_some, ↓reduceIte]
          sl_step
          sl_step*

/-! ## Pure functional consequences -/

theorem ModelTable.lookup_cons_cons (table : ModelTable)
    (index next : Index) (rest : Path) :
    table.lookup (index :: next :: rest) =
      match table.get index with
      | .table child => child.lookup (next :: rest)
      | _ => none := by
  cases hEntry : table.get index <;>
    simp [ModelTable.lookup, hEntry]

theorem ModelTable.remove_cons_cons (table : ModelTable)
    (index next : Index) (rest : Path) :
    table.remove (index :: next :: rest) =
      match table.get index with
      | .table child =>
          let (child', removed) := child.remove (next :: rest)
          (table.set index (.table child'), removed)
      | _ => (table, none) := by
  cases hEntry : table.get index <;>
    simp [ModelTable.remove, hEntry]

/-- Pure remove returns exactly the mapping visible at the target path. -/
theorem ModelTable.remove_result_eq_lookup (table : ModelTable)
    (path : Path) :
    (table.remove path).2 = table.lookup path := by
  induction path generalizing table with
  | nil => rfl
  | cons index rest ih =>
      cases rest with
      | nil =>
          cases hEntry : table.get index <;>
            simp [ModelTable.remove, ModelTable.lookup, hEntry]
      | cons next rest =>
          rw [ModelTable.remove_cons_cons,
            ModelTable.lookup_cons_cons]
          cases hEntry : table.get index with
          | empty => rfl
          | leaf frame => rfl
          | table child =>
              exact ih child

/-- Pure remove clears the exact target lookup. -/
theorem ModelTable.remove_clears_lookup (table : ModelTable)
    (path : Path) :
    (table.remove path).1.lookup path = none := by
  induction path generalizing table with
  | nil => rfl
  | cons index rest ih =>
      cases rest with
      | nil =>
          cases hEntry : table.get index <;>
            simp [ModelTable.remove, ModelTable.lookup, hEntry]
      | cons next rest =>
          rw [ModelTable.remove_cons_cons]
          cases hEntry : table.get index with
          | empty =>
              rw [ModelTable.lookup_cons_cons]
              simp only [hEntry]
          | leaf frame =>
              rw [ModelTable.lookup_cons_cons]
              simp only [hEntry]
          | table child =>
              rw [ModelTable.lookup_set_table_same]
              exact ih child

@[simp] theorem ModelTable.empty_lookup (path : Path) :
    ModelTable.empty.lookup path = none := by
  cases path with
  | nil => rfl
  | cons index rest =>
      cases index <;>
        simp [ModelTable.lookup, ModelTable.empty, ModelTable.get]

theorem ModelTable.lookup_eq_none_of_isEmpty (table : ModelTable)
    (path : Path) (hEmpty : table.isEmpty = true) :
    table.lookup path = none := by
  rw [table.eq_empty_of_isEmpty hEmpty]
  exact ModelTable.empty_lookup path

/-- Prune changes allocation shape only: every virtual-path mapping is
preserved. -/
theorem ModelTable.prune_preserves_lookup (table : ModelTable)
    (prunePath queryPath : Path) :
    (table.prune prunePath).1.lookup queryPath =
      table.lookup queryPath := by
  induction prunePath generalizing table queryPath with
  | nil => rfl
  | cons index rest ih =>
      cases rest with
      | nil => rfl
      | cons next rest =>
          cases hEntry : table.get index with
          | empty =>
              simp only [ModelTable.prune, hEntry]
          | leaf frame =>
              simp only [ModelTable.prune, hEntry]
          | table child =>
              simp only [ModelTable.prune, hEntry]
              let child' := (child.prune (next :: rest)).1
              by_cases hChildEmpty :
                  (child.prune (next :: rest)).2 = true
              · simp only [hChildEmpty, ↓reduceIte]
                cases queryPath with
                | nil => rfl
                | cons queryIndex queryRest =>
                    by_cases hSame : queryIndex = index
                    · subst queryIndex
                      have hChildModelEmpty : child'.isEmpty = true := by
                        dsimp [child']
                        rw [← ModelTable.prune_result_isEmpty child
                          (next :: rest)]
                        exact hChildEmpty
                      cases queryRest with
                      | nil =>
                          simp only [ModelTable.lookup,
                            ModelTable.get_set_same, hEntry]
                      | cons queryNext queryRest =>
                          have hNone :=
                            child'.lookup_eq_none_of_isEmpty
                              (queryNext :: queryRest) hChildModelEmpty
                          rw [ModelTable.lookup_set_empty_same,
                            ModelTable.lookup_table_of_get table index
                              queryNext queryRest child hEntry]
                          exact hNone.symm.trans
                            (ih child (queryNext :: queryRest))
                    · exact ModelTable.lookup_set_of_ne table index
                        queryIndex .empty queryRest hSame
              · have hChildNonempty :
                    (child.prune (next :: rest)).2 = false := by
                    exact Bool.eq_false_of_not_eq_true hChildEmpty
                simp only [hChildNonempty, Bool.false_eq_true, ↓reduceIte]
                cases queryPath with
                | nil => rfl
                | cons queryIndex queryRest =>
                    by_cases hSame : queryIndex = index
                    · subst queryIndex
                      cases queryRest with
                      | nil =>
                          simp only [ModelTable.lookup,
                            ModelTable.get_set_same, hEntry]
                      | cons queryNext queryRest =>
                          rw [ModelTable.lookup_set_table_same,
                            ModelTable.lookup_table_of_get table index
                              queryNext queryRest child hEntry]
                          exact ih child (queryNext :: queryRest)
                    · exact ModelTable.lookup_set_of_ne table index
                        queryIndex (.table child') queryRest hSame

/-- High-level pure unmap returns the old target mapping and leaves that target
unmapped after pruning. -/
theorem ModelTable.unmap_result_and_clear (table : ModelTable)
    (path : Path) :
    (table.unmap path).2 = table.lookup path ∧
    (table.unmap path).1.lookup path = none := by
  unfold ModelTable.unmap
  cases hRemove : table.remove path with
  | mk table' removed =>
      have hResult := table.remove_result_eq_lookup path
      have hClear := table.remove_clears_lookup path
      simp only [hRemove] at hResult hClear
      cases removed with
      | none =>
          simp only
          exact ⟨hResult, hClear⟩
      | some frame =>
          simp only
          exact ⟨hResult,
            (table'.prune_preserves_lookup path path).trans hClear⟩

end VerusPageTable

end Aeneas.SLPoC
