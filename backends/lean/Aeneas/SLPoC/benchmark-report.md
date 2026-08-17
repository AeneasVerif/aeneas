# SLPoC benchmark-port report

This report records the eleven sequential, first-order benchmark ports added to
evaluate the SLPoC proof mode. Each Lean module is standalone and follows the
same organization: executable definitions first, then ghost state,
specifications, and proofs.

The ports cover examples from Pulse, Verus-based projects, Creusot, and
Asterinas. They exercise recursive ownership, allocation and deallocation,
indexed cells, aliasing, initialized prefixes, circular layouts, in-place
sorting, cyclic structures, ownership transfer, and recursive trees.

## Scope and interpretation

SLPoC is affine the way Iris is: assertions are closed under heap extension, so
an unused heap resource is simply dropped — `H ⊢ emp` for every `H`. The
specifications below prove functional results and preservation or transfer of
the ownership predicates explicitly present in their postconditions. A triple
alone does not prove a global no-leak property or an exact heap-allocation
delta. Such claims would need a non-affine logic or a separate operational
trace theorem.

Several ports deliberately isolate a first-order sequential kernel from a
larger source development. Each module documents its abstraction boundary.
In particular, the verified vector omits raw allocation and resizing, the
mimalloc model uses two typed cells instead of one byte-addressed block, the
intrusive list omits concurrent metadata-region machinery, and the page table
implements exact-key uniform leaves rather than huge pages.

## Results

All eleven modules compile without `sorry`, `admit`, new axioms, unsafe
definitions, partial definitions, or heartbeat overrides. Independent reviews
of the array-backed, structural, and page-table groups found no substantive
correctness issue after the final fixes.

The proof-score audit preserved every executable definition and theorem
statement. It removed unnecessary manual predicate exposure and terminal
framing, taught automation a small number of representation equalities, and
rephrased pure consequences so that `sl_step` could finish them.

| File | Triples | Spots | Before | After | Ideal-spot gain |
|---|---:|---:|---:|---:|---:|
| `PulseLinkedList.lean` | 15 | 59 | 34 (57.6%) | 48 (81.4%) | +14 |
| `PulseArrayTests.lean` | 15 | 71 | 30 (42.3%) | 60 (84.5%) | +30 |
| `VerusBitmap.lean` | 8 | 36 | 16 (44.4%) | 24 (66.7%) | +8 |
| `PulseResizableVec.lean` | 9 | 17 | 5 (29.4%) | 16 (94.1%) | +11 |
| `PulseRingBuffer.lean` | 9 | 19 | 5 (26.3%) | 18 (94.7%) | +13 |
| `PulseInsertionSort.lean` | 3 | 17 | 10 (58.8%) | 15 (88.2%) | +5 |
| `CreusotListReversalLasso.lean` | 2 | 4 | 3 (75.0%) | 4 (100.0%) | +1 |
| `VerusVerifiedVec.lean` | 7 | 27 | 10 (37.0%) | 25 (92.6%) | +15 |
| `VerusMimallocLinkedList.lean` | 2 | 2 | 0 (0.0%) | 1 (50.0%) | +1 |
| `AsterinasIntrusiveFrameList.lean` | 7 | 13 | 0 (0.0%) | 1 (7.7%) | +1 |
| `VerusPageTable.lean` | 10 | 94 | 18 (19.1%) | 18 (19.1%) | 0 |
| **Total** | **87** | **359** | **131 (36.5%)** | **230 (64.1%)** | **+99** |

The number of completely ideal triple proofs rose from 10 to 52 out of 87.
The detailed spot-by-spot report is generated outside the source tree for this
benchmark set with:

```text
lake env lean --run Aeneas/SLPoC/ProofScore.lean -o REPORT.md FILE.lean ...
```

## Ported files

### `PulseLinkedList.lean`

**Interface.** Nullable links and heap-allocated nodes, with `isEmpty`, `head`,
`pop`, `length`, `create`, `cons`, `append`, `isLastCell`,
`appendAtLastCell`, `detachNext`, `split`, `insert`, `delete`,
`reverseAppend`, and `reverse`.

**Representation and specification.** `isList x xs` recursively owns exactly
the nodes reachable from `x` and relates them to `xs`. The proofs establish
exact observations, ownership-preserving append and split, head-cell
deallocation by `pop`, insertion at the specified split point, and in-place
reversal to `xs.reverse`. The upstream `delete` currently has the insertion
body; the port proves that actual behavior instead of claiming removal.
Wand-based cursors and iterators remain outside this first-order port.

### `PulseArrayTests.lean`

**Interface.** Reusable cell-wise arrays with `alloc`, `free`, `readAt`,
`writeAt`, `fill`, and `compare`, plus recursive cell-level helpers and the
`vecAllocSmoke` allocation/deallocation test.

**Representation and specification.** `ownsCells` relates an ordered pointer
list to an exact logical value list. Allocation returns the requested number
of initialized cells; reads preserve ownership and return exact optional
lookup; writes return the exact bounds test and update only `List.set`; fill
replaces every value; free consumes complete array ownership. Comparison
returns exact list equality while preserving both disjoint arrays. A separate
theorem verifies the actual `compare a a` execution with one ownership
resource, rather than duplicating exclusive ownership.

### `VerusBitmap.lean`

**Interface.** Fixed-width `Word` values, `fromArray`, `getBit`, `setBit`,
`bitmapOr`, and an optional optimized `bitmapOrSelf`.

**Representation and specification.** Words are natural-number masks reduced
modulo `2^64`, and the bitmap owns an array of words. `getBit` returns the
selected Boolean bit. `setBit` preserves the represented length and proves
that precisely the selected bit changes. OR allocates a fresh result with the
same length and proves pointwise Boolean disjunction while preserving both
inputs. Disjoint inputs and exact self-aliasing are proved separately; the
theorem for `bitmapOr bitmap bitmap` verifies the original two-read executable
under one ownership resource.

### `PulseResizableVec.lean`

**Interface.** A bounded vector with `new`, `length`, `capacity`, `hasRoom`,
`get`, `set`, `push`, `pop`, and `free`.

**Representation and specification.** `owns` combines the backing array,
mutable size and capacity cells, and `bufferInv`. The invariant identifies the
logical initialized prefix while deliberately leaving the suffix
unconstrained, matching a pop that does not clear storage. The proofs give
exact bounds results, exact lookup/update behavior, append-or-reject push,
last-element pop, fixed capacity, and complete deallocation. Despite the
source name, this upstream module is bounded and exposes no growth operation.

### `PulseRingBuffer.lean`

**Interface.** Fixed-capacity FIFO operations `new`, `length`, `capacity`,
`isEmpty`, `isFull`, `pushBack`, `popFront`, `peekFront`, and `free`.

**Representation and specification.** `isRingBuffer` owns the backing array
and separate head, tail, and count cells. A circular-layout equation extracts
the logical FIFO list from physical slots. The proofs establish exact
empty/full tests, reject-on-full push, append-at-tail behavior across wrap,
exact front peek and pop, preservation of stale unoccupied slots, and
deallocation of all represented cells. Pop and peek are totalized with
`Option`, unlike the source interface's nonempty precondition.

### `PulseInsertionSort.lean`

**Interface.** In-place `insertCells`, `sortCells`, and public
`insertionSort`.

**Representation and specification.** The inner proof relates cell swaps to
the pure `orderedInsert`; the outer proof relates recursion to
`sortedContents`. The final theorem retains ownership of the original cells,
identifies their exact final contents, proves those contents pairwise sorted,
and proves a permutation of the input. The traversal is right-to-left rather
than Pulse's prefix-growing loop but performs the same insertion-sort step.

### `CreusotListReversalLasso.lean`

**Interface.** `reverseAux` and fuel-bounded `reverse` over an explicit
first-order `Memory` stored in one SLPoC cell.

**Representation and specification.** `Segment`, `Lasso`, and
`ReversalTrace` describe the dynamically followed successor trace. The
recursive theorem proves exact agreement with the pure `rewire` model. The
lasso theorem supplies the exact traversal bound, proves the returned pointer
is the original head, proves the resulting lasso shape with the cycle
reversed, and proves addresses outside the traversal are unchanged.

### `VerusVerifiedVec.lean`

**Interface.** Fixed-capacity `newFixed`, `length`, `capacity`, `readValue`,
and `pushNoResize`.

**Representation and specification.** `owns` partitions backing cells into an
exact initialized prefix and a suffix whose typed markers are all `none`.
Reads observe exact initialized values. Successful push transfers the first
suffix cell into the initialized prefix and appends one logical value; a full
push returns false without change. This is explicitly the post-resize bounded
kernel, not the source's incomplete full vector: raw allocation, contiguity,
layout conversion, deallocation tokens, resizing, and borrow lifetimes are
not modeled.

### `VerusMimallocLinkedList.lean`

**Interface.** Free-list `insertBlock` and `popBlock`.

**Representation and specification.** A source block is represented by a
typed header cell and a separate typed padding/resource cell tied together by
`BlockMeta`. Insertion consumes whole-block ownership, writes the previous
head into the header, and transfers both cells into the free list. Pop returns
the exact first header, preserves the tail list, and returns ownership of both
cells. The model does not claim byte adjacency, provenance, or the allocator's
global page invariants.

### `AsterinasIntrusiveFrameList.lean`

**Interface.** `new`, `cursorFront`, allocation-free `pushFront`,
`takeCurrent`, and `popFront`.

**Representation and specification.** `listRep` recursively owns every
embedded metadata slot and fixes front/back links, list membership, size, and
pure frame order. `detachedFrame` is exclusive ownership of a cleared slot.
Push transfers a detached frame into the exact list head. Cursor removal and
pop repair neighboring links, clear and return the same frame, and preserve
the exact remaining sequence. Typed slots abstract metadata-region address
conversion, atomics, reference counts, and global list-ID allocation.

### `VerusPageTable.lean`

**Interface.** Four-entry tables with `query`, `map`, `remove`, `prune`, and
`unmap`, together with their recursive `*Aux` operations and pure
`ModelTable` counterparts.

**Representation and specification.** `tableOwn` recursively owns each
reachable intermediate table allocation. Query equals exact-key model lookup.
Map equals pure insertion and reports whether insertion occurred. Remove
returns exactly the old final leaf and clears it. Prune frees empty child
tables bottom-up while retaining root ownership. Unmap returns the exact
removed frame and establishes the pure remove-and-prune model. Paths are total
finite lists; the four-level bound is advisory. Early leaves and huge pages
are intentionally not part of this uniform leaf-only subset.

## Why spots remain non-ideal

The score measures proof-mode ergonomics, not theorem strength or
correctness. A spot is non-ideal when any step in one straight-line proof
block manually handles separation logic. One necessary transformation marks
the whole spot non-ideal even if every other command in that block is pure
reasoning or `sl_step`.

The remaining 129 non-ideal spots have these main causes:

1. **Recursive predicate selection and folding.** Automation can often expose
   a predicate at the front of a precondition, but it does not always select,
   transform, or refold a recursive predicate buried among framed resources.
   Linked-list construction, array result predicates, and bitmap result arrays
   still need occasional explicit representation steps.

2. **Result-dependent terminal posts.** After a pure return, the spatial
   postcondition may contain the returned pointer, tuple projection, or a
   representation folded around it. The current `sl_step` result matching
   cannot always use the pure result equality before spatial matching, so a
   consequence or framing step remains necessary.

3. **Buried existentials and pure facts.** `sl_pull` intentionally handles
   common front-facing forms. It does not search beneath arbitrary star
   associations for every existential or pure fact. Some mismatch and
   ownership-transfer branches therefore rearrange or expose assertions
   manually.

4. **Recursive tree navigation.** The page table accounts for 76 of the 129
   remaining non-ideal spots. Its `tableOwn_select`, `tableOwn_unselect`, and
   replacement lemmas move between whole-table ownership and one selected
   slot plus recursively owned siblings. These are entailments rather than
   simplification equalities, so recursive branches require explicit
   `sl_xchange`. This is the clearest high-value target for future proof-mode
   automation.

5. **Local triple composition.** The intrusive-list cursor and public pop
   proofs adapt preconditions and postconditions around calls to
   `takeCurrent`. Current framing inference cannot derive all of these
   conversions automatically, so the proofs use local triples,
   `triple_conseq`, or explicit framing.

6. **Witness choice without a spatial anchor.** Some vector transitions must
   choose an empty prefix or a particular suffix partition. No existing heap
   atom uniquely determines that witness, so a manual entailment is needed.

7. **Conservative scoring.** The scorer charges every mention of a
   separation-logic declaration or connective, including representation
   simplification and a locally stated helper triple. These are useful signals
   that the user still sees the logic, but they are not necessarily difficult
   proof obligations. Spot-level binary scoring also hides partial automation
   within a block.

## Recommended proof-mode work

The first priority is a generic selected-child transformation for recursive
record ownership, aimed at replacing the page table's repeated
select/unselect/replace `sl_xchange` sequence. Next, terminal result matching
should rewrite pure return equalities before matching spatial posts. Finally,
`sl_pull` could gain bounded reassociation/search for pure facts and
existentials, and framing could infer the simple precondition conversions used
by the intrusive cursor wrappers.

Those changes target recurring proof patterns rather than benchmark-specific
lemmas and would improve the score while keeping specifications unchanged.
