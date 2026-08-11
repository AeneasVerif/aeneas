# Separation Logic Proof of Concept

This directory contains the proof-of-concept work for extending the separation
logic (SL) support.

## Files

| File | Purpose |
|---|---|
| [`DoublyLinkedList.lean`](DoublyLinkedList.lean) | Port of the Verus doubly-linked-list example: executable definitions, then ghost state, specifications and proofs. |
| [`doubly_linked_loc.py`](doubly_linked_loc.py) | Deterministically regenerates the relevant-LOC comparison with the pinned Verus example below. |
| [`FFree.lean`](FFree.lean) | Defines the generic freer monad, and the state machines that give it an operational semantics (after "Program Logics à la Carte"): `StateMachine`, `Exec`, `Runs` and `Evaluates`. |
| [`Heap.lean`](Heap.lean) | Defines locations, dynamically typed cells, and finite heaps. |
| [`RustHeap.lean`](RustHeap.lean) | The Rust view of the heap: `Ptr` and the pointer operations, over `Heap.lean`. |
| [`SLTactics.lean`](SLTactics.lean) | Port of the SLF tactics: `sl_frame`, `sl_pull`, `sl_xchange`, … |
| [`ST.lean`](ST.lean) | The state monad `St`, its state machine, its denotation `theta` into `Wp`, the Hoare triples, and the specifications of the pointer operations. |
| [`Step.lean`](Step.lean) | Wires the triples into the `step` tactic and provides `sl_frame`. |
| [`StepTests.lean`](StepTests.lean) | Regression tests for `step` and `sl_frame`. |
| [`VerusStd.lean`](VerusStd.lean) | The `vstd` layer: generic sequences of pointer/payload pairs and permission maps over them, with each declaration naming its `vstd` counterpart. Independent of any data structure. |
| [`WP.lean`](WP.lean) | Separation-logic assertions, the magic wand, and the `Wp` monad of predicate transformers. |
| `README.md` | Records the purpose and meaning of files in this directory. |

Keep this table updated whenever a file is added, removed, or repurposed.

## Doubly-linked-list LOC comparison

Run `python3 Aeneas/SLPoC/doubly_linked_loc.py` from `backends/lean` to
regenerate this report, or pass `--check` to verify that it is current. The
script fetches an exact Verus commit and verifies its SHA-256 checksum before
counting. It counts declaration lines and body lines after removing comments,
blank lines, imports/uses, namespaces/modules, standalone delimiters, and
other non-definition scaffolding. Language-level markers such as `by`, `do`,
`proof`, `requires`, `ensures`, `invariant`, and `decreases` are counted.

Verus imports `vstd`, so its sequence, map and permission reasoning costs it no
lines here.  The Lean side has to build that layer, which is why it is kept in
`VerusStd.lean` and reported separately: that module is generic, knows nothing
about doubly-linked lists, and is reusable by any development using the same
"ghost sequence of pointers plus permission map" pattern.  The figure comparable
with Verus is therefore the "Lean example total".

<!-- BEGIN GENERATED DOUBLY LINKED LOC REPORT -->

Pinned Verus source: [`99ae45aa8e35`](https://github.com/verus-lang/verus/blob/99ae45aa8e3568ec4933d23c6573a59efcd08ca3/examples/doubly_linked.rs) (SHA-256 `52abe834f0d6596bbaebcabb92330476707df184bb5456aeaf7c573ac01394c3`).

| Source | Declarations | Relevant LOC |
|---|---:|---:|
| Verus | 24 | 339 |
| Lean executable definitions | 14 | 84 |
| Lean ghost state, specifications and proofs | 44 | 287 |
| **Lean example total** | **58** | **371** |
| `vstd` equivalent, generic and reusable (`VerusStd.lean`) | 26 | 109 |
| Lean grand total | 84 | 480 |

| Definition or semantic group | Verus | Lean (executable, spec/proof) |
|---|---:|---:|
| `Node` | 4 | 4 (4, 0) |
| `DoublyLinkedList` | 4 | 3 (3, 0) |
| ghost state / `Cells` | 3 | 1 (0, 1) |
| `prev_of` / `prevOf` | 5 | 2 (0, 2) |
| `next_of` / `nextOf` | 5 | 2 (0, 2) |
| `well_formed_node` / `nodeAt` | 5 | 2 (0, 2) |
| `well_formed` / representation predicates | 7 | 6 (0, 6) |
| `view` | 4 | 1 (0, 1) |
| `new` | 10 | 9 (2, 7) |
| `push_empty_case` / `pushEmptyCase` | 17 | 8 (3, 5) |
| `push_back` / `pushBack` | 36 | 34 (9, 25) |
| `pop_back` / `popBack` | 42 | 32 (12, 20) |
| `push_front` / `pushFront` | 46 | 31 (9, 22) |
| `pop_front` / `popFront` | 49 | 24 (12, 12) |
| `get` (including the Lean loop) | 27 | 47 (13, 34) |
| `Iterator` | 4 | 4 (4, 0) |
| `Iterator::list` | 2 | 0 (0, 0) |
| `Iterator::index` | 2 | 0 (0, 0) |
| `Iterator::valid` | 4 | 2 (0, 2) |
| `Iterator::new` | 9 | 10 (2, 8) |
| `Iterator::value` | 10 | 13 (4, 9) |
| `Iterator::move_next` / `moveNext` | 20 | 31 (7, 24) |
| `main::run` / example | 22 | 29 (0, 29) |
| entry-point `main` | 2 | 0 (0, 0) |
| Other example-local support declarations | - | 76 (0, 76) |
| **Total** | **339** | **371 (84, 287)** |

`VerusStd.lean` (26 declarations, 109 lines) is not compared declaration by declaration: it is the generic sequence and permission-map layer that Verus obtains from `vstd`, it does not mention the doubly-linked list, and each of its declarations names its `vstd` counterpart in its doc comment.

"Other example-local support declarations" contains 0 Verus, 0 Lean executable, and 15 Lean specification/proof declarations not assigned to a direct cross-language correspondence above.

<!-- END GENERATED DOUBLY LINKED LOC REPORT -->
