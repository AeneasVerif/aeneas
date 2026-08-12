# Separation Logic Proof of Concept

This directory contains the proof-of-concept work for extending the separation
logic (SL) support.

## Files

| File | Purpose |
|---|---|
| [`FFree.lean`](FFree.lean) | Defines the generic freer monad, and the state machines that give it an operational semantics (after "Program Logics à la Carte"): `StateMachine`, `Exec`, `Runs` and `Evaluates`. |
| [`Heap.lean`](Heap.lean) | Defines locations, dynamically typed cells, and finite heaps. |
| [`RustHeap.lean`](RustHeap.lean) | The Rust view of the heap: `Ptr` and the pointer operations, over `Heap.lean`. |
| [`SLTactics.lean`](SLTactics.lean) | Port of the SLF tactics: `sl_frame`, `sl_pull`, `sl_xchange`, …, including affine `GC` absorption. |
| [`ST.lean`](ST.lean) | The state monad `St`, its state machine, its denotation `theta` into `Wp`, affine Hoare triples, and the specifications of the pointer operations. |
| [`Step.lean`](Step.lean) | Wires the triples into the `step` tactic and provides `sl_frame`. |
| [`WP.lean`](WP.lean) | Separation-logic assertions, fully affine `GC`, the magic wand, and the `Wp` monad of predicate transformers. |
| [`ProofScore.lean`](ProofScore.lean) | Engineering tool, not part of the library: measures how close the proofs of the triples are to the ideal proof, i.e. how much separation logic the automation still leaves to the user. Writes [`proof-score.md`](proof-score.md). |
| `README.md` | Records the purpose and meaning of files in this directory. |

| File in [`Examples/`](Examples) | Purpose |
|---|---|
| [`Basic.lean`](Examples/Basic.lean) | Basic programs and specifications exercising `step` over pure computations and pointers. |
| [`VerusDoublyLinkedList.lean`](Examples/VerusDoublyLinkedList.lean) | Port of the Verus doubly-linked-list example: executable definitions, then ghost state, specifications and proofs. |
| [`EqOrDisj.lean`](Examples/EqOrDisj.lean) | Pointer specifications that account for possible aliasing using equal-or-disjoint ghost state. |
| [`UnitTest.lean`](Examples/UnitTest.lean) | Regression tests for `step`, `sl_step`, and the separation-logic tactics. |
| [`VerusStd.lean`](Examples/VerusStd.lean) | The `vstd` layer: generic sequences of pointer/payload pairs and permission maps over them, with each declaration naming its `vstd` counterpart. Independent of any data structure. |
| [`doubly_linked_loc.py`](Examples/doubly_linked_loc.py) | Deterministically regenerates the relevant-LOC comparison with the pinned Verus example below. |

Keep these tables updated whenever a file is added, removed, or repurposed.

The logic is affine, following SLF's
[Affine Separation Logic](https://softwarefoundations.cis.upenn.edu/slf-current/Affine.html).
There is no linear or partially affine mode: `GC` accepts every heap, and every
triple implicitly extends its postcondition with `GC`. Consequently, any unused
heap resources may be discarded from either a triple's precondition or
postcondition.

## How ideal are the proofs?

The point of the automation is that a triple should be proved by unfolding the
program and calling `sl_step*`, with only pure reasoning and `sl_pull` in
between, and one such block per branch of the program.  Run

```
lake env lean --run Aeneas/SLPoC/ProofScore.lean
```

from `backends/lean` to measure how far the proofs are from that, in
[`proof-score.md`](proof-score.md): every proof of a triple is split into
*spots* — one straight-line block before the first branch, then one per branch
body, recursively — and a spot counts as ideal when no step of it steers the
separation logic by hand.  The report names the offending step and says what
gave it away, so it doubles as a to-do list for the automation.

The tool parses with Lean's own parser but elaborates nothing except the
commands that open a namespace, so it takes about a second and also works on a
file that does not compile; a file whose module has been built is additionally
imported, which makes the notation it defines available.  Pass file paths to
score files other than those of [`Examples/`](Examples), and `-o` to write the
report elsewhere.

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
| Lean ghost state, specifications and proofs | 36 | 241 |
| **Lean example total** | **50** | **325** |
| `vstd` equivalent, generic and reusable (`VerusStd.lean`) | 24 | 98 |
| Lean grand total | 74 | 423 |

| Definition or semantic group | Verus | Lean (executable, spec/proof) |
|---|---:|---:|
| `Node` | 4 | 4 (4, 0) |
| `DoublyLinkedList` | 4 | 3 (3, 0) |
| ghost state / `Cells` | 3 | 1 (0, 1) |
| `prev_of` / `prevOf` | 5 | 2 (0, 2) |
| `next_of` / `nextOf` | 5 | 2 (0, 2) |
| `well_formed_node` / `nodeAt` | 5 | 2 (0, 2) |
| `well_formed` / representation predicates | 7 | 4 (0, 4) |
| `view` | 4 | 1 (0, 1) |
| `new` | 10 | 7 (2, 5) |
| `push_empty_case` / `pushEmptyCase` | 17 | 9 (3, 6) |
| `push_back` / `pushBack` | 36 | 25 (9, 16) |
| `pop_back` / `popBack` | 42 | 22 (12, 10) |
| `push_front` / `pushFront` | 46 | 28 (9, 19) |
| `pop_front` / `popFront` | 49 | 19 (12, 7) |
| `get` (including the Lean loop) | 27 | 38 (13, 25) |
| `Iterator` | 4 | 4 (4, 0) |
| `Iterator::list` | 2 | 0 (0, 0) |
| `Iterator::index` | 2 | 0 (0, 0) |
| `Iterator::valid` | 4 | 3 (0, 3) |
| `Iterator::new` | 9 | 9 (2, 7) |
| `Iterator::value` | 10 | 13 (4, 9) |
| `Iterator::move_next` / `moveNext` | 20 | 26 (7, 19) |
| `main::run` / example | 22 | 29 (0, 29) |
| entry-point `main` | 2 | 0 (0, 0) |
| Other support declarations | - | 74 (0, 74) |
| **Total** | **339** | **325 (84, 241)** |

`VerusStd.lean` (24 declarations, 98 lines) is not compared declaration by declaration: it is the generic sequence and permission-map layer that Verus obtains from `vstd`, it does not mention the doubly-linked list, and each of its declarations names its `vstd` counterpart in its doc comment.

"Other support declarations" contains 0 Verus, 0 Lean executable, and 14 Lean specification/proof declarations not assigned to a direct cross-language correspondence above, together with the `attribute` commands that configure the automation.

<!-- END GENERATED DOUBLY LINKED LOC REPORT -->
