# Separation Logic Proof of Concept

This directory contains the proof-of-concept work for extending the separation
logic (SL) support.

## Files

| File | Purpose |
|---|---|
| [`DoublyLinkedList.lean`](DoublyLinkedList.lean) | Port of the Verus doubly-linked-list example: executable definitions. |
| [`DoublyLinkedListLib.lean`](DoublyLinkedListLib.lean) | Ghost state of `DoublyLinkedList.lean` plus the sequence/index and permission-map lemmas Verus gets from `vstd`; every lemma names its `vstd` counterpart. |
| [`DoublyLinkedListSpec.lean`](DoublyLinkedListSpec.lean) | Specifications and proofs for `DoublyLinkedList.lean`. |
| [`DoublyLinkedListTests.lean`](DoublyLinkedListTests.lean) | Frame-inference regression tests exercising the list specifications. |
| [`doubly_linked_loc.py`](doubly_linked_loc.py) | Deterministically regenerates the relevant-LOC comparison with the pinned Verus example below. |
| [`FFree.lean`](FFree.lean) | Defines the generic freer monad, and the state machines that give it an operational semantics (after "Program Logics à la Carte"): `StateMachine`, `Exec`, `Runs` and `Evaluates`. |
| [`Heap.lean`](Heap.lean) | Defines locations, dynamically typed cells, and finite heaps. |
| [`RustHeap.lean`](RustHeap.lean) | The Rust view of the heap: `Ptr` and the pointer operations, over `Heap.lean`. |
| [`SLTactics.lean`](SLTactics.lean) | Port of the SLF tactics: `sl_frame`, `sl_pull`, `sl_xchange`, … |
| [`ST.lean`](ST.lean) | The state monad `St`, its state machine, its denotation `theta` into `Wp`, the Hoare triples, and the specifications of the pointer operations. |
| [`Step.lean`](Step.lean) | Wires the triples into the `step` tactic and provides `sl_frame`. |
| [`StepTests.lean`](StepTests.lean) | Regression tests for `step` and `sl_frame`. |
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
`DoublyLinkedListLib.lean` and reported separately: the comparable figure is the
executable definitions plus `DoublyLinkedListSpec.lean`.

<!-- BEGIN GENERATED DOUBLY LINKED LOC REPORT -->

Pinned Verus source: [`99ae45aa8e35`](https://github.com/verus-lang/verus/blob/99ae45aa8e3568ec4933d23c6573a59efcd08ca3/examples/doubly_linked.rs) (SHA-256 `52abe834f0d6596bbaebcabb92330476707df184bb5456aeaf7c573ac01394c3`).

| Source | Declarations | Relevant LOC |
|---|---:|---:|
| Verus | 24 | 339 |
| Lean executable definitions | 14 | 84 |
| Lean ghost state and `vstd`-equivalent library (`DoublyLinkedListLib.lean`) | 49 | 187 |
| Lean specifications and proofs (`DoublyLinkedListSpec.lean`) | 21 | 219 |
| **Lean total** | **84** | **490** |

| Definition or semantic group | Verus | Lean (executable, spec/proof) |
|---|---:|---:|
| `Node` | 4 | 4 (4, 0) |
| `DoublyLinkedList` | 4 | 3 (3, 0) |
| ghost state / `Cells` | 3 | 1 (0, 1) |
| `prev_of` / `prevOf` | 5 | 2 (0, 2) |
| `next_of` / `nextOf` | 5 | 2 (0, 2) |
| `well_formed_node` / `nodeAt` | 5 | 2 (0, 2) |
| `well_formed` / representation predicates | 7 | 8 (0, 8) |
| `view` | 4 | 1 (0, 1) |
| `new` | 10 | 9 (2, 7) |
| `push_empty_case` / `pushEmptyCase` | 17 | 8 (3, 5) |
| `push_back` / `pushBack` | 36 | 34 (9, 25) |
| `pop_back` / `popBack` | 42 | 32 (12, 20) |
| `push_front` / `pushFront` | 46 | 31 (9, 22) |
| `pop_front` / `popFront` | 49 | 24 (12, 12) |
| `get` (including the Lean loop) | 27 | 60 (13, 47) |
| `Iterator` | 4 | 4 (4, 0) |
| `Iterator::list` | 2 | 0 (0, 0) |
| `Iterator::index` | 2 | 0 (0, 0) |
| `Iterator::valid` | 4 | 2 (0, 2) |
| `Iterator::new` | 9 | 10 (2, 8) |
| `Iterator::value` | 10 | 13 (4, 9) |
| `Iterator::move_next` / `moveNext` | 20 | 31 (7, 24) |
| `main::run` / example | 22 | 29 (0, 29) |
| entry-point `main` | 2 | 0 (0, 0) |
| Support corresponding to Verus library primitives<br>1. `headPtr`<br>2. `lastPtr`<br>3. `view_nil`<br>4. `view_cons`<br>5. `view_append`<br>6. `view_length`<br>7. `view_getElem?`<br>8. `nodesFrom_nil`<br>9. `nodesFrom_cons`<br>10. `nodes_nil`<br>11. `prevOf_zero`<br>12. `headPtr_nil`<br>13. `lastPtr_nil`<br>14. `nodesFrom_congr`<br>15. `nodesFrom_append`<br>16. `nodesFrom_singleton`<br>17. `nodesFrom_append_prefix`<br>18. `nodesFrom_cons_shift`<br>19. `headPtr_cons`<br>20. `lastPtr_snoc`<br>21. `lastPtr_singleton`<br>22. `lastPtr_cons_cons`<br>23. `nodeAt_snoc_last`<br>24. `nodes_snoc`<br>25. `nodes_snoc_two`<br>26. `nodes_cons`<br>27. `nodeAt_cons_one`<br>28. `nodesFrom_cons_two`<br>29. `get!_some`<br>30. `eq_nil_or_snoc`<br>31. `lastPtr_eq_none_iff`<br>32. `headPtr_eq_none_iff`<br>33. `headPtr_append_two`<br>34. `lastPtr_append_two`<br>35. `nodes_eq_nodesFrom`<br>36. `nodes_split`<br>37. `nodes_read`<br>38. `exists_cell`<br>39. `view_eq_snoc`<br>40. `view_eq_cons` | - | 171 (0, 171) |
| Other example-local support declarations | - | 9 (0, 9) |
| **Total** | **339** | **490 (84, 406)** |

"Support corresponding to Verus library primitives" is exactly the set of 40 declarations of `DoublyLinkedListLib.lean` that are not matched to a Verus declaration above: sequence/index reasoning and permission lookup/splitting that Verus obtains from `vstd` primitives and their specifications.  Each of them carries a doc comment naming the `vstd` counterpart.

"Other example-local support declarations" contains 0 Verus, 0 Lean executable, and 1 Lean specification/proof declarations not assigned to a direct cross-language correspondence above.

<!-- END GENERATED DOUBLY LINKED LOC REPORT -->
