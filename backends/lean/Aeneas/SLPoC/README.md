# Separation Logic Proof of Concept

This directory contains the proof-of-concept work for extending the separation
logic (SL) support.

## Files

| File | Purpose |
|---|---|
| [`DoublyLinkedList.lean`](DoublyLinkedList.lean) | Port of the Verus doubly-linked-list example: executable definitions. |
| [`DoublyLinkedListSpec.lean`](DoublyLinkedListSpec.lean) | Ghost state, specifications and proofs for `DoublyLinkedList.lean`. |
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
