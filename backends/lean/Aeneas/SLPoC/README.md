# Separation Logic Proof of Concept

This directory contains the proof-of-concept work for extending the separation
logic (SL) support.

## Files

| File | Purpose |
|---|---|
| [`Computation.lean`](Computation.lean) | Instantiates the freer monad with heap events and defines its runner. |
| [`DoublyLinkedList.lean`](DoublyLinkedList.lean) | Port of the Verus doubly-linked-list example, with its specifications. |
| [`FFree.lean`](FFree.lean) | Defines the generic freer monad. |
| [`Heap.lean`](Heap.lean) | Defines locations, dynamically typed cells, and finite heaps. |
| [`SepLogic.lean`](SepLogic.lean) | Separation-logic assertions, the `Wp` monad, and Hoare triples. |
| [`Step.lean`](Step.lean) | Wires the triples into the `step` tactic and provides `sl_frame`. |
| [`StepTests.lean`](StepTests.lean) | Regression tests for `step` and `sl_frame`. |
| `README.md` | Records the purpose and meaning of files in this directory. |

Keep this table updated whenever a file is added, removed, or repurposed.
