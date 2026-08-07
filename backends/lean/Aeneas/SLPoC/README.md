# Separation Logic Proof of Concept

This directory contains the proof-of-concept work for extending the separation
logic (SL) support.

## Files

| File | Purpose |
|---|---|
| [`Computation.lean`](Computation.lean) | Instantiates the freer monad with heap events and defines its runner. |
| [`FFree.lean`](FFree.lean) | Defines the generic freer monad. |
| [`Heap.lean`](Heap.lean) | Defines locations, dynamically typed cells, and finite heaps. |
| `README.md` | Records the purpose and meaning of files in this directory. |

Keep this table updated whenever a file is added, removed, or repurposed.
