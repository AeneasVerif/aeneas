# Summary

[Introduction](./README.md)

# Setup guide

# Proving with Lean

- [Getting started]()
- [Defining Binary Search Trees in Rust](./rust/bst_def.md)
  - [Extracting to Lean]()
  - [Panic-freedomness]()
- [Specifying Invariants in Lean]()
  - [Invariants of a binary search tree](./lean/bst/invariants.md)
  - [Picking mathematical representations](./lean/bst/math-repr.md)
- [Verifying `Find` Operation]()
  - [What does it mean to be in a tree?](./lean/bst/set_of_values.md)
  - [Dealing with Loops](./lean/bst/loops.md)
  - [Applying Known Specifications: `progress` tactic](./lean/bst/progress.md)
- [Verifying Insert Operation]()
  - [Dealing with Large Proofs]()
  - [Dealing with Symmetry]()
- [Verifying Height Operation](./lean/bst/height.md)
  - [Dealing with Termination Issues](./lean/bst/termination.md)
  - [Dealing with Machine Integers: `scalar_tac` Tactic](./lean/bst/scalars.md)
  - [Refining the Translation](./lean/bst/refining.md)
