# Introduction to Aeneas

Aeneas is a verification toolchain for Rust programs aiming to embed purely functional translation of Rust programs into theorem provers such as Coq or Lean.

## What it can do?

Aeneas aims to provide verification facilities for **safe** Rust with some caveats described in the next section.

## What it cannot do?

- loops: no nested loops for now. We are working on lifting this limitation.
- no functions pointers/closures: ongoing work. We have support for traits and will have support for function pointers and closures soon.
- limited type parametricity: it is not possible for now to instantiate a type parameter with a type containing a borrow. This is mostly an engineering issue.
- no nested borrows in function signatures: ongoing work.
- interior mutability: ongoing work. We are thinking of modeling the effects of interior mutability by using ghost states.
- no concurrent execution: long-term effort. We plan to address coarse-grained parallelism as a long-term goal.
