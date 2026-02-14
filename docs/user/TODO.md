# TODO list for this sub-project

## Scaffolding

This project makes use of the Lean flake, but this flake will be soon deprecated and be development-only.

To overcome this problem, there's a need of https://github.com/oxalica/rust-overlay but for Lean, so that release candidates and various
versions can be selected without a compilation cost by reusing Lean pre-built binaries, i.e. wrapping Lean binaries in FODs in that repository.
