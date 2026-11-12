(** The per-module split ([-split-files], Lean only): one Lean module per Rust
    module, plus an entry point which imports them all.

    The Rust modules which depend on each other are merged in a single Lean
    module, and a module whose opaque and transparent declarations alternate is
    cut into several files; see {!FileGraph} and {!FilePlan}, which are the
    internals of this layout. *)

include FileLayout.S
