# Aeneas / Lean Verification Glossary

## Aeneas-Specific Terms

**Aeneas** — A tool that translates Rust programs to pure Lean code via the LLBC intermediate representation, enabling formal verification of Rust code in the Lean proof assistant.

**Backward continuation** — A function returned alongside a borrowed value that propagates updates back to the original owner. Generated when Rust code uses mutable borrows (`&mut T`). In the generated Lean code, appears as an extra return value: `Result (T × (T → Result OriginalType))`.

**Charon** — The Rust compiler frontend used by Aeneas. Extracts Rust MIR and produces LLBC. The `charon` binary and `charon-pin` file in the repo manage this.

**LLBC (Low-Level Borrow Calculus)** — Intermediate representation between Rust MIR and Lean. Captures ownership, borrowing, and lifetime information in a form suitable for translation to pure functional code.

**`Result` monad** — The error monad used in all Aeneas-generated code: `ok v` for success, `fail` for errors (panic, overflow, out-of-bounds). All generated functions return `Result T`.

**`ControlFlow`** — Inductive type used in loop translation: `ControlFlow.cont x` to continue the loop with new state, `ControlFlow.done y` to break with a result.

**`loop` (fixed-point operator)** — The combinator used to translate Rust loops: `loop (body : α → Result (ControlFlow α β)) (x : α) : Result β`. Reason about it with `loop.spec` or `loop.spec_decr_nat`.

## Specification Terms

**Progress theorem** — A theorem tagged with `@[progress]` that specifies the behavior of a function. The `progress` tactic searches these to step through monadic code.

**Auxiliary spec** — An intermediate specification that mirrors the code structure but is pure (no Result monad). Used as a bridge between a high-level mathematical spec and the Aeneas-generated code. Also called "intermediate spec."

**Weakest-precondition notation (`⦃ ⦄`)** — The notation `f x ⦃ r => P r ⦄` means "if `f x` succeeds, the result `r` satisfies `P r`." Used in all Aeneas spec statements.

**Fold theorem** — A theorem proving that a sequence of inline monadic operations equals a call to a helper function. Used to decompose large proofs into manageable pieces.

**`#setup_aeneas_simps`** — A command placed at the top of proof files that enables `getElem!`/`set!` patterns and deactivates problematic simp lemmas.

## Tactic Terms

**`progress`** — Core Aeneas tactic. Applies a function specification to step through one monadic bind (`let x ← f args`). Searches `@[progress]`-tagged theorems.

**`progress*`** — Repeatedly applies `progress` with automatic case splitting until it gets stuck.

**`progress*?`** — Like `progress*` but generates an explicit proof script that can be copied, reviewed, and optimized.

**`scalar_tac`** — Arithmetic reasoning tactic for Rust integer types. Handles bounds checking, overflow, and integer arithmetic. Supports `+nonLin` for nonlinear reasoning.

**`simp_scalar`** — Simplification tactic for scalar expressions (min, max, modular arithmetic). simp-based, so safe to activate many local lemmas.

**`simp_lists`** — Simplification tactic for list/array operations (get, set, length). simp-based.

**`bv_tac`** — Bit-vector decision procedure. Syntax: `bv_tac N` where N is the bit-width (e.g., 32, 64).

**`bvify`** — Lifts a Nat/Int goal into a BitVec goal so `bv_tac` can solve it. Syntax: `bvify N`.

**`natify`** — Converts BitVec expressions back to Nat. Used in the reverse lifting trick.

**`zmodify`** — Lifts Nat/Int expressions into ZMod. Useful because ZMod is a ring (enables `ring` tactic).

**`agrind`** — Preferred general-purpose automation tactic (over `grind`, which tends to explode). Good for list reasoning, equalities, and general goals.

**`split_conjs`** — Splits a conjunction goal (`A ∧ B ∧ C`) into separate sub-goals. Often paired with `<;> agrind` because each conjunct is easier to prove separately.

**`simp_ifs`** — Simplifies if-then-else expressions in the goal.

**`fcongr`** — Congruence tactic for monadic/functional expressions.

## Proof Patterns

**Sorry-driven development** — Writing `sorry` as a placeholder, then using `goal` to inspect what needs proving, replacing `sorry` with tactics incrementally.

**Reverse lifting trick** — When `bvify` can't lift a goal/hypothesis directly: (1) state the BitVec equivalent with `have`, prove it with `bv_tac`, convert back with `natify`; or (2) for hypotheses, state the BitVec equivalent, prove it using `natify` to transform into the original hypothesis.

**Function decomposition** — Breaking a large generated function into smaller helper definitions with fold theorems, proving specs for each piece independently.

**The `progress*?` → automate → refold workflow** — Use `progress*?` to generate a full script, register automation lemmas, then progressively compact the script back into `progress*` + finishing tactics.

## Project Structure

**`Types.lean`** — Generated file containing Lean translations of Rust types.

**`Funs.lean`** — Generated file containing Lean translations of Rust functions.

**`FunsExternal.lean`** — Hand-written models of external functions (e.g., std library functions not translated by Aeneas).

**`Properties/`** — Directory for proof files (specs, lemmas, theorems).

**`Spec.lean`** — Convention for files containing pure mathematical specifications.
