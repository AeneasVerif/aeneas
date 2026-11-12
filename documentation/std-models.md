# Adding a Model of the Rust Standard Library

Calls to the Rust standard library are translated to *models*: Lean definitions in `backends/lean/Aeneas/Std`. A new model comes, in one PR, with tests of the examples of the Rust documentation, specification theorems, and specifications of the examples proved by `step*`.

## 1. The model

- **Name and place it after the Rust path** (`core::option::Option::map` → `core.option.Option.map` in `Std/Core/CoreOption.lean`). The Rust name patterns are in Aeneas's `TypesExternal_Template.lean` / `FunsExternal_Template.lean` (with `-split-files`).
- **Annotate it** (`rust_type`, `rust_const`, `rust_fun`, `rust_trait`, `rust_trait_impl`; options in `Aeneas/Extract/Extract.lean`), and **link the Rust documentation** in its docstring: `` /-- Model of `Option::map` (<https://doc.rust-lang.org/std/option/enum.Option.html#method.map>). -/ ``.
- **Follow Rust where it matters**: the same calls in the same order, and `fail` where Rust panics.
- **Keep it unfoldable**: `@[expose]`, no `private`, no `partial` (use `partial_fixpoint`).
- **Run `make extract-lean-std`** and commit `src/extract/ExtractBuiltinLean.ml` (CI checks it).

## 2. The documentation's examples as tests

In `tests/src/<name>.rs`, write **every example of the documentation of the new items**, and its corner cases, in two parts:

- a `pub fn` doing the computation of the example: section 4 specifies it, and proves it with `step*`;
- a `#[verify::test]` function calling it on the inputs of the documentation and asserting its results (assert only with modelled operations). Aeneas follows each `#[verify::test]` with `#guard (test_…).reducesTo ()`, so the Lean build evaluates the translated `assert!`s; `#[cfg(test)]` runs them in Rust (`make cargo-test`).

```rust
//@ [!lean] skip
//@ [lean] subdir=ResultCombinators
#![feature(register_tool)]
#![register_tool(verify)]

pub fn incr(r: Result<u32, bool>) -> Result<u32, bool> {
    r.map(|v| v + 1)
}

#[verify::test]
pub fn test_incr() {
    assert!(matches!(incr(Ok(2)), Ok(3)));
    assert!(matches!(incr(Err(true)), Err(true)));
}

#[cfg(test)]
mod tests {
    #[test]
    fn result_combinators() {
        super::test_incr()
    }
}
```

Generate the Lean translation with `make test-<name>.rs` and commit it.

## 3. Specification theorems

For each new function, prove the `@[step]` theorem (`<function>.spec`) which makes proofs about code calling it as effortless as possible: `step` applies it without help, its preconditions are ones `step` discharges, and its postcondition is what those proofs need.

## 4. Specifications of the examples

In `tests/lean/<Name>/Properties.lean` (imported by `tests/lean/<Name>.lean`; then `make -C tests/lean lakefile.lean`), prove a specification of each `pub fn` of the examples, covering every facet (each constructor, empty inputs, failures):

```lean
attribute [local step_simps] incr.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once

theorem incr_ok (v : U32) (h : v.val + 1 ≤ U32.max) :
    incr (.Ok v) ⦃ r => ∃ w, r = .Ok w ∧ w.val = v.val + 1 ⦄ := by
  unfold incr; step*

theorem incr_err (e : Bool) : incr (.Err e) ⦃ r => r = .Err e ⦄ := by
  unfold incr; step*
```

**Aim for each proof to be `unfold` and `step*`**, with at most a short finishing tactic. If a proof needs more, attempt to improve the specification theorem, not the proof.

Finally, check `lake build Aeneas --wfail` (in `backends/lean`), `make -C tests/lean verify` and `make cargo-test`.
