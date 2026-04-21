# Full Support For Nested Loop Exits

This plan tracks full support for:

- `return` from inside nested loops.
- `break` to an outer loop, for example `break 'outer`.
- `continue` to an outer loop, for example `continue 'outer`.

The goal is not to remove assertions locally. The goal is to preserve Rust
control flow through pre-passes, symbolic execution, pure AST translation,
micro-passes, extraction, and backend verification.

## Current Known Blockers

- `src/PrePasses.ml` rejects `Break i` and `Continue i` when `i <> 0`.
- `src/PrePasses.ml` rejects `Return` when loop depth is greater than one.
- `src/interp/InterpLoopsFixedPoint.ml` assumes loop fixed-point computation only
  sees `Continue 0` for re-entry and `Break 0` for loop exit.
- `src/interp/InterpLoops.ml` assumes symbolic loop body synthesis only needs to
  emit the current loop's `LoopContinue` and `LoopBreak`.
- `src/symbolic/SymbolicToPureExpressions.ml` receives a loop id for
  `LoopContinue` and `LoopBreak`, but currently ignores it and uses only the
  active `mk_continue` / `mk_break` callbacks.
- `src/pure/Pure.ml` has a `TLoopResult` type with only current-loop
  `continue`, current-loop `break`, and failure. There is no pure-level
  representation for propagated `return`, outer `break`, or outer `continue`.

## Design Invariants

- Concrete and symbolic control-flow semantics must agree: `Break i` and
  `Continue i` are relative depths, consumed one loop at a time.
- Current-loop exits stay local: `Continue 0` drives fixed-point re-entry and
  `Break 0` drives the normal loop result.
- Outer-loop exits are propagated through inner loops without joining them into
  the inner loop's normal break context.
- `return` from any nested loop is propagated as a function return, not encoded
  as an unrelated current-loop break unless this is a proven, semantics-preserving
  final lowering.
- Loop output contexts must remain precise enough for borrows, abstractions,
  symbolic values, and backward functions.
- Generated pure code must make propagated control flow explicit and typed.
- Existing generated code for ordinary loops should remain stable as much as
  possible.

## Milestone 1: Add Focused Known-Failure Tests

Add minimal tests before changing behavior.

- Add `tests/src/loops-nested-control.rs`.
- Mark it as `known-failure` initially if needed.
- Include plain scalar examples:
  - `break_outer`: inner loop executes `break 'outer`.
  - `continue_outer`: inner loop executes `continue 'outer`.
  - `return_nested`: inner loop executes `return value`.
  - `break_outer_with_value_flow`: outer loop mutates a value before and after
    the inner loop so the expected output depends on correct propagation.
- Include borrow-sensitive examples:
  - `break_outer_array_update`: update an array in the inner loop, then break
    the outer loop.
  - `continue_outer_array_update`: update an array before continuing the outer
    loop.
  - `return_nested_mut_borrow`: return from a branch that has active local
    mutable borrow structure, if accepted by Rust.

Verification:

- `make test-loops-nested-control.rs` reaches the current expected error.
- The checked `.out` file names the unsupported nested return or outer
  break/continue limitation.
- `rustc` accepts the Rust examples.

Expected result:

- No functional support yet.
- The failing surface is recorded and small enough to use while developing.

## Milestone 2: Make Pre-Passes Control-Flow Transparent

Update `PrePasses.update_loops` so it no longer rejects control flow that the
symbolic interpreter can represent.

- Remove the blanket `i = 0` assertions for `Break i` and `Continue i`.
- Replace the `depth <= 1` assertion for `Return` with a transformation strategy
  that only rewrites returns when the rewrite is local and proven safe.
- Keep the current return-to-break rewrites for simple one-loop cases if they are
  still useful, but do not apply them across nested loop boundaries.
- Ensure any transformation that moves `after` statements into a loop only applies
  to exits targeting that same loop.
- Add comments that state the relative-depth convention.

Verification:

- Add unit-shaped expectations by running the known-failure tests and confirming
  errors move past pre-passes into loop synthesis.
- Run existing loop translations:
  - `make test-loops.rs`
  - `make test-loops-nested.rs`
  - `make test-loops-nested-rec.rs`

Tests should assert:

- A `break 'outer` is still represented as `Break 1` when evaluating the inner
  loop body.
- A `continue 'outer` is still represented as `Continue 1` when evaluating the
  inner loop body.
- Existing one-loop early-return examples still translate.

Expected result:

- Pre-passes preserve nested exits instead of rejecting them.
- Symbolic loop code becomes the next failure point.

## Milestone 3: Introduce Explicit Symbolic Loop Exit Kinds

Extend the symbolic AST so loop exits are not all forced into the current loop's
normal break channel.

- Add a symbolic loop exit kind, for example:
  - `NormalBreak`
  - `PropagatedBreak of int`
  - `PropagatedContinue of int`
  - `PropagatedReturn`
- Replace or supplement `break_svalues` / `break_abs` in `SymbolicAst.loop` with
  per-exit output descriptions.
- Keep `LoopContinue` for current-loop re-entry.
- Either generalize `LoopBreak` into `LoopExit` or add a new `LoopExit` node.
- Update `PrintSymbolicAst.ml` to display exit kind and payloads.

Verification:

- Add local symbolic-AST print checks if the test runner can expose them.
- Otherwise use generated `.out` from known-failure tests while implementation is
  incomplete.
- Run `cd src && dune build`.

Tests should assert:

- Inner `Break 0` becomes the inner loop's `NormalBreak`.
- Inner `Break 1` becomes a propagated `Break 0` for the outer loop.
- Inner `Continue 1` becomes a propagated `Continue 0` for the outer loop.
- Nested `return` becomes a propagated function return.

Expected result:

- Symbolic AST has enough structure to represent all loop exits precisely.

## Milestone 4: Generalize Loop Fixed-Point Entry Computation

Update `compute_loop_entry_fixed_point` to ignore only propagated exits while
still using current-loop continues for fixed-point iteration.

- Treat `Continue 0` as a re-entry context.
- Treat `Continue i` for `i > 0` as a propagated exit, not as a fixed-point
  re-entry.
- Treat `Break _`, `Return`, and `Panic` as non-re-entry exits.
- Preserve current behavior for loops with only local continue/break.

Verification:

- Run focused tests where the inner loop has both:
  - a local `continue`, and
  - an outer `continue`.
- Run existing nested loop tests to ensure ordinary inner loops still compute
  fixed points.
- Run `cd src && dune build`.

Tests should assert:

- Fixed-point inputs for an inner loop are computed only from local re-entry
  paths.
- An outer `continue` path does not pollute the inner loop's fixed-point state.

Expected result:

- Loop fixed points remain local to the loop being analyzed.

## Milestone 5: Generalize Loop Exit Context Collection

Replace `compute_loop_break_context` with a function that collects all relevant
exit contexts for the current loop.

- For `Break 0`, compute the normal loop break context as today.
- For `Break i` with `i > 0`, collect a propagated break context with depth
  `i - 1` after the current loop consumes one level.
- For `Continue i` with `i > 0`, collect a propagated continue context with
  depth `i - 1`.
- For `Return`, collect a propagated return context.
- Keep `Panic` behavior unchanged unless panic propagation also needs explicit
  typing in the same mechanism.
- Join contexts per exit kind, not all together.
- Preserve the single-break fast path for the normal break case.

Verification:

- Add examples with multiple `break 'outer` branches that reach the same outer
  loop exit and require a join.
- Add examples where normal inner break and propagated outer break coexist.
- Run:
  - `make test-loops-nested-control.rs`
  - `make test-loops-nested.rs`

Tests should assert:

- Normal inner break continues after the inner loop.
- Propagated outer break exits the outer loop.
- Joined propagated exits include the right modified scalar/array values.

Expected result:

- The symbolic interpreter can compute output contexts for every loop exit kind.

## Milestone 6: Return Multiple Results From Symbolic Loop Evaluation

Update `eval_loop_symbolic` so a loop can evaluate to more than one statement
result.

- Current behavior returns one `(break_ctx, Unit)` after a successful loop call.
- New behavior should return:
  - `(normal_break_ctx, Unit)` for normal loop completion.
  - `(ctx, Break i)` for propagated outer breaks.
  - `(ctx, Continue i)` for propagated outer continues.
  - `(ctx, Return)` for propagated returns.
- Adapt `eval_loop` and callers so the loop continuation composes multiple exit
  expressions correctly.
- Preserve the concrete evaluator's existing depth-decrement behavior.

Verification:

- Run existing switch/branch tests that produce multiple contexts.
- Run focused tests where after-loop code must execute only for normal break.
- Run `cd src && dune build`.

Tests should assert:

- Statements after the inner loop execute on normal inner break.
- Statements after the inner loop do not execute on propagated outer break,
  propagated outer continue, or propagated return.
- Statements after the outer loop execute only for normal outer break.

Expected result:

- Symbolic statement sequencing sees loop exits just like it sees branch exits.

## Milestone 7: Lower Symbolic Loop Exits To Typed Pure Control Flow

Update `SymbolicToPureExpressions.translate_loop` and related context helpers.

- Stop ignoring the loop id in `translate_continue_break`.
- Replace the single active `mk_continue` / `mk_break` pair with target-aware
  loop-control callbacks, or lower all non-current exits through explicit loop
  result payloads before translation.
- Define a typed encoding for loop exits. Candidate shape:
  - current `ControlFlow continue break` remains the loop-body result for simple
    loops;
  - loops with propagated exits use a sum type around normal break and
    propagated control;
  - propagated return carries the function return payload and backward outputs.
- Generate a `match` after each loop call that dispatches:
  - normal break payload to `next_expr`;
  - propagated break payload to the outer loop's break callback;
  - propagated continue payload to the outer loop's continue callback;
  - propagated return payload to the function return callback.
- Ensure panic/failure still maps to the result error path.

Verification:

- Build pure AST with type checking enabled if available.
- Run `cd src && dune build`.
- Run focused tests to generate Lean/F*/Coq where supported.

Tests should assert:

- Generated pure code contains a dispatch after an inner loop with propagated
  exits.
- The dispatch target for `break 'outer` is the outer loop's `done`, not the
  inner loop's `done`.
- The dispatch target for `continue 'outer` is the outer loop's `cont`, not the
  inner loop's `cont`.
- A nested `return` lowers to the function's return path.

Expected result:

- Pure expressions become well typed for nested exits.

## Milestone 8: Update Pure Loop Micro-Passes

Audit and update `src/pure/PureMicroPassesLoops.ml`.

- Update passes that inspect `TLoopResult` constructors so they understand the
  new exit encoding.
- Preserve simplifications for ordinary loops.
- Update loop input/output filtering to account for propagated-exit payloads.
- Update recursive-loop conversion if nested exits interact with
  `RecLoopCall`.
- Update loop decomposition so generated auxiliary loop definitions expose the
  right output type.

Verification:

- Run:
  - `make test-loops.rs`
  - `make test-loops-rec.rs`
  - `make test-loops-nested.rs`
  - `make test-loops-nested-rec.rs`
  - `make test-loops-nested-control.rs`
- Compare generated output for existing tests and keep churn explainable.

Tests should assert:

- Useless loop input/output filtering does not remove values needed by
  propagated exits.
- Recursive-loop extraction still works for ordinary nested loops.
- If recursive-loop extraction cannot support propagated exits initially, it
  should fail with a targeted error and the non-recursive loop path should pass.

Expected result:

- Pure micro-passes preserve and simplify nested-exit control flow correctly.

## Milestone 9: Update Extraction Backends

Update extraction code and backend primitives only if the chosen pure encoding
requires it.

- Check Lean, F*, Coq, and HOL4 naming for any new control-flow type or variant.
- Prefer reusing existing sum/result/control-flow encodings where possible.
- Update pretty-printers and builtin mappings if a new builtin is introduced.
- Keep backend-specific syntax small and generated from shared pure structure.

Verification:

- Run backend generation:
  - `make test-loops-nested-control.rs`
  - `make test-loops-nested.rs`
- Run backend verification where practical:
  - `cd tests && make verify-lean`
  - `cd tests && make verify-coq`
  - `cd tests && make verify-fstar`

Tests should assert:

- Generated Lean compiles for scalar nested-exit examples.
- Generated Coq/F* compiles or is explicitly skipped only for existing unrelated
  backend limitations.
- Existing generated backend files still verify.

Expected result:

- Nested exits are representable in emitted proof code.

## Milestone 10: Remove Known-Failure Status And Update Documentation

Once support is complete, update tests and docs.

- Remove `known-failure` from `tests/src/loops-nested-control.rs`.
- Commit generated backend outputs.
- Update `README.md` to remove the loop limitation.
- Update `docs/user/src/README.md` if it still mentions no nested loops.
- Add a short note to tests or docs explaining supported loop-control forms.

Verification:

- Run:
  - `make test-loops-nested-control.rs`
  - `make test`
  - relevant `make verify-*` targets.
- Confirm README no longer claims unsupported nested loop exits.

Tests should assert:

- All new examples translate successfully.
- Existing loop tests still translate and verify.
- Documentation matches actual behavior.

Expected result:

- The safe subset officially supports nested returns and outer break/continue.

## Final Acceptance Criteria

- `break 'outer` works from nested loops.
- `continue 'outer` works from nested loops.
- `return` works from nested loops.
- Support works for scalar-only code and code with mutable state that affects
  loop output contexts.
- Existing loop tests continue to pass.
- Generated pure code is typed and backend output verifies for supported
  backends.
- No assertions remain that reject supported nested loop exits.
- README limitation is removed only after tests and backend generation pass.
