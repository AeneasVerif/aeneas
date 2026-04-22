# Full Support For Nested Loop Exits

This plan tracks full support for:

- `return` from inside nested loops.
- `break` to an outer loop, for example `break 'outer`.
- `continue` to an outer loop, for example `continue 'outer`.

The goal is not to remove local assertions. The goal is to preserve Rust control
flow through Charon/LLBC input, pre-passes, symbolic execution, borrow and
abstraction reconciliation, pure AST translation, loop micro-passes, extraction,
and backend verification.

Panic stays orthogonal to this work: it should continue to use the existing
`Result` error path, not the new loop-exit payload.

## Current Known Blockers

- `src/PrePasses.ml` rejects `Break i` and `Continue i` when `i <> 0`.
- `src/PrePasses.ml` rejects `Return` when loop depth is greater than one.
- `src/interp/InterpLoopsFixedPoint.ml` assumes fixed-point computation only
  sees `Continue 0` for re-entry and `Break 0` for loop exit.
- `src/interp/InterpLoops.ml` assumes symbolic loop body synthesis only needs to
  emit the current loop's `LoopContinue` and `LoopBreak`.
- `src/symbolic/SymbolicToPureExpressions.ml` receives a loop id for
  `LoopContinue` and `LoopBreak`, but currently ignores it and uses only the
  active `mk_continue` / `mk_break` callbacks.
- `src/pure/Pure.ml` has a `TLoopResult` type with only current-loop
  `continue`, current-loop `break`, and failure. There is no pure-level
  representation for propagated `return`, outer `break`, or outer `continue`.
- The concrete loop evaluator in `src/interp/InterpLoops.ml` already decrements
  relative `Break i` / `Continue i`, but the pre-pass currently prevents most
  nested-control cases from reaching it. This must be verified with tests rather
  than assumed.

## Design Invariants

- Charon labels must be resolved to relative `Break i` / `Continue i` depths
  before Aeneas relies on this representation.
- Concrete and symbolic control-flow semantics must agree: `Break i` and
  `Continue i` are relative depths, consumed one loop at a time.
- Current-loop exits stay local: `Continue 0` drives fixed-point re-entry and
  `Break 0` drives the normal loop result.
- Propagated exits are consumed by each enclosing loop. After an inner loop turns
  `Continue 1` into `Continue 0`, the enclosing loop must treat it as one of its
  own fixed-point re-entry contexts.
- Inner-loop abstractions must not leak across loop boundaries. Before an exit is
  propagated, the inner loop must end, consume, or translate abstractions it
  owns into a context compatible with the target loop.
- Context joins for propagated exits must align borrow, loan, abstraction,
  symbolic value, dummy variable, and backward-function structure. They are not
  just value joins.
- `return` from any nested loop is propagated as a function return, not encoded
  as an unrelated current-loop break unless a later lowering proves that rewrite
  semantics-preserving.
- Generated pure code must make propagated control flow explicit and typed.
- Existing generated code for ordinary loops should remain stable as much as
  possible.

## Milestone 1: Baseline Inputs And Current Failures

Add minimal tests and verify assumptions before changing behavior.

- Confirm the test harness supports `//@ known-failure` by checking
  `tests/test_runner/Input.ml` and the behavior documented in `tests/README.md`.
- Add `tests/src/loops-nested-control.rs`.
- Mark it as `known-failure` initially if needed.
- Include plain scalar examples:
  - `break_outer`: inner loop executes `break 'outer`.
  - `continue_outer`: inner loop executes `continue 'outer`.
  - `return_nested`: inner loop executes `return value`.
  - `normal_and_outer_break`: inner loop has both a local break and an outer
    break.
  - `outer_continue_feeds_fixed_point`: inner loop executes `continue 'outer`
    after mutating the outer loop's state.
- Include borrow-sensitive examples:
  - `break_outer_array_update`: update an array in the inner loop, then break
    the outer loop.
  - `continue_outer_array_update`: update an array before continuing the outer
    loop.
  - `return_nested_mut_borrow`: return from a branch that has active local
    mutable borrow structure, if accepted by Rust.
- Inspect Charon LLBC output for `break 'outer` and `continue 'outer`.

Verification:

- `rustc` accepts all new Rust examples.
- Charon emits relative `Break i` / `Continue i` depths, or the plan is revised
  before implementation continues.
- `make test-loops-nested-control.rs` reaches the current expected error.
- The checked `.out` file names the unsupported nested return or outer
  break/continue limitation.
- Because the known-failure run aborts on the first pre-pass error, inspect the
  generated LLBC directly to confirm the nested-return examples still contain
  `Return` statements.
- Code inspection confirms `eval_loop_concrete` decrements `Break i` /
  `Continue i` correctly. A direct or reduced concrete-execution check is
  deferred until Milestone 3, when pre-passes no longer reject the nested exits
  before concrete execution can observe them.

Tests should assert:

- Charon resolves `break 'outer` to depth `1` in the inner loop.
- Charon resolves `continue 'outer` to depth `1` in the inner loop.
- Charon preserves nested `return` as `Return` in the inner loop.
- Current Aeneas failure happens before semantic support is present and is
  recorded as a known failure.

Expected result:

- No functional support yet.
- The frontend and harness assumptions are explicit and verified.

## Milestone 2: Commit To A Pure Exit Encoding

Choose the representation before changing lowering and micro-passes.

- Define a pure-level loop-exit shape. Prefer a dedicated ADT over ad hoc nested
  sums if it keeps extraction and micro-passes readable.
- Required constructors:
  - normal loop break, carrying the loop's normal break payload.
  - propagated break, carrying the decremented depth and payload needed by the
    target loop.
  - propagated continue, carrying the decremented depth and payload needed by
    the target loop.
  - propagated return, carrying the function return payload and any backward
    outputs needed by the function boundary.
- Decide whether simple loops continue to use `TLoopResult` unchanged, and only
  loops with propagated exits use the new ADT.
- Decide how exit payloads are typed when different exits carry different value
  and abstraction-continuation sets.
- Decide how backend names will be generated for the new type or reused sum
  encoding.

Verification:

- Write a short design note in this file or an implementation comment near the
  new type.
- Add type-shape examples for:
  - inner loop with only normal break.
  - inner loop with normal break plus `break 'outer`.
  - inner loop with `continue 'outer`.
  - inner loop with nested `return`.
- `cd src && dune build` after adding type definitions, if this milestone
  introduces code.

Tests should assert:

- The chosen type can represent all reachable exit targets without relying on
  source labels.
- Panic is not represented as one of the new exit constructors.

Expected result:

- Later milestones have a committed target shape for signatures, contexts, and
  extraction.

Decision:

- Keep `TLoopResult continue break` unchanged for ordinary loops whose only
  structured exits are current-loop `continue` and current-loop `break`.
- Add a dedicated pure builtin `TLoopExit normal_break propagated_break
  propagated_continue propagated_return` for loops that may propagate an exit
  beyond the current loop.
- `NormalBreak normal_break` is the current loop's consumed break result.
- `PropagatedBreak propagated_break` carries a decremented relative break depth
  plus the value and abstraction-continuation payload required by the target
  loop.
- `PropagatedContinue propagated_continue` carries a decremented relative
  continue depth plus the target loop re-entry payload.
- `PropagatedReturn return` carries the function return payload and any
  backward outputs needed at the function boundary.
- Multiple branches reaching the same propagated target must be joined before
  packaging the corresponding payload; Milestone 6 defines the context join, but
  the pure exit type has one payload type per exit kind.
- If an exit kind is unreachable in a particular loop, its type parameter is
  `unit`. Type-shape examples:
  - inner-only break: `TLoopResult continue_ty normal_break_ty`.
  - normal break plus `break 'outer`: `TLoopExit normal_break_ty
    outer_break_ty unit unit`.
  - `continue 'outer`: `TLoopExit unit unit outer_continue_ty unit`.
  - nested `return`: `TLoopExit unit unit unit propagated_return_ty`.
- Backend names are generated as `LoopExit`/`loop_exit` with constructors
  `normalBreak`/`NormalBreak`, `propagatedBreak`/`PropagatedBreak`,
  `propagatedContinue`/`PropagatedContinue`, and
  `propagatedReturn`/`PropagatedReturn`.
- Panic remains on the existing `Result` error path and is not a `TLoopExit`
  constructor.
- `src/loop_exit_shape_test.ml` constructs and destructs all four `TLoopExit`
  variants with distinct payload types to pin the representation before later
  lowering emits it.

## Milestone 3: Make Pre-Passes Control-Flow Transparent

Update `PrePasses.update_loops` so it no longer rejects control flow that later
passes can represent.

- Remove the blanket `i = 0` assertions for `Break i` and `Continue i`.
- Replace the `depth <= 1` assertion for `Return` with a strategy that only
  rewrites returns when the rewrite is local and proven safe.
- Keep current one-loop return-to-break rewrites if useful, but do not apply
  them across nested loop boundaries.
- Ensure any transformation that moves `after` statements into a loop only
  applies to exits targeting that same loop.
- Add comments that state the relative-depth convention and explain why outer
  exits are preserved.

Verification:

- Run the known-failure tests and confirm errors move past pre-passes into loop
  synthesis or pure lowering.
  - `loops-nested-control.rs` now reaches `InterpLoopsFixedPoint.ml` with
    `Continues to outer loops not supported yet`; this confirms `PrePasses`
    preserves the nested exit instead of rejecting it.
- Run existing loop translations:
  - `make test-loops.rs`
  - `make test-loops-nested.rs`
  - `make test-loops-nested-rec.rs`

Tests should assert:

- A `break 'outer` is still represented as `Break 1` when evaluating the inner
  loop body.
- A `continue 'outer` is still represented as `Continue 1` when evaluating the
  inner loop body.
- A local return is not rewritten when the same loop can also be exited by an
  inner `break 'outer` path.
- Existing one-loop early-return examples still translate.

Expected result:

- Pre-passes preserve nested exits instead of rejecting them.
- Symbolic loop code becomes the next failure point.

## Milestone 4: Introduce Explicit Symbolic Loop Exit Kinds

Extend the symbolic AST so loop exits are not forced into the current loop's
normal break channel.

- Add a symbolic loop exit kind:
  - `NormalBreak`.
  - `PropagatedBreak of int`.
  - `PropagatedContinue of int`.
  - `PropagatedReturn`.
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

Implementation:

- `src/symbolic/SymbolicAst.ml` now has explicit symbolic loop exit kinds:
  `NormalBreak`, `PropagatedBreak of int`, `PropagatedContinue of int`, and
  `PropagatedReturn`.
- `LoopExit` represents loop exits with their kind and payload. `LoopBreak`
  remains as a legacy current-loop break node while pure lowering migrates.
- `loop.loop_exits` records per-exit output descriptions. Current-loop break
  outputs are mirrored in the old `break_svalues` / `break_abs` fields so
  existing pure lowering remains stable.
- Symbolic loop synthesis now emits `LoopExit NormalBreak` for current-loop
  breaks.
- `PrintSymbolicAst.ml` prints `LoopExit` expressions and loop-level
  `loop_exits`.
- `src/symbolic_loop_exit_shape_test.ml` pins the relative-depth mapping:
  `Break 0 -> NormalBreak`, `Break 1 -> PropagatedBreak 0`,
  `Continue 1 -> PropagatedContinue 0`, and nested returns are represented by
  `PropagatedReturn`.
- Because fixed-point computation still rejects propagated exits before loop
  synthesis can emit them, these are representation and helper-contract checks.
  Runtime production of propagated break/continue/return entries moves to
  Milestones 5 and 6.

## Milestone 5: Generalize Fixed-Point Entry And Outer Continue Consumption

Design fixed-point computation together with propagated continue consumption.

- For the loop currently being analyzed, treat direct `Continue 0` as a re-entry
  context.
- Treat direct `Continue i` for `i > 0` as a propagated exit from the current
  loop.
- When an inner loop returns propagated `Continue 0` to an enclosing loop, the
  enclosing loop must include that context in its own fixed-point re-entry set.
- Fixed-point inputs for an outer loop are:
  - direct continues in the outer loop body.
  - propagated continues from inner loops after one depth decrement.
- Treat `Break _`, `Return`, and `Panic` as non-re-entry exits for the current
  loop.
- Preserve current behavior for loops with only local continue/break.

Verification:

- Run focused tests where the inner loop has both a local `continue` and an
  outer `continue`.
- Run a test where the outer loop fixed point changes only because of a
  propagated continue from the inner loop.
- Run existing nested loop tests to ensure ordinary inner loops still compute
  fixed points.
- Run `cd src && dune build`.

Tests should assert:

- Fixed-point inputs for an inner loop are computed only from local re-entry
  paths.
- Propagated outer continues do not pollute the inner loop's fixed point.
- Once consumed by the outer loop, propagated continues do contribute to the
  outer loop's fixed point.

Expected result:

- Fixed-point computation is local to the current loop but complete for enclosing
  loops.

Implementation:

- `InterpLoopsFixedPoint.classify_loop_entry_result` now classifies loop-body
  results before fixed-point entry joining:
  - `Continue 0` is the current loop's re-entry.
  - `Continue i` for `i > 0` is a propagated continue with remaining depth
    `i - 1`, not a re-entry for the current loop.
  - `Break _`, `Return`, and `Panic` are non-re-entry exits.
- `compute_loop_entry_fixed_point` no longer rejects direct outer continues.
  It logs them as propagated exits and excludes them from the current loop's
  fixed-point join.
- `src/loop_fixed_point_entry_test.ml` pins the classifier contract, including
  negative-depth rejection.
- `tests/src/loops-nested-continue-control.rs` records the current end-to-end
  state for continue-only nested-control examples: outer continues move past
  fixed-point entry and now fail later in loop synthesis (`InterpLoops.ml`).
  Break-containing nested-control examples still stop in break-context
  collection until Milestone 6 handles propagated break exits. Full runtime
  production and payload joining for propagated continues remain part of
  Milestone 6's exit-context collection.

## Milestone 6: Collect And Join Exit Contexts Per Target

Replace `compute_loop_break_context` with a function that collects all relevant
exit contexts for the current loop.

- For `Break 0`, compute the normal loop break context as today.
- For `Break i` with `i > 0`, collect a propagated break context with depth
  `i - 1`.
- For `Continue i` with `i > 0`, collect a propagated continue context with
  depth `i - 1`.
- For `Return`, collect a propagated return context.
- Join contexts per exit kind and per remaining depth, not all together.
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

- The symbolic interpreter can identify every loop exit target independently.

Implementation:

- `InterpLoopsFixedPoint.classify_loop_exit_result` now classifies loop-body
  results for exit collection:
  - `Break 0` is the current loop's normal break.
  - `Break i` for `i > 0` is a propagated break with remaining depth `i - 1`.
  - `Continue i` for `i > 0` is a propagated continue with remaining depth
    `i - 1`.
  - `Return` is a propagated return.
  - `Continue 0` and `Panic` are not break-exit contexts for this pass.
- `compute_loop_exit_contexts` replaces the old single-purpose break collector.
  It preserves the normal-break fast path and groups propagated exits by kind
  and remaining depth before joining each group independently.
- Symbolic loop metadata now includes propagated exit output descriptions in
  `loop.loop_exits` alongside the normal-break mirror.
- Current loop-body synthesis still rejects propagated exits, so the known
  failures now move past fixed-point exit collection and stop in `InterpLoops.ml`.
  Consuming those collected exits in synthesized loop bodies remains the next
  milestone.
- `src/loop_exit_contexts_test.ml` pins the exit classification and propagated
  exit grouping contracts.

## Milestone 7: Reconcile Borrows And Abstractions Across Loop Boundaries

Make the risky context-boundary behavior explicit before returning multiple
symbolic loop results.

- Define which loop owns each abstraction introduced during fixed-point
  computation.
- When an inner loop propagates an exit, end or consume the inner loop's own
  abstractions before handing the context to the enclosing loop.
- Translate inner-loop output abstractions into values/backward continuations
  expected by the target loop, or prove they are not visible outside the inner
  loop.
- Reuse `loop_match_break_ctx_with_target` / `match_ctx_with_target` patterns
  where possible, but make the target abstraction set explicit.
- For propagated `break`, reconcile the context with the target loop's break
  abstraction set.
- For propagated `continue`, reconcile the context with the target loop's
  fixed-point abstraction set.
- For propagated `return`, reconcile the context with the function return /
  backward-function boundary.
- Ensure fresh abstraction ordering is stable after reconciliation.
- Ensure dummy variables and symbolic values introduced by the inner loop do not
  escape unless they are part of the target payload.

Verification:

- Add borrow-sensitive tests for propagated `break`, propagated `continue`, and
  propagated `return`.
- Add a test where an inner loop creates fresh abstractions that should not be
  visible after a propagated outer break.
- Run with sanity checks where available:
  - `AENEAS_OPTIONS=-checks make test-loops-nested-control.rs`
  - `AENEAS_OPTIONS=-checks make test-loops-nested.rs`
- Run `cd src && dune build`.

Tests should assert:

- Borrow/loan/abstraction invariants hold after each propagated exit.
- Propagated break contexts can join with direct outer break contexts.
- Propagated continue contexts can join with direct outer continue contexts.
- No inner-loop-owned abstraction id appears in the outer context unless it has
  been intentionally translated into the target payload.

Expected result:

- Propagated exits carry contexts that are shape-compatible with their target
  loop or function boundary.

Implementation:

- Loop-body synthesis now reconciles direct `Break i` / `Continue i` for
  `i > 0` and `Return` against the propagated exit contexts collected by
  `compute_loop_exit_contexts`.
- Each propagated branch is matched against its per-kind/per-depth joined exit
  context with the same `loop_match_break_ctx_with_target` path used for normal
  joined breaks. This keeps borrow, loan, abstraction, symbolic value, and dummy
  variable reconciliation explicit.
- Synthesized symbolic bodies now emit `LoopExit (PropagatedBreak depth)`,
  `LoopExit (PropagatedContinue depth)`, and `LoopExit PropagatedReturn` for
  those branches. Normal `Break 0` and `Continue 0` behavior is unchanged.
- `same_propagated_exit_kind` is exported from `InterpLoopsFixedPoint` so
  synthesis and exit-context grouping use the same target equality.
- Added focused borrow-sensitive known-failure fixtures for propagated break,
  propagated continue, and propagated return. They now reach the expected pure
  lowering boundary instead of failing in symbolic loop synthesis.
- Added a three-level nested-break known-failure fixture to pin the synthesis
  depth decrement with `PropagatedBreak 1`.
- Propagated-exit synthesis now checks that collected exit targets are unique
  and reports the missing or duplicate target kind if the collector/synthesizer
  invariant is violated.
- Returning multiple symbolic statement results is handled by Milestone 8, and
  pure lowering of propagated loop exits remains Milestone 9.

## Milestone 8: Return Multiple Results From Symbolic Loop Evaluation

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
- Verify concrete execution after pre-pass changes. The concrete loop evaluator
  should not need semantic changes if relative depths are preserved.

Verification:

- Run existing switch/branch tests that produce multiple contexts.
- Run focused tests where after-loop code must execute only for normal break.
- Run concrete-execution tests or `-test-trans-units` checks that exercise
  nested `break`/`continue` after pre-pass support.
- Run `cd src && dune build`.

Tests should assert:

- Statements after the inner loop execute on normal inner break.
- Statements after the inner loop do not execute on propagated outer break,
  propagated outer continue, or propagated return.
- Statements after the outer loop execute only for normal outer break.
- Concrete and symbolic statement results agree on depth decrement.

Expected result:

- Symbolic statement sequencing sees loop exits just like it sees branch exits.

Implementation:

- `eval_loop_symbolic` now returns a statement-result list. The normal loop
  completion path is `(break_ctx, Unit)`, and each collected propagated exit
  contributes its reconciled context paired with `Break depth`,
  `Continue depth`, or `Return`.
- `eval_loop` in symbolic mode now forwards the loop result list directly to
  statement sequencing instead of collapsing it back to a singleton result.
- The loop expression continuation still consumes only the normal-break
  `next_expr`; propagated exits are already represented in the loop body as
  `LoopExit Propagated*` nodes and remain blocked at pure lowering until
  Milestone 9. The discarded propagated expression tail is explicit in the code
  and relies on statement sequencing threading only identity expressions for
  those propagated branches until Milestone 9 rewires pure lowering.
- The function-boundary `Return` path already consumes the propagated return
  result through the same `eval_function_body` / `evaluate_function_symbolic`
  finish path as natural returns: the reconciled exit context is paired with
  `Return`, then the caller pops the return value and synthesizes forward and
  backward endings normally.
- Verified that ordinary loop translations still pass after the pre-pass
  changes. Added concrete `-test-units` checks for nested `break 'outer` and
  `continue 'outer`; no concrete loop evaluator changes were needed.

## Milestone 9: Lower Symbolic Loop Exits To Typed Pure Control Flow

Update `SymbolicToPureExpressions.translate_loop` and related context helpers.

- Stop ignoring the loop id in `translate_continue_break`.
- Replace the single active `mk_continue` / `mk_break` pair with target-aware
  loop-control callbacks, or lower all non-current exits through explicit loop
  result payloads before translation.
- Use the committed exit encoding from Milestone 2.
- Generate an after-loop dispatch:
  - normal break payload goes to `next_expr`.
  - propagated break payload goes to the enclosing loop's break callback.
  - propagated continue payload goes to the enclosing loop's continue callback.
  - propagated return payload goes to the function return callback.
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

Implementation:

- `SymbolicToPureExpressions.translate_loop` now lowers loops with propagated
  scalar exits to `TLoopExit` payloads carried by the loop's break result.
- Multiple propagated break or continue depths from the same loop are encoded
  with nested `TSum` payloads under the corresponding `TLoopExit` constructor.
- After-loop dispatch matches on `NormalBreak`, `PropagatedBreak`,
  `PropagatedContinue`, and `PropagatedReturn` and forwards each scalar
  propagated exit to the enclosing break, continue, or return callback.
- `translate_continue_break` and `translate_loop_exit` validate the source loop
  id against the currently active loop body before lowering the control node.
- Propagated exits that carry abstraction continuations now stop at an explicit
  Milestone 10 boundary instead of flowing into an incorrectly typed outer-loop
  break payload.
- `loops-nested-control-scalar.rs`,
  `loops-nested-continue-control.rs`, and
  `loops-nested-depth-break-control.rs` generate Lean with explicit `LoopExit`
  dispatch.

## Milestone 10: Design And Implement Backward Functions For Multi-Exit Loops

Handle loop-generated backward functions explicitly.

- Determine the backward signature for a loop with multiple exit kinds.
- The backward input must include which exit happened and the exit payload, or an
  equivalent typed value derived from the committed exit encoding.
- For each exit kind, generate the backward behavior that consumes that exit's
  payload and produces the consumed-borrow results expected by loop inputs.
- Ensure propagated `return` carries enough information for function-level
  backward functions.
- Ensure propagated `break` and `continue` carry enough information for target
  loop backward functions.
- Update naming and pretty-printing so generated backward functions remain
  inspectable.

Verification:

- Add tests with mutable borrows and multiple exit kinds from one inner loop.
- Add a test where different exit kinds consume different borrows.
- Generate backend code and inspect the loop backward function signatures.
- Run `cd src && dune build`.

Tests should assert:

- Backward function inputs include exit discrimination.
- Each exit branch returns consumed-borrow results of the expected type.
- Existing simple-loop backward signatures remain unchanged when no propagated
  exits are present.

Expected result:

- Multi-exit loops are sound for forward and backward translation.

Implementation:

- `SymbolicAst.loop_exit` now carries an optional per-exit branch expression.
  Symbolic loop evaluation attaches the statement-sequencing expression for each
  propagated exit to the matching exit descriptor.
- Pure lowering binds the `TLoopExit` payload first, then translates the attached
  propagated-exit branch body in that payload context. This lets the existing
  context-matching synthesis produce the enclosing loop break/continue or
  function return payload, including branch-specific backward continuations.
- Propagated exits with abstraction continuations no longer stop at the
  Milestone 9 guard. Their `TLoopExit` payloads include the exit discriminator
  and any backward functions needed by that branch.
- The borrow-sensitive break, continue, return, and combined nested-control
  fixtures now generate Lean instead of known-failure outputs.

## Milestone 11: Update Pure Loop Micro-Passes

Audit and update `src/pure/PureMicroPassesLoops.ml`.

- Update passes that inspect `TLoopResult` constructors so they understand the
  committed exit encoding.
- Preserve simplifications for ordinary loops.
- Update loop input/output filtering to account for all exit payloads.
- Update recursive-loop conversion if nested exits interact with `RecLoopCall`.
- Update loop decomposition so generated auxiliary loop definitions expose the
  right output type and backward signature.

Verification:

- Run:
  - `make test-loops.rs`
  - `make test-loops-rec.rs`
  - `make test-loops-nested.rs`
  - `make test-loops-nested-rec.rs`
  - `make test-loops-nested-control.rs`
- Compare generated output for existing tests and keep churn explainable.

Tests should assert:

- Useless loop input/output filtering does not remove values needed by any exit
  payload.
- Recursive-loop extraction still works for ordinary nested loops.
- If recursive-loop extraction cannot support propagated exits initially, it
  fails with a targeted error and the non-recursive loop path passes.

Expected result:

- Pure micro-passes preserve and simplify nested-exit control flow correctly.

Implementation:

- Audited `PureMicroPassesLoops.ml` after Milestone 10. The existing loop
  decomposition and recursive-loop conversion paths already treat a propagated
  `TLoopExit` result as an ordinary single loop output, while continuing to use
  `TLoopResult` only for loop-body continue/break/failure conversion.
- Added `loops-nested-control-rec.rs` to pin recursive-loop extraction for
  propagated break, propagated continue, propagated return, and a borrow-backed
  propagated break payload. The generated Lean contains recursive loop
  definitions whose `LoopExit` payloads preserve the needed backward function.

## Milestone 12: Update Extraction Backends

Update extraction code and backend primitives as required by the committed exit
encoding.

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

Implementation:

- The existing shared builtin mappings cover `TLoopExit` and `TSum` names for
  Lean, Coq, F*, and HOL4. The backend fixture now pins the emitted Lean,
  Coq, and F* syntax for propagated break, continue, return, and multiple
  propagated break depths.
- Added `loops-nested-control-backends.rs` and committed the generated
  backend outputs. Coq and F* misc primitives now include the copied
  `aeneas_sum` encoding required by nested propagated-exit payloads; Lean uses
  the existing `AeneasSum` and `LoopExit` primitives and the lakefile lists the
  new nested-control modules.
- Backend generation passes for `loops-nested-control-backends.rs`,
  `loops-nested-control.rs`, and `loops-nested.rs`. Backend verification was
  attempted, but the local environment is missing `lake`, `coq_makefile`, and
  `fstar.exe`.

## Milestone 13: Remove Known-Failure Status And Update Documentation

Once support is complete, update tests and docs.

- Remove `known-failure` from `tests/src/loops-nested-control.rs`.
- Commit generated backend outputs.
- Update `README.md` to remove the loop limitation.
- Update `docs/user/src/README.md` if it still mentions no nested loops.
- Check `documentation/getting-started.md` and `documentation/skills/*.md` for
  any stale limitation text.
- Add a short note to tests or docs explaining supported loop-control forms.

Verification:

- Run:
  - `make test-loops-nested-control.rs`
  - `make test`
  - relevant `make verify-*` targets.
- Confirm documentation no longer claims unsupported nested loop exits.

Tests should assert:

- All new examples translate successfully.
- Existing loop tests still translate and verify.
- Documentation matches actual behavior.

Expected result:

- The safe subset officially supports nested returns and outer break/continue.

Implementation:

- Removed the stale nested-loop limitation from the public README and user
  guide. `documentation/getting-started.md` and `documentation/skills/*.md`
  contain no stale nested-loop limitation text.
- Removed the remaining known-failure-boundary comments from the isolated
  borrow-sensitive nested-control fixtures.
- Regenerated backend outputs after the final nested-control changes. During
  full regression testing, user-level `sum` declarations collided with the
  builtin propagated-exit sum in Lean, Coq, and F*. The generated builtin is now
  named `AeneasSum` for Lean and `aeneas_sum` for Coq/F*, while HOL4 keeps
  `sum`.
- Added extraction-name coverage for the backend-specific propagated-exit sum
  type and variant names.
- `make test`, `make test-loops-nested-control.rs`,
  `make test-loops-nested-control-scalar.rs`,
  `make test-loops-nested-control-backends.rs`, `make test-arrays.rs`,
  `make test-no_nested_borrows.rs`, `dune build`, and
  `dune runtest ./loop_exit_shape_test.exe` pass locally. Backend verification
  was attempted, but the local environment is missing `lake`, `coq_makefile`,
  and `fstar.exe`.

## Final Acceptance Criteria

- Charon relative-depth assumptions are verified.
- `break 'outer` works from nested loops.
- `continue 'outer` works from nested loops.
- `return` works from nested loops.
- Propagated continues feed the target loop fixed point after depth decrement.
- Support works for scalar-only code and mutable-state code that affects loop
  output contexts.
- Borrow, loan, abstraction, symbolic value, and dummy-variable invariants hold
  across propagated loop exits.
- Loop backward functions are sound for multi-exit loops.
- Existing loop tests continue to pass.
- Generated pure code is typed and backend output verifies for supported
  backends.
- No assertions remain that reject supported nested loop exits.
- README limitation is removed only after tests and backend generation pass.
