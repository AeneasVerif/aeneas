# Separation Logic Proof of Concept

This directory contains the proof-of-concept work for extending the separation
logic (SL) support.

## Updating the stacked branches

`cezar/firstorder_seplogic` is stacked on `cezar/tactic-step`. After committing
in the `tactic-step` worktree, update both remote branches and replay the SLPoC
commits on the new tactic commit:

```bash
git push origin cezar/tactic-step
git -C ../firstorder_seplogic rebase cezar/tactic-step
git -C ../firstorder_seplogic push --force-with-lease origin cezar/firstorder_seplogic
```

## Files

| File | Purpose |
|---|---|
| [`FFree.lean`](FFree.lean) | Defines the generic freer monad, and the state machines that give it an operational semantics (after "Program Logics à la Carte"): `StateMachine`, `Exec`, `Runs` and `Evaluates`. |
| [`Heap.lean`](Heap.lean) | Defines locations, dynamically typed cells, finite heaps, and the sub-heap order the affine assertions are closed under. |
| [`RustHeap.lean`](RustHeap.lean) | The Rust view of the heap: `Ptr` and the pointer operations, over `Heap.lean`. |
| [`SLTactics.lean`](SLTactics.lean) | Port of the SLF tactics: `sl_frame`, `sl_pull`, `sl_xchange`, …, including the affine discard of whatever a cancellation leaves over. |
| [`ST.lean`](ST.lean) | The state monad `St`, its state machine, its denotation `theta` into `Wp`, the Hoare triples it induces, and the specifications of the pointer operations. |
| [`Step.lean`](Step.lean) | Wires triples into `sl_step`/`sl_step*` and provides `sl_pure` for exposing the entailment of a syntactic terminal return. |
| [`WP.lean`](WP.lean) | Affine separation-logic assertions (`SLProp`, closed under heap extension like Iris's `uPred`), the magic wand, and the `Wp` monad of predicate transformers. |
| [`Run.lean`](Run.lean) | The certified interpreter: runs a program whose weakest precondition is proved, reading the ownership witnesses every read, write and deallocation needs off that proof. |
| [`ProofScore.lean`](ProofScore.lean) | Engineering tool, not part of the library: measures how close the proofs of the triples are to the ideal proof, i.e. how much separation logic the automation still leaves to the user. Writes [`proof-score.html`](proof-score.html). |
| [`proof_simplify.py`](proof_simplify.py) | Compilation-guided proof simplifier: compresses consecutive `sl_step` calls and removes unused `sl_pull` names, retaining only rewrites accepted by Lean. |
| [`benchmark-report.md`](benchmark-report.md) | Report on the eleven external benchmark ports, their interfaces and specifications, proof-score improvements, and remaining automation gaps. |
| [`automation-report.md`](automation-report.md) | Maps ideas from Dardinier's thesis on automated separation-logic verifiers to a prioritized design for more SLPoC proof-mode automation. |
| `README.md` | Records the purpose and meaning of files in this directory. |

| File in [`Examples/`](Examples) | Purpose |
|---|---|
| [`AsterinasIntrusiveFrameList.lean`](Examples/AsterinasIntrusiveFrameList.lean) | Port of Asterinas's intrusive frame list: allocation-free push/pop and cursor removal with exclusive detached-frame ownership. |
| [`Basic.lean`](Examples/Basic.lean) | Basic programs and specifications exercising `step` over pure computations and pointers. |
| [`CreusotListReversalLasso.lean`](Examples/CreusotListReversalLasso.lean) | Port of Creusot's cyclic-list reversal over an explicit first-order memory, with exact traversal and rewiring results. |
| [`DardinierMagicWands.lean`](Examples/DardinierMagicWands.lean) | Ports Dardinier's leftmost-leaf wand-packaging example and the uniform-footprint counterexample from *Sound Automation of Magic Wands*. |
| [`EqOrDisj.lean`](Examples/EqOrDisj.lean) | The `InPlaceOrDisjointBuffer` interface of [SymCRust](https://github.com/microsoft/VCR) — a read/write view pair that either aliases or is separated — specified in full against equal-or-disjoint ghost state. |
| [`IrisTutorial.lean`](Examples/IrisTutorial.lean) | Sequential ports of Iris tutorial proof-mode, pointer, and linked-list examples. |
| [`PulseArrayTests.lean`](Examples/PulseArrayTests.lean) | Cell-wise array model and ports of Pulse allocation/free, indexed access, fill, and exact comparison examples. |
| [`PulseInsertionSort.lean`](Examples/PulseInsertionSort.lean) | In-place Pulse insertion sort with sortedness and permutation proofs. |
| [`PulseLinkedList.lean`](Examples/PulseLinkedList.lean) | Sequential Pulse linked-list operations over a recursive ownership predicate, including append, split, insertion, and reversal. |
| [`PulseResizableVec.lean`](Examples/PulseResizableVec.lean) | Pulse bounded resizable vector with separate size/capacity cells and initialized-prefix ownership. |
| [`PulseRingBuffer.lean`](Examples/PulseRingBuffer.lean) | Pulse fixed-capacity FIFO ring buffer with circular-layout and wrap-around proofs. |
| [`Run.lean`](Tests/Run.lean) | Regression tests for the interpreter: running verified programs, and what execution shows that an affine triple cannot. |
| [`UnitTest.lean`](Tests/UnitTest.lean) | Regression tests for `step`, `sl_step`, and the separation-logic tactics. |
| [`YOLOCancel.lean`](Examples/YOLOCancel.lean) | Memory-bounded, downscaled ports of YOLO's synthetic shuffled-atom cancellation benchmarks. |
| [`VerusBitmap.lean`](Examples/VerusBitmap.lean) | Verus bitmap over 64-bit-style words, including exact get/set and pointwise OR refinement proofs. |
| [`VerusDoublyLinkedList.lean`](Examples/VerusDoublyLinkedList.lean) | Port of the Verus doubly-linked-list example: executable definitions, then ghost state, specifications and proofs. |
| [`VerusMimallocLinkedList.lean`](Examples/VerusMimallocLinkedList.lean) | Port of mimalloc's free-list kernel with typed header/padding split and whole-block ownership transfer. |
| [`VerusPageTable.lean`](Examples/VerusPageTable.lean) | Uniform-leaf, exact-key subset of verified-pt map/query/unmap/prune with recursive table ownership and explicit allocation/free operations. |
| [`VerusStd.lean`](Examples/VerusStd.lean) | The `vstd` layer: generic sequences of pointer/payload pairs and permission maps over them, with each declaration naming its `vstd` counterpart. Independent of any data structure. |
| [`VerusVerifiedVec.lean`](Examples/VerusVerifiedVec.lean) | Fixed-capacity adaptation of Verus's initialized-prefix vector, using typed `Option` cells for the abstract raw suffix. |
| [`doubly_linked_loc.py`](Examples/doubly_linked_loc.py) | Deterministically regenerates the relevant-LOC comparison with the pinned Verus example below. |

Keep these tables updated whenever a file is added, removed, or repurposed.

The logic is affine the way Iris's is, rather than the way SLF's
[Affine Separation Logic](https://softwarefoundations.cis.upenn.edu/slf-current/Affine.html)
is: affinity is a property of the *model*, not an extra `GC` written into the
triples. An `SLProp` is closed under heap extension — it owns the cells it
describes and says nothing about the others — exactly like Iris's `uPred`.
Consequently:

* the entailment weakens: `H ⊢ emp` for every `H`, so `sl_frame`/`sl_xsimpl`
  drop whatever a cancellation leaves over;
* `emp`, `GC` and `⌜True⌝` all hold of every heap — `GC` is *definitionally*
  `emp`, and is kept only so that SLF-shaped statements keep parsing;
* `triple P m Q` is `theta m ≤ pp2wp P Q`, with no `∗+ GC` in the
  postcondition, and unused resources may still be discarded from either side.

What affinity does *not* change: separation is still separation, so `p ↦ v ∗ p ↦
w ⊢ ⌜False⌝`, and a specification still has to own what it reads or writes.
Leak-freedom claims are out of scope, as they already were.

## Three semantics for `St`

A program has an *operational* semantics (`StEvents.Step`, lifted to the
big-step `Evaluates` of `FFree.lean`), a *denotational* one (`theta`, into the
weakest-precondition monad), and — in [`Run.lean`](Run.lean) — an *executable*
one.

`St` cannot be interpreted unconditionally: a heap cell stores its own Lean type
(`HeapCell = Σ α : Type, α`), so `Ptr.contains h p` is not decidable and a read
through a dangling or mistyped pointer is stuck rather than erroneous. The
program logic supplies what is missing, so `run` takes the weakest precondition
as an argument and reads the ownership witnesses off it. Proofs are erased at
run time, so this computes:

```lean
theorem roundTrip.spec : (roundTrip) ⦃⇓ result => result = 42⦄ := by
  unfold roundTrip; sl_step*

#eval (execClosed roundTrip roundTrip.spec).1  -- 42
```

`run` is certified: it returns the postcondition and the `Evaluates` derivation
alongside the answer, so `(execClosed roundTrip roundTrip.spec).1 = 42` is
`execClosed_post`, with nothing executed and nothing re-proved.

Execution also shows what an affine triple cannot state. `⦃emp⦄ m ⦃⇓ emp⦄` holds
of a program that frees what it allocates *and* of one that leaks it; running a
closed program tells the two apart, and `by rfl` proves the difference — see
[`Tests/Run.lean`](Tests/Run.lean).

## How ideal are the proofs?

The point of the automation is that a triple should be proved by unfolding the
program and calling `sl_step*`, `step`, or `step*`, with only pure reasoning and
`sl_pull` in between, and one such block per branch of the program.  A manual
`sl_pure` is not ideal: stepping should handle the terminal return.  Similarly,
`sl_step with some.spec` is not ideal whenever the named declaration states a
triple, regardless of whether it is registered with `@[step]`; local induction
hypotheses remain ideal.  Run

```
lake env lean --run Aeneas/SLPoC/ProofScore.lean
```

from `backends/lean` to measure how far the proofs are from that, in
[`proof-score.html`](proof-score.html): every proof of a triple is split into
*spots* — one straight-line block before the first branch, then one per branch
body, recursively — and a spot counts as ideal when no step of it steers the
separation logic by hand.  The report names the offending step and says what
gave it away, so it doubles as a to-do list for the automation.

The page is standalone, and fetches nothing from anywhere.  Every file is a
collapsible section listing its proofs and spots. Each spot includes its number
of lines of code and its own code — the nested blocks elided as `…`, the
comments left out — highlighted and framed in green or red according to the
verdict, with the offending lines shaded.  The toggle at the top switches
between all the spots, only the ideal ones, and only those that are not.

The tool parses with Lean's own parser but elaborates nothing except the
commands that open a namespace, so it takes about a second and also works on a
file that does not compile; a file whose module has been built is additionally
imported, which makes the notation it defines available.  Pass file paths to
score files other than those of [`Examples/`](Examples), and `-o` to write the
report elsewhere.

## Simplifying proofs

Run the compilation-guided simplifier from `backends/lean`:

```
python3 Aeneas/SLPoC/proof_simplify.py FILE.lean
python3 Aeneas/SLPoC/proof_simplify.py --in-place FILE.lean
```

The default mode prints a unified diff.  `--in-place` applies it, and `--check`
exits with status 1 when a file can be simplified.  The tool first tries to
replace each `sl_pure` with `sl_step`.  For replacements Lean rejects, it then
tries to merge an adjacent `sl_pure`/step pair.  Next it tries to drop explicit
`sl_pull` patterns and replace individually unused simple names with `_`.
Compressing consecutive plain `sl_step` calls is the final stage: it validates
`sl_step* N`, then immediately tries to remove each newly created bound.
Bounds already present in the input are not retried.  Each proposed rewrite is
retained only when `lake env lean --stdin` accepts the complete resulting file.

To keep compiler use bounded, step-run and binder rewrite classes are validated
as batches; `sl_pull` names are first checked for lexical use in their tactic
scope.  Mixed successful and unsuccessful `sl_pure` replacements and step pairs are
bisected separately.  No Lean invocation is made when lexical analysis finds
nothing to rewrite.

Rejected candidates are reported on standard error with their source line,
proposed replacement, batch size, and the first error returned by Lean.  This
distinguishes a fully simplified file from one where potential rewrites were
tried but did not compile.

## Doubly-linked-list LOC comparison

Run `python3 Aeneas/SLPoC/doubly_linked_loc.py` from `backends/lean` to
regenerate this report, or pass `--check` to verify that it is current. The
script fetches an exact Verus commit and verifies its SHA-256 checksum before
counting. It counts declaration lines and body lines after removing comments,
blank lines, imports/uses, namespaces/modules, standalone delimiters, and
other non-definition scaffolding. Language-level markers such as `by`, `do`,
`proof`, `requires`, `ensures`, `invariant`, and `decreases` are counted.

Verus imports `vstd`, so its sequence, map and permission reasoning costs it no
lines here.  The Lean side has to build that layer, which is why it is kept in
`VerusStd.lean` and reported separately: that module is generic, knows nothing
about doubly-linked lists, and is reusable by any development using the same
"ghost sequence of pointers plus permission map" pattern.  The figure comparable
with Verus is therefore the "Lean example total".

<!-- BEGIN GENERATED DOUBLY LINKED LOC REPORT -->

Pinned Verus source: [`99ae45aa8e35`](https://github.com/verus-lang/verus/blob/99ae45aa8e3568ec4933d23c6573a59efcd08ca3/examples/doubly_linked.rs) (SHA-256 `52abe834f0d6596bbaebcabb92330476707df184bb5456aeaf7c573ac01394c3`).

| Source | Declarations | Relevant LOC |
|---|---:|---:|
| Verus | 24 | 339 |
| Lean executable definitions | 14 | 84 |
| Lean ghost state, specifications and proofs | 36 | 241 |
| **Lean example total** | **50** | **325** |
| `vstd` equivalent, generic and reusable (`VerusStd.lean`) | 24 | 98 |
| Lean grand total | 74 | 423 |

| Definition or semantic group | Verus | Lean (executable, spec/proof) |
|---|---:|---:|
| `Node` | 4 | 4 (4, 0) |
| `DoublyLinkedList` | 4 | 3 (3, 0) |
| ghost state / `Cells` | 3 | 1 (0, 1) |
| `prev_of` / `prevOf` | 5 | 2 (0, 2) |
| `next_of` / `nextOf` | 5 | 2 (0, 2) |
| `well_formed_node` / `nodeAt` | 5 | 2 (0, 2) |
| `well_formed` / representation predicates | 7 | 4 (0, 4) |
| `view` | 4 | 1 (0, 1) |
| `new` | 10 | 7 (2, 5) |
| `push_empty_case` / `pushEmptyCase` | 17 | 9 (3, 6) |
| `push_back` / `pushBack` | 36 | 25 (9, 16) |
| `pop_back` / `popBack` | 42 | 22 (12, 10) |
| `push_front` / `pushFront` | 46 | 28 (9, 19) |
| `pop_front` / `popFront` | 49 | 19 (12, 7) |
| `get` (including the Lean loop) | 27 | 38 (13, 25) |
| `Iterator` | 4 | 4 (4, 0) |
| `Iterator::list` | 2 | 0 (0, 0) |
| `Iterator::index` | 2 | 0 (0, 0) |
| `Iterator::valid` | 4 | 3 (0, 3) |
| `Iterator::new` | 9 | 9 (2, 7) |
| `Iterator::value` | 10 | 13 (4, 9) |
| `Iterator::move_next` / `moveNext` | 20 | 26 (7, 19) |
| `main::run` / example | 22 | 29 (0, 29) |
| entry-point `main` | 2 | 0 (0, 0) |
| Other support declarations | - | 74 (0, 74) |
| **Total** | **339** | **325 (84, 241)** |

`VerusStd.lean` (24 declarations, 98 lines) is not compared declaration by declaration: it is the generic sequence and permission-map layer that Verus obtains from `vstd`, it does not mention the doubly-linked list, and each of its declarations names its `vstd` counterpart in its doc comment.

"Other support declarations" contains 0 Verus, 0 Lean executable, and 14 Lean specification/proof declarations not assigned to a direct cross-language correspondence above, together with the `attribute` commands that configure the automation.

<!-- END GENERATED DOUBLY LINKED LOC REPORT -->
