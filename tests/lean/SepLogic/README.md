# Separation Logic Proof of Concept

This directory contains the proof-of-concept work for extending the separation
logic (SL) support.

## Updating the stacked branches

`cezar/firstorder_seplogic` is stacked on `cezar/integration`. After updating
the integration branch, replay the SLPoC commits on it:

```bash
git -C ../firstorder_seplogic rebase cezar/integration
git -C ../firstorder_seplogic push --force-with-lease origin cezar/firstorder_seplogic
```

## Files

| File | Purpose |
|---|---|
| [`Coinductive/Spec.lean`](../Data/Coinductive/Spec.lean) | Generic `Handler`, `TotalSpec`, and `PartialSpec`, their shared layer `SpecF`, structural rules, and admissibility for conjunctive handlers. Shared with `Std/WP.lean`. |
| [`StateMachine.lean`](StateMachine.lean) | Operational semantics for those handlers (after "Program Logics à la Carte"): `Exec`, `Handler.Runs`, and `Handler.Evaluates`, with the adequacy proofs connecting the generic correctness judgments to runs. |
| [`Heap.lean`](../Std/Heap.lean) | Defines addresses (`AllocId × Nat`), finite heaps of slots under disjoint union, their PCM instance, references and their arithmetic, the heap of a run of slots, allocation, and the sub-heap order the affine assertions are closed under. |
| [`Primitives.lean`](../Std/Primitives.lean) | Defines `Result`, the interaction-tree monad over the `RustEffect` heap events (`guardedModify` and `fail`), its monad and partial-fixpoint instances, and the `loop` combinator. |
| [`PartialCommMonoid.lean`](../Data/PartialCommMonoid.lean) | The `PartialCommMonoid` class the heap is an instance of: a total union selected by a compatibility relation. |
| [`MutableData/Array.lean`](MutableData/Array.lean) | Arrays `Array α n`, the Rust `[α; n]`: the length lives in the type.  `toBuffer` is the coercion to a slice, and every operation and specification is the buffer one with `n` for the length. |
| [`MutableData/Ptr.lean`](MutableData/Ptr.lean) | The first layer: allocation of a run of slots, interior pointers `Ptr α`, pointer arithmetic, range and slot ownership, splitting and joining, read, write and free of one slot, the range operations `freeRange`/`fillRange`/`copyRange`/`compareRange`, and the raw-pointer borrow.  A `Ref` never escapes this directory. |
| [`MutableData/Buffer.lean`](MutableData/Buffer.lean) | Slices `Buffer α`, the Rust `&mut [T]`: `sub`, `split`, `join`, slot-level and array-level indexed access, `alloc`/`ofList`/`free`/`fill`/`copy`/`compare`/`swap`, and how ownership follows the views. |
| [`ST.lean`](ST.lean) | The heap handler `RustEffect.machine`, whose event semantics is `EventSpec`; the generic judgments specialized as `spec` and `dspec`; and the separation triples, framing and loop rules, and `step` integration. The pure judgments `WP.spec` and `WP.dspec` wrap triples with no owned input and a pure postcondition and have their own `step` registrations. |
| [`Semantics.lean`](Semantics.lean) | What those triples say about running the program: the relations `Reaches` and `Evaluates` for `RustEffect.machine`, the adequacy of `dspec`/`dtriple`, and the certified interpreter (`exec`, `execTriple`, `execClosed`) that uses a total-correctness proof to run a verified program. |
| [`Basic.lean`](../SepLogic/Basic.lean) | Affine separation-logic assertions (`IProp`, closed under heap extension like Iris's `uPred`), the separating conjunction, the quantifiers, and the magic wand. |
| [`PredicateTransformer.lean`](../SepLogic/PredicateTransformer.lean) | Monotone predicate transformers `Wp` over those assertions (`Wᴾᵘʳᵉ` of "Dijkstra Monads for All"), and `pp2wp`, the transformer a precondition/postcondition pair denotes. |
| [`Tactic/SepLogic/`](../Tactic/SepLogic) | The separation-logic proof mode: `Init.lean` registers the `iris_simps` simp set, `Frame.lean` holds the `IFrame` cancellation engine with `iframe`/`isimp`, `Intro.lean` holds the `iintro` family and `isimpl`, `Rewrite.lean` holds `irewrite`, and `Tests/` holds one regression file per tactic. |
| [`ProofScore.lean`](Tests/Examples/scripts/ProofScore.lean) | Engineering tool, not part of the library: measures how close the proofs of the triples are to the ideal proof, i.e. how much separation logic the automation still leaves to the user. Writes [`proof-score.html`](Tests/Examples/reports/proof-score.html). |
| [`SourceLoc.lean`](Tests/Examples/scripts/SourceLoc.lean) | Engineering tool, not part of the library: downloads the artifacts every example ports, and unverified Rust implementations of the same data structures, and counts the relevant lines of all three, per file and per declaration, split into computational code, specification/annotation, and proof. Writes [`source-loc.json`](Tests/Examples/reports/source-loc.json), and a standalone `source-loc.html` that draws it (generated on demand, not committed). |
| [`sources-manifest.json`](Tests/Examples/reports/sources-manifest.json) | Maps every file of `Tests/Examples` to the upstream artifact it ports, pinned to a commit and a SHA-256, says whether the example is expressible in safe Rust and why, and lists unverified Rust implementations of the same data structure. Read by `SourceLoc.lean`. |
| [`proof_simplify.py`](Tests/Examples/scripts/proof_simplify.py) | Compilation-guided proof simplifier: compresses consecutive `step` calls and removes unused `sl_pull` names, retaining only rewrites accepted by Lean. |
| [`benchmark-report.md`](Tests/Examples/reports/benchmark-report.md) | Report on the eleven external benchmark ports, their interfaces and specifications, proof-score improvements, and remaining automation gaps. |
| [`automation-report.md`](Tests/Examples/reports/automation-report.md) | Maps ideas from Dardinier's thesis on automated separation-logic verifiers to a prioritized design for more SLPoC proof-mode automation. |
| `README.md` | Records the purpose and meaning of files in this directory. |

| File under [`Tests/`](Tests) | Purpose |
|---|---|
| [`AsterinasIntrusiveFrameList.lean`](Tests/Examples/AsterinasIntrusiveFrameList.lean) | Port of Asterinas's intrusive frame list: allocation-free push/pop and cursor removal with exclusive detached-frame ownership. |
| [`Basic.lean`](Tests/Examples/Basic.lean) | Basic programs and specifications exercising `step` over pure computations and pointers. |
| [`CreusotListReversalLasso.lean`](Tests/Examples/CreusotListReversalLasso.lean) | Port of Creusot's cyclic-list reversal over an explicit first-order memory, with exact traversal and rewiring results. |
| [`DardinierMagicWands.lean`](Tests/Examples/DardinierMagicWands.lean) | Ports Dardinier's leftmost-leaf wand-packaging example and the uniform-footprint counterexample from *Sound Automation of Magic Wands*. |
| [`EqOrDisj.lean`](Tests/Examples/EqOrDisj.lean) | Port of the `InPlaceOrDisjointBuffer` of [SymCRust](https://github.com/microsoft/VCR) over `Ptr`/`Buffer` — a read/write view pair that either aliases or is separated — with its constructors, views and element accessors specified in full against equal-or-disjoint ghost state. |
| [`IrisTutorial.lean`](Tests/Examples/IrisTutorial.lean) | Sequential ports of Iris tutorial proof-mode, pointer, and linked-list examples. |
| [`Partial.lean`](Tests/Partial.lean) | Regression tests for partial correctness: the automation on a `dtriple` goal, what a partial triple still owes, and the loops only it proves. |
| [`PureSpec.lean`](Tests/PureSpec.lean) | Regression tests for the pure-computation notation: that `m ⦃ x => p ⦄` and `⦃ emp ⦄ m ⦃⇓ x => ⌜p⌝ ⦄` are the *same* proposition, the round trip through the delaborator, the interoperability one judgment buys — a pure specification framed into a heap proof, a heap proof behind a pure specification, both under one `step*`, and higher-order contracts in either form. |
| [`PulseArrayTests.lean`](Tests/Examples/PulseArrayTests.lean) | Cell-wise array model and ports of Pulse allocation/free, indexed access, fill, and exact comparison examples. |
| [`PulseInsertionSort.lean`](Tests/Examples/PulseInsertionSort.lean) | In-place Pulse insertion sort with sortedness and permutation proofs. |
| [`PulseLinkedList.lean`](Tests/Examples/PulseLinkedList.lean) | Sequential Pulse linked-list operations over a recursive ownership predicate, including append, split, insertion, and reversal. |
| [`PulseResizableVec.lean`](Tests/Examples/PulseResizableVec.lean) | Pulse bounded resizable vector with separate size/capacity cells and initialized-prefix ownership. |
| [`PulseRingBuffer.lean`](Tests/Examples/PulseRingBuffer.lean) | Pulse fixed-capacity FIFO ring buffer with circular-layout and wrap-around proofs. |
| [`Array.lean`](Tests/Array.lean) | Regression tests for the array interface: every operation run end to end by the interpreter, and the lemmas relating an array to the slice and the range underneath it. |
| [`Run.lean`](Tests/Run.lean) | Regression tests for the interpreter: running verified programs, and what execution shows that an affine triple cannot. |
| [`Step.lean`](Tests/Step.lean) | Regression tests for the `step` tactic. |
| [`UnitTest.lean`](Tests/UnitTest.lean) | Regression tests for `step`, `step`, and the separation-logic tactics. |
| [`YOLOCancel.lean`](Tests/Examples/YOLOCancel.lean) | Memory-bounded, downscaled ports of YOLO's synthetic shuffled-atom cancellation benchmarks. |
| [`VerusBitmap.lean`](Tests/Examples/VerusBitmap.lean) | Verus bitmap over 64-bit-style words, including exact get/set and pointwise OR refinement proofs. |
| [`VerusDoublyLinkedList.lean`](Tests/Examples/VerusDoublyLinkedList.lean) | Port of the Verus doubly-linked-list example: executable definitions, then ghost state, specifications and proofs. |
| [`VerusMimallocLinkedList.lean`](Tests/Examples/VerusMimallocLinkedList.lean) | Port of mimalloc's free-list kernel with typed header/padding split and whole-block ownership transfer. |
| [`VerusPageTable.lean`](Tests/Examples/VerusPageTable.lean) | Uniform-leaf, exact-key subset of verified-pt map/query/unmap/prune with recursive table ownership and explicit allocation/free operations. |
| [`VerusStd.lean`](Tests/Examples/VerusStd.lean) | The `vstd` layer: generic sequences of pointer/payload pairs and permission maps over them, with each declaration naming its `vstd` counterpart. Independent of any data structure. |
| [`VerusVerifiedVec.lean`](Tests/Examples/VerusVerifiedVec.lean) | Fixed-capacity adaptation of Verus's initialized-prefix vector, using typed `Option` cells for the abstract raw suffix. |

Keep these tables updated whenever a file is added, removed, or repurposed.

The logic is affine the way Iris's is, rather than the way SLF's
[Affine Separation Logic](https://softwarefoundations.cis.upenn.edu/slf-current/Affine.html)
is: affinity is a property of the *model*, not an extra affine top written into
the triples. An `IProp` is closed under heap extension — it owns the cells it
describes and says nothing about the others — exactly like Iris's `uPred`.
Consequently:

* the entailment weakens: `H ⊢ emp` for every `H`, so `iframe`/`isimpl`
  drop whatever a cancellation leaves over;
* `emp` and `⌜True⌝` both hold of every heap, so `emp` *is* the affine top and
  no separate predicate for it is needed;
* `triple P m Q` quantifies over every frame, with nothing absorbing in the
  postcondition, and unused resources may still be discarded from either side.

What affinity does *not* change: separation is still separation, so `p ↦ v ∗ p ↦
w ⊢ ⌜False⌝`, and a specification still has to own what it reads or writes.
Leak-freedom claims are out of scope, as they already were.

## The memory model: a slot at a time

An **address** is an allocation identifier together with a slot index into that
allocation, and a heap is a finite map from addresses to the values they hold:

```text
Loc      = AllocId × Nat
HeapCell = (α : Type) × α
Heap     = Loc ⇀ HeapCell            (finitely supported)
```

Two heaps compose when the addresses they use are disjoint, so `∪` is a plain
disjoint union — no PCM, and no type equality to decide.  Ownership is
*slot-granular*, which is what lets one allocation be owned a part at a time:
the `(α : Type) × List α` view of an allocation is `Ptr.pointsToRange`, the
values at consecutive addresses, and it splits and joins by regrouping a
separating conjunction.  One lemma does all of it:

```text
owns_union : Compatible A B → owns (A ∪ B) ⊣⊢ owns A ∗ owns B
```

[`MutableData/`](MutableData) builds the Rust view on that, and is the only
place a `Ref` is visible:

* [`Ptr.lean`](MutableData/Ptr.lean) — `Ptr α`, an interior pointer: a base
  address and an offset, carrying neither length nor permission.  `q ↦ value`
  owns the slot it addresses and `q ↦* values` the run from it on, and ranges
  split and join:

  ```text
  Ptr.pointsToRange_append : q ↦* xs ++ ys ⊣⊢ q ↦* xs ∗ q.add xs.length ↦* ys
  ```

  Two interior pointers may alias; their assertions compose exactly when the
  intervals they own are disjoint.  Allocation of a run lives here, as do the
  operations that walk one: `freeRange`, `fillRange`, `copyRange` and
  `compareRange`;
* [`Buffer.lean`](MutableData/Buffer.lean) — `Buffer α`, the Rust `&mut [T]`: a
  bounded view with `sub`, `split` and `join`.  The views are values; the
  lemmas beside them say how ownership follows;
* [`Array.lean`](MutableData/Array.lean) — `Array α n`, the Rust `[α; n]`.

The three layers differ only in where a length lives — nowhere for a pointer,
in a field for a slice, in the type for an array — so `a ↦ values` and
`a.toBuffer ↦ values` are *the same assertion* and ownership crosses the
coercion for free.

Each of `Array` and `Buffer` has the whole interface: `alloc`, `ofList`,
`read`, `write`, `swap`, `fill`, `copy`, `compare` and `free`.  A slot-level
specification and an array-level one are both available for a buffer's `read`
and `write`, the array-level ones owning the whole view and giving it back:

```text
Buffer.read.spec_array  : ⦃b ↦ values⦄ b.read i ⦃⇓ r => ⌜r = values[i]⌝ ∗ b ↦ values⦄
Buffer.write.spec_array : ⦃b ↦ values⦄ b.write i v ⦃⇓ b ↦ values.set i v⦄
```

Only the slot-level ones are registered with `step`; registering both would
make it ambiguous.

None of the pointer or buffer operations has a precondition: pointer
arithmetic, buffer views, allocation, reads, writes and deallocation are total
functions of their arguments.  What may go wrong is caught by the separation
logic and by the *definedness guard* of the event an operation triggers: a read
through a dangling or unowned pointer is stuck, not erroneous.

Deallocation releases the slots it owns — `Buffer.free` is `Ptr.freeRange` over
the range the view spans — so freeing part of an allocation is expressible and
frame-preserving.  `Heap.size` counts the slots a heap still holds, which is
what tells a leak from a clean run.

## Four semantics for `Result`

A program of `Result` is an **interaction tree**
([`Aeneas.Data.Coinductive.ITree`](../Data/Coinductive/ITree.lean)) over the
event signature `RustEffect`. Its handler `RustEffect.machine` gives it an
*operational* semantics via the big-step `Evaluates` of
[`StateMachine.lean`](StateMachine.lean),
a total-correctness semantics (`TotalSpec`, exposed as `spec`), a
partial-correctness one (`PartialSpec`, exposed as `dspec`) — the least and the
greatest fixed point of one shared layer `SpecF`, which differ only in what
divergence owes and share `EventSpec`, the single statement of what an event
demands of the run that follows it — and an *executable* one. The generic
judgments live in [`Coinductive/Spec.lean`](../Data/Coinductive/Spec.lean),
their heap specializations in [`ST.lean`](ST.lean), their adequacy proofs in
[`StateMachine.lean`](StateMachine.lean), and the heap semantics and interpreter
in [`Semantics.lean`](Semantics.lean).

As in `Aeneas.Std.WP.spec`, a proof of total correctness is a finite derivation:
`ret` establishes the postcondition and `vis` proves the guard and the
continuation. Nothing proves `ITree.div` correct, so every proved program
terminates. `TotalSpec.mono_le` connects this judgment to the interaction-tree
approximation order used by `partial_fixpoint`.

`Result` cannot be interpreted unconditionally either: a heap cell stores its own
Lean type (`HeapCell = Σ α : Type, α`), so `Ptr.contains h p` is not decidable
and a read through a dangling or mistyped pointer is stuck rather than
erroneous. The program logic supplies what is missing, so `run` takes the
weakest precondition as an argument and reads the ownership witnesses off it —
the interpreter `runOpt` it is built from is a `partial_fixpoint` of the tree,
not a structural recursion.  Proofs are erased at run time, so this computes:

```lean
theorem roundTrip.spec : (roundTrip) ⦃⇓ result => result = 42⦄ := by
  unfold roundTrip; step*

#eval (execClosed roundTrip roundTrip.spec).1  -- 42
```

`run` is certified: it returns the postcondition and the `Evaluates` derivation
alongside the answer, so `(execClosed roundTrip roundTrip.spec).1 = 42` is
`execClosed_post`, with nothing executed and nothing re-proved.

Execution also shows what an affine triple cannot state. `⦃emp⦄ m ⦃⇓ emp⦄` holds
of a program that frees what it allocates *and* of one that leaks it; running a
closed program tells the two apart, and `by rfl` proves the difference — see
[`Tests/Run.lean`](Tests/Run.lean).

## Partial correctness

[`ST.lean`](ST.lean) states the divergence-tolerant triple `dtriple`, written
`⦃P⦄ m ⦃⇓ x => Q⦄div`, beside the total `triple` — the two judgments and the two
triples are declared side by side, and registered with `step` back to back, the
way `Aeneas.Std.WP` lays out `spec` and `dspec`.  `dtriple` quantifies over
frames exactly as `triple` does and says what the total triple says of a run
that *stops*, while still requiring every event the program reaches to be
defined: divergence is permitted, being stuck is not.

`Aeneas.Std.WP.dspec` specializes the same generic `PartialSpec` to a handler
that rejects every event. SLPoC instead accepts defined heap events, including
infinite `vis` trees that no inductive judgment accepts. `PartialSpec` is the
*greatest* fixed point of its one-layer
condition, spelled out as the union of the post-fixed points, dually to the way
`Exec` is the least fixed point of `ExecF`.  `PartialSpec.coinduction` is its
introduction rule and `PartialSpec.ret`, `.div` and `.vis` recover the
constructors an inductive definition would have offered, so a straight-line
proof reads like a total one, and `step` drives a partial goal
through the lifting `triple_dtriple` — every `@[step]` specification states
total correctness and is applied to a partial goal as it stands, exactly as
`Aeneas.Std.WP.spec_dspec` is used for `Result`.

What a partial triple owes is proved against the same machine as the total one:
`PartialSpec.runs` carries it along every run, so a terminating run
establishes the postcondition (`dtriple_evaluates`) and every event reached is
defined on the heap it is reached with (`dtriple_pre_of_reaches`).

Because the heap handler is conjunctive, partial correctness is also
*admissible* (`dspec_admissible`, `dtriple_admissible`), which is what
`fixpoint_induct` asks of a property proved of a `partial_fixpoint`. That proof
rests on the facts about suprema of chains
of trees — a supremum has the shape of the elements it is taken over, and its
children are the suprema of theirs — which are ordinary interaction-tree order
theory and live with the rest of it in
[`ITree.lean`](../Data/Coinductive/ITree.lean), where
`Aeneas.Std.WP.dspec_admissible` finds the ones it needs too.  On top of that,
`dtriple_iter` is the loop rule an invariant alone discharges:

```lean
theorem incrForever.spec (p : Ptr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ incrForever p ⦃⇓ emp⦄div
```

for a loop that increments `p` and never leaves — a triple no total judgment
can state, since `TotalSpec.div_false` says divergence satisfies none.  See
[`Tests/Partial.lean`](Tests/Partial.lean).

## How ideal are the proofs?

The point of the automation is that a triple should be proved by unfolding the
program and calling `step*`, `step`, or `step*`, with only pure reasoning and
`sl_pull` in between, and one such block per branch of the program.
`step with some.spec` is not ideal whenever the named declaration states a
triple, regardless of whether it is registered with `@[step]`; local induction
hypotheses remain ideal.  Run

```
lake env lean --run Aeneas/SLPoC/Tests/Examples/scripts/ProofScore.lean
```

from `backends/lean` to measure how far the proofs are from that, in
[`proof-score.html`](Tests/Examples/reports/proof-score.html): every proof of a triple is split into
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
score files other than those of [`Tests/Examples/`](Tests/Examples), and `-o` to write the
report elsewhere.

## Simplifying proofs

Run the compilation-guided simplifier from `backends/lean`:

```
python3 Aeneas/SLPoC/Tests/Examples/scripts/proof_simplify.py FILE.lean
python3 Aeneas/SLPoC/Tests/Examples/scripts/proof_simplify.py --in-place FILE.lean
```

The default mode prints a unified diff.  `--in-place` applies it, and `--check`
exits with status 1 when a file can be simplified.  The tool first merges
adjacent `step`/`step*` pairs, then tries to drop explicit `sl_pull` patterns
and replace individually unused simple names with `_`.
Compressing consecutive plain `step` calls is the final stage: it validates
`step* N`, then immediately tries to remove each newly created bound.
It then replaces each plain `iframe` whose most recent automation tactic on
its proof path is `step*` with another `step*`, and recompresses any pair this
creates.  An intervening `step` makes the `iframe` acceptable.
Bounds already present in the input are not retried.  Each proposed rewrite
is retained only when `lake env lean --stdin` accepts the complete resulting
file.

To keep compiler use bounded, step-run and binder rewrite classes are validated
as batches; `sl_pull` names are first checked for lexical use in their tactic
scope.  Mixed successful and unsuccessful step pairs are bisected separately.  No Lean invocation is made when lexical analysis finds
nothing to rewrite.

Rejected candidates are reported on standard error with their source line,
proposed replacement, batch size, and the first error returned by Lean.  This
distinguishes a fully simplified file from one where potential rewrites were
tried but did not compile.

## Lines of code against the original artifacts

Almost every file of [`Tests/Examples`](Tests/Examples) ports an artifact from
another project.  [`reports/sources-manifest.json`](Tests/Examples/reports/sources-manifest.json)
records which one, pinned to a commit and to the SHA-256 of the file at that
commit, and [`SourceLoc.lean`](Tests/Examples/scripts/SourceLoc.lean) downloads
them and counts both sides:

```
lake env lean --run Aeneas/SLPoC/Tests/Examples/scripts/SourceLoc.lean
```

It writes the counts twice: [`reports/source-loc.json`](Tests/Examples/reports/source-loc.json)
holds them per file *and per declaration*, and `reports/source-loc.html` draws
them as a standalone page — every example one row of three stacked bars, on a
scale common to the whole table, sortable by size or by share of specification
and proof, filterable by safe-Rust verdict, and expandable to the files, the
declarations, and the twenty declarations that cost the most proof.  Nothing on
that page is fetched from anywhere.  It is regenerated on demand and is not
committed, so open it from a local run.  Downloads are cached under
`.lake/source-loc-cache`, so a first run takes about half a minute and later
ones about eight seconds.  Pass `--offline` to count only what is already
cached, `-o FILE` or `--html FILE` to write elsewhere.

A line counts when what is left of it after comment removal is at least four
characters wide and is neither delimiters alone nor import, module or scope
boilerplate.  Each counted line is charged to `code` (what runs), `spec` (what
the program is claimed to do, and the annotations a verifier needs: pre- and
postconditions, invariants, representation predicates, theorem statements,
ghost state, attributes) or `proof` (tactic scripts, `proof { … }` blocks,
`assert`s and ghost steps, `Proof. … Qed.`, Pulse's `fold`/`unfold`/`rewrite`).
The classification is a documented heuristic — see the module doc comment of the
script for the rule used in each language — and is deliberately generous to
`code`, so it understates rather than overstates verification overhead.

Two entries of the manifest are recorded but not counted: Dardinier's Viper
artifact, which is a Zenodo archive rather than a file, and SymCRust's
`common.rs`, which is not publicly readable.

### Can it be written in safe Rust?

Aeneas translates *safe* Rust, so for each example the manifest also records
whether its program could be written in that fragment at all — a property of
the aliasing the example is about, not of its proof, since `spec` and `proof`
material never runs:

* **yes** (10 examples) — expressible in safe Rust, at worst by replacing a raw
  pointer with an index, a `Box`, or a `&mut`;
* **no** (5) — the aliasing *is* the point: intrusive links, a doubly-linked
  list, a free list threaded through freed memory, hardware page tables;
* **n/a** (4) — no single answer applies: the file holds no program at all, or
  part of it is safe and the rest needs `unsafe`, a borrow checker that does not
  exist yet (the leftmost-leaf `&mut` traversal is NLL problem case #3), or has
  no sequential Rust counterpart.

Each entry also lists `references`: unverified Rust implementations of roughly
the same data structure — `std::collections::LinkedList`, `VecDeque`, `Vec`,
`fixedbitset`, `intrusive-collections`, RustCrypto's `InOutBuf`, a buddy
allocator's free list, an x86-64 page-table walker — so that a port can be read
against real Rust and not only against a verifier's encoding.  Their `safe`
field says whether the implementation itself is safe Rust; `false` on a `std`
collection means a safe *API* over `unsafe` internals, which is precisely the
gap a verified port has to close.  Being unverified, a reference costs `code`
lines and no `spec` or `proof` line at all — the 5710 lines below are all
computational.

### Is the comparison a ratio, or only two figures?

A port may be divided by the artifact it answers only when it answers the whole
of it.  Nine of them deliberately do not: they take the kernel out of a library
(`vstd`'s sequences, mimalloc's free list, a leaf-only subset of the page
table), and one is a downscaled benchmark.  Each entry records which it is, and
why, so the sums that follow are taken over the 6 comparable examples alone —
adding the rest in would compare a kernel against a library and flatter whichever
side happens to be a fragment.

Over those 6, the port costs **×1.29** the artifact it answers: **×0.86** on
what runs, and **×1.49** on specification and proof.  It spends 78.4% of its
lines on verification, the artifact 67.7%.

Relevant lines, as `total (code, spec + proof)`:

| Example | Safe Rust | Original artifact | Aeneas+SL | Port ÷ artifact | Rust reference |
|---|---|---:|---:|---:|---:|
| [`AsterinasIntrusiveFrameList.lean`](Tests/Examples/AsterinasIntrusiveFrameList.lean) | no | 186 (186, 0) | 314 (93, 221) | fragment | 1123 (1123, 0) |
| [`Basic.lean`](Tests/Examples/Basic.lean) | yes | — | 52 (13, 39) | — | — |
| [`CreusotListReversalLasso.lean`](Tests/Examples/CreusotListReversalLasso.lean) | yes | 181 (53, 128) | 380 (53, 327) | fragment | — |
| [`DardinierMagicWands.lean`](Tests/Examples/DardinierMagicWands.lean) | n/a | — | 180 (25, 155) | — | — |
| [`EqOrDisj.lean`](Tests/Examples/EqOrDisj.lean) | no | — | 262 (55, 207) | — | 143 (143, 0) |
| [`HigherOrder.lean`](Tests/Examples/HigherOrder.lean) | yes | — | 97 (15, 82) | — | — |
| [`IrisTutorial.lean`](Tests/Examples/IrisTutorial.lean) | n/a | 459 (87, 372) | 444 (100, 344) | ×0.97 | 98 (98, 0) |
| [`PulseArrayTests.lean`](Tests/Examples/PulseArrayTests.lean) | yes | 329 (179, 150) | 333 (59, 274) | fragment | — |
| [`PulseInsertionSort.lean`](Tests/Examples/PulseInsertionSort.lean) | yes | 182 (75, 107) | 188 (29, 159) | ×1.03 | 38 (38, 0) |
| [`PulseLinkedList.lean`](Tests/Examples/PulseLinkedList.lean) | yes | 601 (263, 338) | 313 (83, 230) | fragment | 98 (98, 0) |
| [`PulseResizableVec.lean`](Tests/Examples/PulseResizableVec.lean) | yes | 180 (69, 111) | 244 (53, 191) | ×1.36 | 663 (663, 0) |
| [`PulseRingBuffer.lean`](Tests/Examples/PulseRingBuffer.lean) | yes | 310 (125, 185) | 366 (67, 299) | ×1.18 | 1051 (1051, 0) |
| [`VerusBitmap.lean`](Tests/Examples/VerusBitmap.lean) | yes | 105 (46, 59) | 457 (75, 382) | ×4.35 | 697 (697, 0) |
| [`VerusDoublyLinkedList.lean`](Tests/Examples/VerusDoublyLinkedList.lean) | no | 338 (106, 232) | 329 (114, 215) | ×0.97 | 558 (558, 0) |
| [`VerusMimallocLinkedList.lean`](Tests/Examples/VerusMimallocLinkedList.lean) | no | 1378 (248, 1130) | 118 (30, 88) | fragment | 68 (68, 0) |
| [`VerusPageTable.lean`](Tests/Examples/VerusPageTable.lean) | no | 1512 (111, 1401) | 1267 (184, 1083) | fragment | 510 (510, 0) |
| [`VerusStd.lean`](Tests/Examples/VerusStd.lean) | n/a | 1407 (280, 1127) | 98 (3, 95) | fragment | — |
| [`VerusVerifiedVec.lean`](Tests/Examples/VerusVerifiedVec.lean) | yes | 118 (29, 89) | 248 (28, 220) | fragment | 663 (663, 0) |
| [`YOLOCancel.lean`](Tests/Examples/YOLOCancel.lean) | n/a | 37 (12, 25) | 28 (0, 28) | fragment | — |
| **Total over the 6 comparable** | | **1574 (508, 1066)** | **2028 (438, 1590)** | **×1.29** | |

The artifact column is the *whole* upstream file, which for a library such as
`vstd`, mimalloc's `linked_list.rs` or Pulse's `LinkedList.fst` is much larger
than the fragment a port covers — which is exactly why those rows carry no
ratio; the manifest's `coverage` field records what was left out.  Conversely, Verus obtains its sequence and permission-map reasoning
from `vstd` for free, so the Lean side keeps that layer separate in
[`VerusStd.lean`](Tests/Examples/VerusStd.lean): the figure comparable with a
Verus example excludes it.  The reference column carries the same caveat twice
over: it is a whole `std` module or crate file, and it implements a data
structure that only resembles the one that was ported.  What it is good for is
the shape of the numbers — an unverified implementation is all `code`, and the
two other columns show what proving it costs.
