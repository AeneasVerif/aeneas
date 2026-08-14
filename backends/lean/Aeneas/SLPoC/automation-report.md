# More automation for the separation-logic proof mode

This report maps ideas from Thibault Dardinier's 2025 thesis,
[*Formal Foundations for Automated Deductive Verifiers*][thesis], to the
proof mode in `Aeneas/SLPoC`. It focuses on changes that fit the current
proof-producing Lean architecture, rather than proposing a translation to
Viper or an SMT-based verifier.

“Automated Verifiers Based on Separation Logic” is Part I of the thesis, not a
single chapter. It comprises Chapter 2 (translational verifiers), Chapter 3
(fractional predicates), and Chapter 4 (magic wands). In the mapping below, the
“Thesis idea” and “Source” columns summarize direct thesis claims; the “SLPoC
interpretation” column and all proposed implementation details are
extrapolations for this codebase.

The main recommendation is to replace the current greedy atom canceller with a
small proof-producing symbolic resource engine:

1. represent the spatial context as resource chunks plus an explicit pure/path
   context;
2. consume required resources and produce returned resources as separate
   phases;
3. search over alternative matches with bounded backtracking;
4. apply registered, directed predicate views on demand; and
5. retain a trace of choices for diagnostics and reproducibility.

This would directly address the largest current gap: recursive predicates that
must be transformed with one-way entailments before a cell can be selected or
the predicate can be folded again.

## Evidence from the current proof mode

The analysis was run on 2026-08-14 on the working tree based on revision
`9bebda3b`. Running

```text
lake env lean --run Aeneas/SLPoC/ProofScore.lean -o REPORT.html
```

found 311 of 481 proof spots ideal (64.7%). `VerusPageTable.lean` alone has 76
of the 170 non-ideal spots: only 18 of its 94 spots are ideal. Its proofs
repeatedly perform:

```lean
sl_xchange (tableOwn_select ...)
...
sl_xchange (tableOwn_unselect ...)
```

or the corresponding replacement transformation. This is representative, not
an isolated benchmark trick: it is the standard operation of focusing on one
child of a recursive ownership predicate and later rebuilding the parent.

The relevant implementation constraints are:

- `SLTactics.lean` flattens only `∗`, treats the resulting expressions as
  opaque atoms, and greedily accepts the first definitionally equal atom
  (`flatten`, `removeMatches`, and `solveHimpl`).
- It has two global attempts: cancellation before and after decomposition with
  `[sl_simps]` (`solveGoal`). This works well for equalities that uniformly
  expose predicates, but not for directed or parameterized transformations
  such as `tableOwn_select`.
- Existentials on the right become metavariables and are expected to be fixed
  by later unification. Frame inference has a special top-level existential
  pass, but there is no general delayed-witness search.
- Pure facts are extracted into Lean's local context or discharged after
  spatial cancellation. They are not maintained as a first-class path
  condition used to normalize spatial atoms before matching.
- `proveWand` introduces a wand and recursively invokes the same entailment
  solver. It does not perform explicit footprint search and permits only one
  unmatched absorbing assertion.
- Failures report source, destination, and a missing atom, but not the choices
  made, alternatives tried, or the closest search frontier.

These design choices explain the gaps already identified in
`benchmark-report.md`: recursive selection and folding, result-dependent
terminal posts, buried pure facts and existentials, local triple composition,
and witnesses without a spatial anchor.

## Thesis ideas that transfer directly

Page references below give the PDF page followed by the printed thesis page.

| Thesis idea | Source | SLPoC interpretation |
|---|---|---|
| Treat verification as manipulation of a symbolic state containing a store, path condition, and heap chunks. | §2.4.1, PDF pp. 59-60 (pp. 37-38) | Introduce an internal resource state instead of repeatedly flattening raw expressions. Lean expressions remain the symbolic terms and proof terms remain the certificate. |
| Separate resource production from resource consumption (`inhale`/`exhale`). Procedure calls consume a precondition and produce a postcondition. | §2.2.1, PDF pp. 44-46 (pp. 22-24) | Give `sl_step` explicit consume/produce phases: consume the callee precondition, retain the frame, then add the callee postcondition before solving the continuation. |
| Algorithmic choices are angelic: several sound choices may exist, and success requires finding one that makes the remainder verify. | §2.2.3, PDF pp. 47-48 (pp. 25-26) | Backtrack over matches, existential witnesses, and predicate views instead of committing to the first definitionally equal atom. Every successful branch constructs a kernel-checked proof term. |
| State consolidation is a replaceable, semantically constrained phase rather than one fixed eager algorithm. | §2.4.1, PDF p. 60 (p. 38) | Add a bounded normalization hook after producing resources. Keep recursive predicates folded by default, canonicalize only cheap facts, and allow specialized normalizers without baking them into the core matcher. |
| Prove the generic exhale/havoc/inhale call pattern once, then reuse it for many front-end constructs. | §§2.2.4 and 2.5, PDF pp. 50-51 and 67 (pp. 28-29 and 45) | Preserve the generic `triple_step_bind`/`triple_step_mono` and specification-registration architecture. Improve the shared resource discharger rather than adding per-operation tactic cases. |
| Wand packaging is footprint inference. Sound search must choose one footprint that works for every state satisfying the wand's left side. | §§4.2.2-4.3.4, PDF pp. 108-116 (pp. 86-94) | Make residual-frame/wand inference explicit. Never accept a footprint chosen independently per branch of a pure case split. |
| Package search processes the right side left-to-right: use resources supplied by the wand's left side when all cases provide them; otherwise extract a resource uniformly from the outer state. | §4.3.5, PDF p. 117 (p. 95) | Generalize `proveWand` into a proof-producing package search. The current affine logic is the favorable case in Theorem 4.3.1 because the right side may discard resources. |
| Recursive predicate instances are resources in their own right; practical automation must remember and manipulate resources inside them. | §§3.5.2 and 4.5, PDF pp. 98-99 and 124-125 (pp. 76-77 and 102-103) | Register sound fold/unfold/select/replace entailments as directed views, and open them only when matching demands it. |
| Retain explicit path conditions while traversing conditional assertions. | §§4.3.3-4.3.5, PDF pp. 113-117 (pp. 91-95) | Use known equalities and branch hypotheses before spatial matching, especially for result-dependent posts and indexed recursive predicates. |

The thesis's broader architectural lesson is also useful: separate a small,
sound semantic core from replaceable proof-search heuristics. In SLPoC the Lean
kernel and the existing entailment lemmas already provide the trusted core; the
new matcher should only choose and compose those lemmas.

## Proposed design

### 1. A proof-producing symbolic resource state

Keep the external assertion language unchanged, but normalize a goal into an
internal state along these lines:

```lean
structure SpatialChunk where
  expr : Expr
  origin : ChunkOrigin

structure SearchState where
  available : Array SpatialChunk
  required : Array Expr
  pureFacts : Array Expr
  witnesses : Array MVarId
  proof : Expr
  trace : Array SearchEvent
```

`origin` should distinguish an original atom, a produced postcondition, and an
atom exposed by a named view. This is useful both for cycle prevention and for
diagnostics.

The proof field (or an equivalent continuation) must witness each state
transition with existing theorems such as `himpl_trans`, `hstar_mono`,
`himpl_of_eq`, and the registered view theorem. Search remains untrusted
metaprogramming; Lean checks the final term.

### 2. Bounded matching plans instead of greedy cancellation

For each required spatial atom, try candidates in a deterministic cost order:

1. exact definitional equality;
2. unification against a rigid resource head such as `p ↦ v`;
3. normalization using known pure equalities;
4. one registered directed view on an available atom;
5. one registered fold view on the required atom; and
6. a user-supplied plan or witness.

Use `saveState`/restore for alternatives, but bound search by view cost, depth,
and explored states. Memoize a key derived from the normalized available and
required heads plus assigned witnesses. This prevents fold/unfold cycles.

The current two-pass policy should remain as the cheap prefix: exact opaque
matching first, then search. Most existing ideal proofs should therefore keep
their current performance.

### 3. Directed predicate views

`[sl_simps]` should remain for unconditional equalities. Add a separate
registry for theorems of the forms:

```text
A ⊢ B
A = B
```

with an explicit direction and cost. Suggested categories are:

- `open`: expose one useful resource;
- `close`: rebuild an abstract predicate;
- `select`: expose a resource chosen by an index/key while framing siblings;
- `replace`: rebuild after the selected resource changed.

Unlike `simp`, the engine must never reverse an entailment unless a theorem for
the reverse direction is separately registered.

The first end-to-end experiment should register:

- `tableOwn_select`;
- `tableOwn_unselect`;
- `tableOwn_replace` and its specialized variants; and
- the analogous list/array fold and unfold lemmas.

The goal is not to infer arbitrary inductive definitions. It is to automate
application of developer-proved views while preserving abstraction and
termination.

### 4. Explicit consume/produce in `sl_step`

Model a specification application as:

```text
normalize
→ consume callee precondition
→ retain residual frame
→ produce callee postcondition
→ add its pure facts to the path context
→ normalize with those facts
→ solve the continuation
```

This ordering should fix a recurring terminal-post problem: a returned value is
known equal to a pointer or tuple component, but the equality is not used until
after spatial matching has already failed.

Initially this can be implemented inside the tactic while retaining
`triple_step_bind` and `triple_step_mono`. A later refactor may expose the
resource transition as a reusable API for `sl_frame`, `sl_step`, and
`sl_xchange`.

### 5. Pure constraints and witness synthesis

Maintain copied pure facts as a search context even when they must remain in
the spatial precondition for framing. Before matching:

- rewrite projections and indices with local equalities;
- run only the configured `sl_simps`/pure discharger on propositions;
- defer right-existential witnesses until spatial anchors and pure equalities
  have been processed; and
- report unresolved witnesses separately from missing resources.

For witnesses with no spatial anchor, automation should remain conservative.
Try local variables and constructor-normal forms under a small, typed candidate
budget, then require an explicit hint. Dardinier's proposed universal
introduction feature (§7.2.1, PDF p. 201) is a useful longer-term model for
universally quantified posts, but it does not justify guessing arbitrary
existential witnesses.

### 6. Sound wand footprint search

This is a later phase, after the resource engine is stable. Introduce explicit
`package` and `apply` operations internally, even if the initial public use is
only the ramified frame rule.

For `A -∗ B`, traverse the normalized atoms of `B`. An atom may be supplied
from `A` only when the symbolic cases for `A` all supply it; otherwise extract
it once from the outer residual state and add it uniformly to every case. This
is the core safety condition from the package logic.

Add a regression test based on the thesis's unsound FIA example (§4.2.3, PDF
p. 110): two cases of the left side require different resources, so selecting a
different footprint per case must be rejected. The current logic is affine and
exclusive, so fractional and combinable wands are not needed for this phase.

### 7. Search diagnostics and controlled escape hatches

On failure, retain the best frontier and print:

- the required atom;
- normalized available chunks;
- assigned and unresolved witnesses;
- pure facts used;
- views attempted, with the reason each failed; and
- the smallest explicit hint that would resume search.

Provide a matching-plan syntax only as an escape hatch, for example to select a
view, witness, or resource occurrence. Plans should guide the same
proof-producing engine, not bypass it with a separate tactic path.

## Prioritized implementation plan

### Phase 1: Resource IR and bounded alternative matching

- Refactor `SLFrame.solveHimpl` without changing external tactics.
- Preserve the current exact and `[sl_simps]` fast paths.
- Add backtracking, path-aware normalization, a trace, and focused unit tests.
- Target current greedy failures and result-dependent terminal posts.

This is the smallest change that imports the thesis's symbolic-state and
angelic-choice ideas without changing the logic.

### Phase 2: Directed predicate views

- Add the view registry and cycle-bounded view search.
- Register the page-table select/unselect/replace lemmas.
- Remove the corresponding `sl_xchange` calls only after the automated proofs
  compile unchanged.

This is the highest-impact phase. If all 76 non-ideal page-table spots became
ideal, the global score would rise from 64.7% to 80.5%; that is an upper bound,
but it shows where the leverage is.

### Phase 3: Shared consume/produce engine

- Reuse the resource state in `sl_step`, terminal-post matching, and local
  triple composition.
- Normalize produced posts with their result equalities before matching.
- Add explicit witness queues and conservative hint support.

### Phase 4: Package-logic-inspired wand automation

- Generalize `proveWand` to explicit, uniform footprint search.
- Add negative soundness tests before expanding supported assertion forms.
- Consider public `sl_package`/`sl_apply` tactics only when examples need them.

### Phase 5: Semantic extensions only if required

Fractional predicates, unbounded permissions, and combinable wands from
Chapters 3 and 4 require a different heap/resource model. They should not be
mixed into the automation refactor. The present exclusive affine logic can
adopt the proof-search architecture without adopting those semantics.

## Validation criteria

Each phase should satisfy all of the following:

- no change to theorem statements or program definitions in the benchmark
  corpus;
- generated proof terms contain no new axioms, `sorry`, or unsafe escape;
- deterministic search under a fixed option set;
- bounded failure on fold/unfold cycles;
- diagnostics identify the best failed plan;
- no regression in the 311 currently ideal spots; and
- a tracked proof-score and runtime comparison.

For Phase 2, a useful go/no-go experiment is to convert one complete recursive
page-table proof to registered views. Proceed with the generic mechanism only
if it removes its select/unselect/replace `sl_xchange` calls without
benchmark-specific matcher code and without more than a small constant-factor
slowdown on the full proof-score corpus.

## Ideas not to import directly

- **A full translational IVL.** CoreIVL is valuable for proving back-end and
  front-end soundness, but SLPoC already has a shallow Lean semantics and
  kernel-checked triples. The useful import is the separation between semantic
  rules and search heuristics, not another language layer.
- **An SMT-style VCG back-end.** The current problems are resource matching and
  predicate navigation, not generation of first-order verification conditions.
- **Eager recursive unfolding.** It loses abstraction, creates loops, and is
  exactly the wrong response to indexed selection. Use demand-driven,
  theorem-backed views.
- **Branch-local wand footprints.** The thesis demonstrates that this can be
  unsound. Any case split during packaging must preserve one outer footprint
  that works uniformly.
- **Fractional predicate automation without new semantics.** The thesis's
  folding, multiplication, and combinability results depend on its unbounded
  resource model. They are not rules for the current exclusive heap.

## Conclusion

The most useful idea from the thesis is not a particular tactic but a proof
search architecture: manipulate an explicit symbolic resource state, separate
consume from produce, represent path conditions, and treat matching choices as
bounded alternatives justified by a small sound core.

For SLPoC, the concrete first target is a registered directed-view engine on
top of a backtracking chunk matcher. It addresses the dominant page-table
failure mode, generalizes to lists, arrays, and cursor representations, and
preserves the strongest property of the current implementation: all automation
ultimately produces ordinary Lean proof terms.

[thesis]: https://dardinier.me/papers/PhD_thesis.pdf
