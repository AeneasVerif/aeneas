---
name: aeneas-tactics-quickref
description: Tactic decision tree, banned tactics, and common combinations for Aeneas Lean proofs
---

# Aeneas Tactics Quick Reference

## Decision Tree: Which Tactic?

**PREREQUISITE:** Always use the lean-lsp-mcp tools for interactive proof development. Use `lean_goal` to inspect the proof state before choosing a tactic. See the `lean-lsp-mcp` skill file.

> **🔑 DEFAULT TACTIC: When you don't know what to do, use `agrind`.**
> `agrind` is always the first tactic to try — it is fast, handles arithmetic,
> equalities, and most structural goals. If `agrind` fails, try `grind` (slower
> but more powerful). **Do NOT reach for `simp_all`** — it is very slow in large
> contexts (common in Aeneas proofs) and silently drops hypotheses you may need later.

```
What does the goal look like?

├─ Monadic function call (let x ← f args; ...)
│  → step / step* / step with <thm>
│
├─ Loop fixed-point (loop body x)
│  → apply loop.spec_decr_nat (Nat measure) or loop.spec (general)
│
├─ Recursive _loop function
│  → unfold + split + step (invariant = pre + post), termination_by + scalar_decr_tac
│
├─ Arithmetic
│  ├─ General → agrind (preferred), then grind, then scalar_tac (NEVER omega/linarith/nlinarith)
│  ├─ Nonlinear → agrind, then grind, then simp_scalar, then scalar_tac +nonLin
│  └─ Scalar simplification (min, max, %) → simp_scalar
│
├─ Bit-vector / Bitwise
│  ├─ **Always use `bv_tac N` for bitwise ops** (&&&, |||, ^^^, ~~~, >>>, <<<, %)
│  ├─ Pure BitVec goal → bv_tac N
│  ├─ Nat goal about bitwise result → bvify N; bv_tac N
│  ├─ bvify fails → have h : bv_prop := by bv_tac N; natify at h; simp_scalar
│  └─ bv_tac error shows non-decomposed expr (e.g. `(x &&& y).bv`) → missing @[bvify_simps] lemma
│
├─ Modular arithmetic
│  ├─ Equivalence (a ≡ b [MOD n]) → zmodify; ring / simp
│  └─ Bounds (a < n) → stay Nat/Int; agrind / grind / scalar_tac
│
├─ List/Array/Slice structural (setSlice!, replicate, append, take, drop, length)
│  → simp_lists  (designed for these operations)
│
├─ List/Array (get/set by index)
│  ├─ Automatic → agrind first; if fails, try grind (slower, more list lemmas)
│  └─ Slow → cases idx <;> simp_lists
│
├─ Slice/List getElem mismatch
│  ├─ Use #setup_aeneas_simps at file top (auto-converts getElem → getElem!)
│  ├─ Manual bridge → List.Inhabited_getElem_eq_getElem! s.val i proof
│  └─ Slice getElem! → List getElem! → rw [Slice.getElem!_Nat_eq]
│
├─ Equality with shared terms (3*x + 2*y = x + 3*y)
│  → ring_eq_nf / ring_eq_nf at h
│
├─ If-then-else → simp_ifs / split
├─ Conjunction (∧) → split_conjs, then immediately scaffold `· agrind` per sub-goal (same as step*)
├─ Boolean/Propositional → simp_bool_prop / tauto
├─ Concrete computation → decide / native_decide
├─ Congruence → fcongr
│
├─ Writing `simp [CONST]; solver` in a cdot block after step*?
│  → STOP. Register CONST with @[grind =, agrind =] first.
│    Re-run step* — the goal may disappear entirely.
│    (See "Register Rust global/const scalar definitions" in Proof Style Rules)
│
└─ General / stuck
   ├─ Try → agrind
   └─ If fails → simp [*]; agrind
```

## Tactic Reference Table

### Aeneas-Specific Tactics

| Tactic | Purpose | Syntax | Key Attributes |
|---|---|---|---|
| `step` | Apply function spec | `step`, `step as ⟨x,h⟩`, `step with thm` | `@[step]` |
| `step*` | Repeat step + case split | `step*`, `step* n` (n steps) | **Immediately** scaffold `· agrind` per sub-goal after |
| `step*?` | Generate proof script | `step*?` | Start here when developing proofs; scaffold `· agrind` after pasting |
| `scalar_tac` | Integer arithmetic/bounds | `scalar_tac`, `scalar_tac +nonLin` | `@[scalar_tac_simps]` |
| `simp_scalar` | Simplify scalar exprs | `simp_scalar`, `simp_scalar [lemmas]` | `@[simp_scalar_simps]` |
| `simp_lists` | Simplify list get/set | `simp_lists`, `simp_lists [lemmas]` | `@[simp_lists_simps]` |
| `bvify` | Lift to BitVec | `bvify N`, `bvify N at h` | `@[bvify_simps]` |
| `bv_tac` | Decide BitVec goals | `bv_tac N` | — |
| `natify` | Convert to Nat | `natify`, `natify at h` | `@[natify_simps]` |
| `zmodify` | Convert to ZMod | `zmodify`, `zmodify [to N]`, `zmodify at h` | `@[zmodify_simps]` |
| `simp_ifs` | Simplify if-then-else | `simp_ifs` | — |
| `simp_bool_prop` | Bool/prop simplification | `simp_bool_prop` | `@[simp_bool_prop_simps]` |
| `ring_eq_nf` | Cancel common terms in equalities | `ring_eq_nf`, `ring_eq_nf at h` | — |
| `fcongr` | Congruence (safe whnf) | `fcongr`, `fcongr N` | — |
| `split_conjs` | Split nested ∧, then scaffold `· agrind` per sub-goal | `split_conjs`, `split_conjs at h` | — |

### Commonly Used Lean Builtins

| Tactic | Purpose | Notes |
|---|---|---|
| `agrind` | **Default tactic — always try first** | Fast, handles most goals. If it fails, try `grind` |
| `grind` | General automation (fallback) | Slower but more powerful than `agrind`. Try when `agrind` fails |
| `simp` / `simp [*]` | Simplification | Use `simp [*]` to keep hypotheses |
| `simp_all` | Aggressive simplification | **⚠️ AVOID in big contexts** — very slow and drops hypotheses. Prefer `agrind` |
| `tauto` | Propositional tautologies | |
| `decide` | Concrete decidable goals | |
| `ring` | Ring equalities | |
| `split` | Case-split match/if | |
| `cases` | Structural case analysis | |

### ⛔ BANNED TACTICS

<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "⛔ BANNED TACTICS" -->

| Banned | Why | Use instead (preference order) |
|---|---|---|
| `omega` | No scalar/Slice/Vec knowledge | `agrind` > `grind` > `scalar_tac` |
| `linarith` | No scalar/Slice/Vec knowledge | `agrind` > `grind` > `scalar_tac` |
| `nlinarith` | No scalar knowledge, explosion risk | `agrind` > `grind` > `scalar_tac +nonLin` / `simp_scalar` |
| `step* <;> ...` | Replays full `step*` on every edit | `step*` then `· tactic` per goal |
| `all_goals tactic` | Same re-elaboration problem | `· tactic` per goal |

**The first three tactics are NEVER acceptable in Aeneas proofs** — not in `step`
theorems, not in helper lemmas, not in `have` steps, not in `decreasing_by` (even
for pure Nat). They cannot reason about U8, U32, Usize, Slice.length, etc. A proof
using them is non-idiomatic and must be rewritten. There are **no exceptions**.
See `aeneas-lean-core` skill file for the full rationale.

**`step* <;>` and `all_goals` are NEVER acceptable either** — they destroy
incrementality by forcing full re-elaboration on every edit. `all_goals` is banned
**everywhere**, not just after `step*`: even a standalone `all_goals scalar_tac` at
the end of a proof forces all goals to be a single elaboration unit. Always use
focused `· tactic` (cdot) blocks — one per goal. There are **no exceptions**.

### ⛔ BANNED PATTERN: `step* <;> tactic` and `all_goals tactic`

**NEVER use `step* <;> ...`, `all_goals ...`, or `step* <;> all_goals ...`.**

`all_goals` is banned in ALL contexts — not just after `step*`. Even a standalone
`all_goals scalar_tac` at the end of a tactic block makes all remaining goals a
single elaboration unit: editing anything forces re-elaboration of everything.

When you modify any tactic after `<;>`, Lean replays the entire `step*` first —
this can take 30+ seconds per edit, destroying interactive feedback.

Instead, close each remaining goal individually using focused `· ...` (cdot) blocks:

```lean
-- ⛔ BAD: editing any tactic after <;> replays the full step*
step* <;> scalar_tac

-- ⛔ ALSO BAD: same problem even with all_goals
step* <;> all_goals agrind

-- ⛔ ALSO BAD: standalone all_goals — all goals become one elaboration unit
step*
all_goals scalar_tac

-- ✅ GOOD: each goal is independently checkpointed
step*
· scalar_tac          -- goal 1: independently elaborated
· agrind              -- goal 2: independently elaborated
· simp [*]; scalar_tac -- goal 3: independently elaborated
```

**Why this matters:** `step*` unfolds the function body and steps through every
monadic call — it can produce 5–20 remaining side-condition goals. With `<;>`, Lean
treats `step* <;> tactic` as a single elaboration unit. Changing `tactic` forces
`step*` to replay from scratch. With `·` blocks, each goal is a separate checkpoint —
editing goal 3 does not re-elaborate goals 1 or 2.

**The same applies to any expensive tactic before `<;>`:** `simp [*] <;> scalar_tac`,
`progress* <;> agrind`, etc. If the left-hand side is slow, always use `·` blocks.

**After `step*`, always use focused `·` blocks** to close each remaining goal
individually. This is mandatory regardless of the number of goals — even 2 goals
must use `·` blocks, not `all_goals` or `<;>`.

### Scaffolding workflow: `· agrind` first, then fix failures

> **🔑 MANDATORY: After every `step*`, immediately scaffold one `· agrind` per
> remaining sub-goal.** This is the very first thing you do — before inspecting
> goals, before trying tactics, before anything else. Never leave `step*` without
> its cdot scaffolding. **The same rule applies to `split_conjs`** and any other
> tactic that produces multiple sub-goals (e.g., `split`, `cases`).

```lean
-- After step*:
step*
· agrind -- goal 1
· agrind -- goal 2
· agrind -- goal 3
· agrind -- goal 4

-- After split_conjs:
split_conjs
· agrind -- conjunct 1
· agrind -- conjunct 2
· agrind -- conjunct 3
```

This has critical benefits:
- **`agrind` closes most sub-goals immediately** — many goals produced by `step*`
  and `split_conjs` are arithmetic bounds or simple equalities that `agrind` handles.
- **Each goal becomes independently inspectable** — for goals where `agrind` fails,
  use `lean_goal` on that line to see exactly the context and target.
- **Edits are incremental** — replacing one `· agrind` with a different tactic only
  re-elaborates that single goal, not the others.
- **No risk of `all_goals` temptation** — the structure is already in place.

After scaffolding, check which `· agrind` goals still have errors. For those,
inspect with `lean_goal`, pick the right tactic, and replace. This is
the correct workflow even for 20+ goals — never try to close them in bulk.

**⚠️ After `step*`, BEFORE writing any cdot blocks: check for missing solver
attributes.** Scan the remaining goals. If 3+ goals need the same constant
unfolded (e.g., you would write `simp [CONST]; solver` in each cdot block),
**STOP** — register the constant with `@[grind =, agrind =]`
FIRST, then re-run `step*`. The goals may disappear entirely. Only write
manual cdot blocks for goals that survive after registration. This one step
eliminates the most common source of verbose, fragile cdot blocks.

If `step*` produces **more than 15 remaining goals**, this is a signal that the
function body likely needs fold decomposition — see "Function Decomposition" in
the `aeneas-crypto-verification` skill file. The solution to many goals is fewer
goals through decomposition, not a clever tactic.

If you are tempted to use `all_goals` because there are many goals, the answer
is fold decomposition (see `aeneas-crypto-verification`), not a bulk tactic.

## Common Tactic Combinations

| Pattern | Use When |
|---|---|
| `split_conjs` then `· agrind` per goal | Goal is a conjunction — scaffold then fix failures (same as `step*`) |
| `simp [*]; agrind` | `agrind` alone fails (grind issue workaround) |
| `bvify N; bv_tac N` | Nat goal about bitwise operation |
| `have h := ...; natify at h; simp_scalar at h` | Reverse bv lifting (goal → bv → back to Nat) |
| `zify at h; zify; simp [h, Int.mul_emod]` | Modular equivalence via Int |
| `unfold fn; split; step` | Recursive function (avoid termination issue) |
| chain of `have` + `simp_scalar` | Non-linear arithmetic (modulo, division) |
| `calc _ = _ := by simp_scalar` | Equational chains for arithmetic |

## Proof Style Rules

<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Proof Style and Maintainability" -->

- **Address ALL warnings** — the only acceptable warning is `"declaration uses 'sorry'"`:
  - `"This simp argument is unused"` → remove the unused lemma from `simp only [...]`
  - `"Too many ids provided"` → reduce binders in `step as ⟨...⟩`
  - `"'...' tactic does nothing"` / `"is never executed"` → remove the dead tactic
  - `"unused variable"` → remove or prefix with `_`
  - `"Used tac1 <;> tac2 where (tac1; tac2) would suffice"` → replace `<;>` with `;`
  - **This applies to sorry'd proofs too.** Warnings in incomplete proofs must still be
    fixed — the sorry is acceptable, but dead tactics, unused simp args, and other
    warnings are not. Keep sorry'd proofs clean so they're ready for completion.
- **No big `simp only [...]` in implementation proofs** — model names are unstable. Use `simp [*]` or targeted rewrites. (OK in spec lemmas.)
- **Register Rust global/const scalar definitions with solver attributes** — pure Rust global/const definitions should be marked `@[simp, scalar_tac_simps, agrind =, grind =, bvify]`. This lets `step` / `step*` discharge precondition sub-goals automatically (they disappear). If you see repeated `simp [CONST]; solver` in cdot sub-goals after `step`, or `have hFoo : CONST.val = N := by simp ...`, the definition is missing attributes.
- **Extract complex sub-proofs** as auxiliary lemmas — don't inline 15 lines of arithmetic inside `step*`
- **Simplify shifts early**: rewrite `>>>` as `/ 2^n`, `<<<` as `* 2^n`
- **Sorry'd proofs must be fast**: do not leave expensive `step*`, `cases p`, or `first | ...` before a sorry. Use plain `sorry` (with a comment sketching the approach). Expensive sorry'd proofs waste build time on every `lake build` for zero verification value.

## Attribute Management Cheatsheet

```lean
-- Setup for crypto/array proofs
#setup_aeneas_simps

-- Swap to simpler cast spec
attribute [-step] UScalar.cast.step_spec
attribute [local step] UScalar.cast_inBounds_spec

-- Register lemma for specific tactic
attribute [local simp_scalar_simps] my_lemma
attribute [local simp_lists_simps] my_lemma
attribute [local agrind] my_lemma

-- Register constant for all tactics
@[simp, scalar_tac_simps, bvify_simps, agrind =]
theorem MY_CONST_val : MY_CONST.val = 42 := by decide
```

**Safety:** simp_scalar/simp_lists are simp-based. Activating many local lemmas is safe (no complexity explosion).

## Key Lemmas Reference

| Lemma | Statement | Use Case |
|---|---|---|
| `WP.spec_ok` | `spec (ok x) p ↔ p x` | Proving `@[step]` for constants that reduce to `ok v` |
| `bind_assoc_eq` | `(x >>= f) >>= g = x >>= (λ a => f a >>= g)` | Fold theorem proofs (reassociate binds) |
| `bind_tc_ok` | `(do let y ← .ok x; f y) = f x` | Fold theorem proofs (eliminate trivial ok binds) |
| `Slice.Inhabited_getElem_eq_getElem!` | `s[i] = s[i]!` for Slice | Bridge proof-based → default-based access |
| `Slice.getElem!_Nat_eq` | `s[i]! = s.val[i]!` | Bridge Slice getElem! → List getElem! |
| `List.Inhabited_getElem_eq_getElem!` | `l[i] = l[i]!` for List | Bridge proof-based → default-based access |

## Critical Pitfalls

| Pitfall | Symptom | Fix |
|---|---|---|
| Recursive step | Termination error after unfold+step | `split` before `step` |
| Nat subtraction | Spec is wrong (truncated at 0) | Use Int, add `h : a ≥ b`, or rewrite as addition |
| `simp_all` drops hyps / slow | Hypothesis gone or timeout | **Prefer `agrind`**. If you need simp, use `simp [*]` or `simp [h1,h2]` |
| `grind` explodes | Timeout | Use `agrind` instead |
| `agrind` fails | Goal unsolved | Try `simp [*]; agrind` |
| Wrong step spec | Unexpected behavior | `step with specific_thm` |
| Auto-param tactic loops | `maxRecDepth`/timeout at theorem statement | Make params explicit, no `:= by ...` in recursive theorems |
| Dependent proof in `rw` | `simp only`/`rw` loops on term with proof arg | `congr 1` to separate value from proof (proof irrelevance) |
| `step*` stuck on projection | No progress on `(Struct p).field args` | `simp only [step_simps]` before `step*`; add `@[simp, step_simps]` lemma |
| Doc comment before `set_option` | Parse error "expected 'lemma'" | Use `/- ... -/` (regular comment), not `/-- ... -/` (doc comment) |
| Concrete computation fails | `agrind`/`scalar_tac` fail on numeric literals | `native_decide` or `decide` |
| `scalar_tac` in spec_gen | Cascading `maxRecDepth` in loop proof | Mass-replace ALL `scalar_tac` → `agrind` in proof body |
| Recurring index bounds slow | Same bound proved inline many times | Extract as solver-attributed lemma (`@[agrind =]`); see item 22 in `aeneas-lean-core` |
| `(by ...)` in type signature | Kernel slowness on `apply`/`exact` of theorem | Use `get_elem_tactic` override with `agrind`; if that fails, use `(by agrind)` > `(by grind)` > `(by scalar_tac)` > standalone lemma. NEVER `cases p <;> simp_all <;> tactic`. See "Never embed (by ...) in type signatures" in `aeneas-lean-core` |
| `first \| simp_all` swallows goals | `simp_all` partially simplifies, `first` considers it done | `(simp_all; done)` — forces full closure; applies to all `simp` variants |

## Debugging and Profiling Commands

```lean
set_option trace.step true        -- trace step decisions
set_option trace.scalar_tac true      -- trace scalar_tac
set_option trace.Aeneas.progress true -- detailed progress
-- ⚠️ maxHeartbeats: see guidelines below
-- ⛔ NEVER set_option maxRecDepth — see below
```

### Profiling proof time

**⚠️ `trace.profiler` only measures tactic execution time — NOT kernel type-checking.**
When a tactic introduces auxiliary theorems (e.g., `agrind`, `grind`), the kernel must
type-check those proof terms *after* the tactic finishes. `trace.profiler` does not
include this cost. **The discrepancy can be huge** — a tactic may report 50ms in the
profiler but actually take 5s wall-clock because the kernel spends 4.95s checking the
proof term it produced.

Use `trace.profiler` to identify which tactic is slow at the *tactic* level:

```lean
-- Per-tactic timing breakdown (tactic execution only, excludes kernel checking)
set_option trace.profiler true in
set_option trace.profiler.threshold 10 in  -- report tactics > 10ms (default: 100ms)

-- Overall proof timing (coarser, shows elaboration phases)
set_option profiler true in
set_option profiler.threshold 10 in
```

To measure **true wall-clock time including kernel type-checking**, use the `measure`
tactic wrapper. Define it locally (or in a shared utilities file):

```lean
/-- Measure wall-clock time of a tactic (including kernel type-checking). -/
elab "measure" t:tactic : tactic => do
  let start ← IO.monoNanosNow
  Lean.Elab.Tactic.evalTactic t
  let stop ← IO.monoNanosNow
  IO.eprintln s!"[measure] {(stop - start) / 1000000}ms"
```

Then wrap the tactic or proof script you want to measure:

```lean
theorem my_fn.spec ... := by
  measure (agrind)          -- measures agrind + kernel checking of its proof term
  measure (simp [*]; grind) -- measures the whole sequence
```

**When to use which:**
- **`trace.profiler`**: first pass — find which tactic is slow at the tactic level
- **`measure`**: second pass — verify true wall-clock cost including kernel checking.
  If `trace.profiler` says a tactic is fast but `measure` says it's slow, the
  bottleneck is kernel type-checking of the proof term the tactic produced. The fix
  is to use a tactic that produces simpler proof terms, or extract the sub-goal as
  an auxiliary lemma (which gets its own smaller proof term).

### ⚠️ `maxHeartbeats` guidelines

<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core item 13 ("Keep maxHeartbeats reasonable") -->

**⛔ NEVER use `set_option ... in` inside a proof script.** For example:
```lean
-- ⛔ BAD: breaks incrementality inside the proof
theorem my_fn.spec ... := by
  set_option maxHeartbeats 16000000 in
  step* ...
```
The `in` scoping inside a tactic block makes everything below it a single elaboration
unit — any edit forces full re-elaboration, destroying incremental feedback.

Using `set_option ... in` **before** a theorem declaration is fine and standard practice:
```lean
-- ✅ GOOD: set_option before the theorem declaration
set_option maxHeartbeats 16000000 in
theorem my_fn.spec ... := by ...
```

Lean's default `maxHeartbeats` (200K) is very low for Aeneas proofs. **Increase it to
1M as a baseline** (`set_option maxHeartbeats 1000000`) — this is a reasonable default
for most proofs.

Well-structured proofs should stay **under 8M heartbeats** even for the biggest proofs.
If you need to increase beyond that, it signals a problem with the proof — don't just
bump the number, fix the root cause:

1. **Decompose the function** — use fold theorems to split a large function into
   smaller helpers (see "Function Decomposition" in the crypto verification skill file).
   Smaller functions → smaller proof contexts → faster elaboration.
2. **Minimize the context** — `clear` unused hypotheses before expensive tactics.
   Large contexts make `simp`, `agrind`, and `grind` slower.
3. **Use `step*?` instead of `step*`** — the expanded script gives you
   control over each step and avoids the combinatorial blowup of repeated automation.
4. **Avoid `grind` when `agrind` suffices** — `grind` is much more expensive.
5. **Extract complex sub-goals as auxiliary lemmas** — a separate lemma gets a fresh,
   minimal context, which is faster for tactics to process.
6. **Check for tactic inefficiency** — if a single tactic call dominates the heartbeat
   budget, consider whether a different tactic would be faster (e.g., `bv_tac` instead
   of `agrind` for bitwise goals, `scalar_tac` instead of `agrind` for pure arithmetic).

### ⏱️ Wall-clock time target: < 60s — THIS IS IMPORTANT

<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core item 14 ("Keep proof wall-clock time < 60s") -->

**Keeping proof times low is critical for productivity.** Fast proofs mean fast iteration
— you can try tactics, see results, and adjust quickly. Slow proofs kill this feedback
loop and make proof development painful.

**The total proof time for a function should be < 60 seconds wall-clock** even for the
biggest functions (50+ lines). This includes both tactic elaboration AND kernel proof-term
replay. If a proof takes longer, it's a sign that the proof is ill-structured or uses
tactics inefficiently — it must be fixed, not tolerated.

**Note:** It can happen that the tactic proof itself runs reasonably fast but *accepting*
the proof (the kernel replaying the proof term) takes very long. This is a distinct issue
from tactic slowness — it means the proof term is too large or complex.

**How to detect kernel replay slowness:** In the LSP, after all tactics have been
elaborated, the server will report that it is still processing the last line of the proof
AND the `theorem` declaration line (along with any `set_option ... in` above it). If it
stays in this state for a long time, it is likely spending time in the kernel checking the
proof term — not running tactics.

**Fixes:** Decompose the function (fold theorems), extract sub-goals as auxiliary lemmas
(which get their own smaller proof terms), or use more direct proof strategies that
produce simpler terms.

Use `set_option trace.profiler true in` to profile tactic elaboration time. **But note:**
`trace.profiler` only measures tactic execution, not kernel type-checking — the
discrepancy can be huge. Use the `measure` tactic wrapper (see "Profiling proof time"
above) to get true wall-clock time including kernel checking. If `trace.profiler` says
tactics are fast but `measure` (or overall proof time) is slow, the bottleneck is kernel
replay — the fix is to produce simpler/smaller proof terms.

### Measuring per-file build time

To measure the elaboration time of each file in isolation (with dependencies already
built), use `lake env lean`:

```bash
cd <project-lean-root>
lake build   # ensure all dependencies are compiled
find Properties -name "*.lean" | sort | while read f; do
  printf "%s: " "$f"
  { time lake env lean "$f" ; } 2>&1 | grep "^real"
done
```

`lake env` sets up `LEAN_PATH` so bare `lean` can find all olean dependencies.
`time lean file.lean` then elaborates just that one file from scratch and reports
wall-clock time. This gives accurate per-file measurements without lake's caching
or scheduling overhead.

Note: `time` output format varies by shell. This works in both bash and zsh.

**Keeping Lean reactive is even more important.** When developing a proof interactively,
adding a tactic at the end should take **< 0.5s** — this is what enables rapid iteration.
If incremental edits are slow (several seconds), the proof structure is forcing
re-elaboration of large chunks. See the `lean-lsp-mcp` skill file for guidance
(avoid `by ...` blocks inside `apply`/`exact`/`refine` arguments, use `have` to create
elaboration checkpoints).

### ⛔ NEVER increase `maxRecDepth`

<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core item 11 ("NEVER increase maxRecDepth") -->

If you hit a `maxRecDepth` error, **do NOT increase it**. If calling any tactic
triggers `maxRecDepth`, it almost certainly means **the tactic is looping internally**
(typically via `simp`). The fix is never to raise the limit — it's to break the loop.

**Root cause: simp loops.** A simp loop occurs when two or more simp lemmas rewrite
back and forth (A → B → A → ...), or when a lemma rewrites to a term that reduces
back to the original (e.g., `s[i]'h → s[i]!` but `s[i]!` unfolds back to something
containing `s[i]'h`). This causes `simp` to recurse until it hits `maxRecDepth`.

**How to diagnose:**
1. The error says "maximum recursion depth has been reached" inside a `simp` call
2. Use the LSP: comment out the failing `simp` call, add `sorry`, inspect the goal
   with `lean_goal` to see what the `simp` was trying to simplify
3. Identify which lemmas interact badly — try each lemma individually

**How to fix (in order of preference):**
1. **Split the `simp only` call**: If `simp only [A, B, C]` loops, try splitting into
   sequential calls: `simp only [A]` then `simp only [B, C]`. The loop is often caused
   by a specific pair of lemmas — separating them breaks the cycle.
   ```lean
   -- BAD: loops because A and B interact
   simp only [A, B, C] at h ⊢
   -- GOOD: separate the conflicting lemmas
   simp only [A] at h ⊢
   simp only [B, C] at h ⊢
   ```
2. **Use `rw` instead of `simp only`**: If you only need to apply a lemma once (not
   repeatedly), `rw` is safer — it applies exactly once and doesn't loop.
   ```lean
   -- BAD: simp loops
   simp only [Slice.Inhabited_getElem_eq_getElem!] at h
   -- GOOD: apply once
   rw [Slice.Inhabited_getElem_eq_getElem!] at h
   ```
3. **Reduce the lemma list**: Remove lemmas one by one until the loop stops. The last
   lemma you removed is part of the loop — find its interaction partner.
4. **Use `conv` for targeted rewriting**: When `simp` loops because it rewrites in
   too many places, use `conv` to target a specific subterm.
5. **`clear` offending hypotheses**: If a hypothesis triggers the loop (e.g., a
   hypothesis whose type causes simp to loop when it tries to rewrite it), `clear` it
   before calling `simp` — but only if the hypothesis is irrelevant to proving the goal.
   Re-introduce it if needed.
6. **For tactics that internally use `simp`** (`agrind`, `grind`, `scalar_tac`,
   `simp_scalar`, `simp_lists`): the loop may be triggered by hypotheses in the context.
   Try `clear`-ing suspicious hypotheses before calling the tactic — but only if the
   hypothesis is irrelevant to proving the goal.

**`scalar_tac`, `simp_scalar`, and `simp_lists` trigger `simp_all` internally.** This means they can
cause `maxRecDepth` errors even though you didn't write a `simp` call yourself. The
loop is typically triggered by a hypothesis in the context — often an equation whose
LHS appears in its RHS (e.g., `h : x = f x y`), causing `simp_all` to rewrite
endlessly.

**Fixes for `scalar_tac`/`simp_scalar`/`simp_lists` maxRecDepth errors (in preference order):**
1. **Use `agrind` or `grind` instead** — they don't call `simp_all` and are immune to
   this class of loops. This is the safest fix.
2. **Identify and modify the faulty hypothesis** — look for an equation in the context
   whose LHS appears in its RHS. Reverse its direction with `rw [← h]` or `symm at h`
   before calling `scalar_tac`. This is more technical but preserves the use of
   `scalar_tac`.
3. **`clear` the offending hypothesis** before calling `scalar_tac` — but only if the hypothesis is irrelevant to proving the goal.

**Common simp loop patterns in Aeneas:**
- `Slice.Inhabited_getElem_eq_getElem!` + `List.Inhabited_getElem_eq_getElem!`:
  These can loop when used together in `simp only`, because rewriting a Slice getElem
  may expose a List getElem that rewrites back. Split them into separate calls.
- `getElem → getElem!` lemmas combined with lemmas that unfold `getElem!`: The
  `Inhabited_getElem_eq_getElem!` lemma rewrites `s[i]'h` to `s[i]!`, but if another
  lemma or reduction rule unfolds `s[i]!` back to a form containing `s[i]'h`, you
  get a loop. Use `rw` instead of `simp` for these.

### Report misbehaving tactics

If a tactic doesn't do what it should — for example, `step` fails to make progress on a goal even though the appropriate `@[step]` lemma is available, or `scalar_tac` can't close a pure arithmetic goal it should handle — **report this to the user**. It may indicate a tactic bug or a missing feature that should be fixed upstream.
