---
name: aeneas-tactics-quickref
description: Tactic decision tree, banned tactics, and common combinations for Aeneas Lean proofs
---

# Aeneas Tactics Quick Reference

## Decision Tree: Which Tactic?

**PREREQUISITE:** Always use `lean_lsp.py --repl --json` for interactive proof development. Use `goal <line>` to inspect the proof state before choosing a tactic. See the `lean-lsp-tool` skill file.

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
├─ List/Array (get/set)
│  ├─ Automatic → agrind first; if fails, try grind (slower, more list lemmas)
│  └─ Slow → cases idx <;> simp_lists [*]
│
├─ Slice/List getElem mismatch
│  ├─ Use #setup_aeneas_simps at file top (auto-converts getElem → getElem!)
│  ├─ Manual bridge → List.Inhabited_getElem_eq_getElem! s.val i proof
│  └─ Slice getElem! → List getElem! → rw [Slice.getElem!_Nat_eq]
│
├─ If-then-else → simp_ifs / split
├─ Conjunction (∧) → split_conjs <;> agrind
├─ Boolean/Propositional → simp_bool_prop / tauto
├─ Concrete computation → decide / native_decide
├─ Congruence → fcongr
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
| `step*` | Repeat step + case split | `step*`, `step* n` (n steps) | Use for final compact proof |
| `step*?` | Generate proof script | `step*?` | Start here when developing proofs |
| `scalar_tac` | Integer arithmetic/bounds | `scalar_tac`, `scalar_tac +nonLin` | `@[scalar_tac_simps]` |
| `simp_scalar` | Simplify scalar exprs | `simp_scalar`, `simp_scalar [lemmas]` | `@[simp_scalar_simps]` |
| `simp_lists` | Simplify list get/set | `simp_lists`, `simp_lists [lemmas]` | `@[simp_lists_simps]` |
| `bvify` | Lift to BitVec | `bvify N`, `bvify N at h` | `@[bvify_simps]` |
| `bv_tac` | Decide BitVec goals | `bv_tac N` | — |
| `natify` | Convert to Nat | `natify`, `natify at h` | `@[natify_simps]` |
| `zmodify` | Convert to ZMod | `zmodify`, `zmodify [to N]`, `zmodify at h` | `@[zmodify_simps]` |
| `simp_ifs` | Simplify if-then-else | `simp_ifs` | — |
| `simp_bool_prop` | Bool/prop simplification | `simp_bool_prop` | `@[simp_bool_prop_simps]` |
| `fcongr` | Congruence (safe whnf) | `fcongr`, `fcongr N` | — |
| `split_conjs` | Split nested ∧ | `split_conjs`, `split_conjs at h` | — |

### Commonly Used Lean Builtins

| Tactic | Purpose | Notes |
|---|---|---|
| `agrind` | General automation | Prefer over `grind` — faster. If it fails, try `grind` |
| `simp` / `simp [*]` | Simplification | Use `simp [*]` to keep hypotheses |
| `simp_all` | Aggressive simplification | **Caution:** may remove needed hypotheses |
| `tauto` | Propositional tautologies | |
| `decide` | Concrete decidable goals | |
| `ring` | Ring equalities | |
| `split` | Case-split match/if | |
| `cases` | Structural case analysis | |

### ⛔ BANNED TACTICS

| Banned | Why | Use instead (preference order) |
|---|---|---|
| `omega` | No scalar/Slice/Vec knowledge | `agrind` > `grind` > `scalar_tac` |
| `linarith` | No scalar/Slice/Vec knowledge | `agrind` > `grind` > `scalar_tac` |
| `nlinarith` | No scalar knowledge, explosion risk | `agrind` > `grind` > `scalar_tac +nonLin` / `simp_scalar` |

**These tactics are NEVER acceptable in Aeneas proofs** — not in `step` theorems,
not in helper lemmas, not in `have` steps, not in `decreasing_by` (even for pure Nat).
They cannot reason about U8, U32, Usize, Slice.length, etc. A proof using them is
non-idiomatic and must be rewritten. There are **no exceptions**.
See `aeneas-lean-core` skill file for the full rationale.

## Common Tactic Combinations

| Pattern | Use When |
|---|---|
| `split_conjs <;> agrind` | Goal is a conjunction |
| `simp [*]; agrind` | `agrind` alone fails (grind issue workaround) |
| `step* <;> bv_tac 32` | Monadic code with bitwise ops |
| `bvify N; bv_tac N` | Nat goal about bitwise operation |
| `have h := ...; natify at h; simp_scalar at h` | Reverse bv lifting (goal → bv → back to Nat) |
| `zify at h; zify; simp [h, Int.mul_emod]` | Modular equivalence via Int |
| `unfold fn; split; step` | Recursive function (avoid termination issue) |
| chain of `have` + `simp_scalar` | Non-linear arithmetic (modulo, division) |
| `calc _ = _ := by simp_scalar` | Equational chains for arithmetic |

## Proof Style Rules

- **Address ALL warnings** — the only acceptable warning is `"declaration uses 'sorry'"`:
  - `"This simp argument is unused"` → remove the unused lemma from `simp only [...]`
  - `"Too many ids provided"` → reduce binders in `step as ⟨...⟩`
  - `"'...' tactic does nothing"` / `"is never executed"` → remove the dead tactic
  - `"unused variable"` → remove or prefix with `_`
- **No big `simp only [...]` in implementation proofs** — model names are unstable. Use `simp [*]` or targeted rewrites. (OK in spec lemmas.)
- **Extract complex sub-proofs** as auxiliary lemmas — don't inline 15 lines of arithmetic inside `step*`
- **Simplify shifts early**: rewrite `>>>` as `/ 2^n`, `<<<` as `* 2^n`

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
| `simp_all` drops hyps | Needed hypothesis gone | Use `simp [*]` or `simp [h1,h2]` |
| `grind` explodes | Timeout | Use `agrind` instead |
| `agrind` fails | Goal unsolved | Try `simp [*]; agrind` |
| Wrong step spec | Unexpected behavior | `step with specific_thm` |

## Debugging and Profiling Commands

```lean
set_option trace.step true        -- trace step decisions
set_option trace.scalar_tac true      -- trace scalar_tac
set_option trace.Aeneas.progress true -- detailed progress
-- ⚠️ maxHeartbeats: see guidelines below
-- ⛔ NEVER set_option maxRecDepth — see below
```

### Profiling proof time

Use these options to identify slow tactics:

```lean
-- Per-tactic timing breakdown (recommended — shows each tactic's time)
set_option trace.profiler true in
set_option trace.profiler.threshold 10 in  -- report tactics > 10ms (default: 100ms)

-- Overall proof timing (coarser, shows elaboration phases)
set_option profiler true in
set_option profiler.threshold 10 in
```

Use `trace.profiler` to find which tactic dominates the time, then optimize or replace it.

### ⚠️ `maxHeartbeats` guidelines

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
3. **Use `progress*?` instead of `progress*`** — the expanded script gives you
   control over each step and avoids the combinatorial blowup of repeated automation.
4. **Avoid `grind` when `agrind` suffices** — `grind` is much more expensive.
5. **Extract complex sub-goals as auxiliary lemmas** — a separate lemma gets a fresh,
   minimal context, which is faster for tactics to process.
6. **Check for tactic inefficiency** — if a single tactic call dominates the heartbeat
   budget, consider whether a different tactic would be faster (e.g., `bv_tac` instead
   of `agrind` for bitwise goals, `scalar_tac` instead of `agrind` for pure arithmetic).

### ⏱️ Wall-clock time target: < 30s — THIS IS IMPORTANT

**Keeping proof times low is critical for productivity.** Fast proofs mean fast iteration
— you can try tactics, see results, and adjust quickly. Slow proofs kill this feedback
loop and make proof development painful.

**Aim for < 30 seconds wall-clock time** even for the biggest proofs (functions of 50+
lines). If a proof takes longer, it's a sign that the proof is ill-structured or uses
tactics inefficiently. Use `set_option trace.profiler true in` to identify the bottleneck,
then apply the strategies above (decompose, extract lemmas, minimize context, pick
better tactics).

**Keeping Lean reactive is even more important.** When developing a proof interactively,
adding a tactic at the end should take **< 0.5s** — this is what enables rapid iteration.
If incremental edits are slow (several seconds), the proof structure is forcing
re-elaboration of large chunks. See the lean-lsp-tool skill file for guidance
(avoid `by ...` blocks inside `apply`/`exact`/`refine` arguments, use `have` to create
elaboration checkpoints).

### ⛔ NEVER increase `maxRecDepth`

If you hit a `maxRecDepth` error, **do NOT increase it**. This is a symptom of a
**simp loop** or a poorly structured proof, not a depth limit to raise.

**Root cause: simp loops.** A simp loop occurs when two or more simp lemmas rewrite
back and forth (A → B → A → ...), or when a lemma rewrites to a term that reduces
back to the original (e.g., `s[i]'h → s[i]!` but `s[i]!` unfolds back to something
containing `s[i]'h`). This causes `simp` to recurse until it hits `maxRecDepth`.

**How to diagnose:**
1. The error says "maximum recursion depth has been reached" inside a `simp` call
2. Use the LSP: comment out the failing `simp` call, add `sorry`, inspect the goal
   with `goal <line>` to see what the `simp` was trying to simplify
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
   before calling `simp`, then re-introduce it if needed.
6. **For tactics that internally use `simp`** (`agrind`, `grind`, `scalar_tac`,
   `simp_scalar`): the loop may be triggered by hypotheses in the context. Try
   `clear`-ing suspicious hypotheses before calling the tactic.

**Common simp loop patterns in Aeneas:**
- `Slice.Inhabited_getElem_eq_getElem!` + `List.Inhabited_getElem_eq_getElem!`:
  These can loop when used together in `simp only`, because rewriting a Slice getElem
  may expose a List getElem that rewrites back. Split them into separate calls.
- `getElem → getElem!` lemmas combined with lemmas that unfold `getElem!`: The
  `Inhabited_getElem_eq_getElem!` lemma rewrites `s[i]'h` to `s[i]!`, but if another
  lemma or reduction rule unfolds `s[i]!` back to a form containing `s[i]'h`, you
  get a loop. Use `rw` instead of `simp` for these.

### Report misbehaving tactics

If a tactic doesn't do what it should — for example, `progress` fails to make progress on a goal even though the appropriate `@[progress]` lemma is available, or `scalar_tac` can't close a pure arithmetic goal it should handle — **report this to the user**. It may indicate a tactic bug or a missing feature that should be fixed upstream.
