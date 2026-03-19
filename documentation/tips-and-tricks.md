# Tips, Tricks & Pitfalls

## Before Starting a Proof

Before diving into a function proof:

1. **Think informally first.** Identify the important steps, key components, loop invariants, and what the main arguments will be. Write a brief informal proof sketch as a comment.

2. **Modularize when possible.** If sub-components of the function are natural to verify independently (they have clear specs), slice the function into pieces using the refolding technique (see proof-strategies.md). In particular, it is often useful to isolate `if-then-else` / `match` expressions into auxiliary functions with fold theorems.

3. **Don't `exact` big terms.** Large `exact ⟨..., fun x => by ..., fun y => by ...⟩` expressions are bad for proof incrementality — the LSP must re-elaborate the entire term on every edit. Instead, use `refine ⟨..., ?_, ?_⟩` or `apply` to create separate goals, then prove each with `·` focus blocks.

## Tactic Selection Quick Guide

| Goal Shape | Try First | Then Try |
|---|---|---|
| Monadic function call | `progress` | `progress with specific_theorem` |
| Arithmetic (Nat/Int) | `scalar_tac` or `agrind` | `omega` (only if pure spec, no machine ints) |
| Arithmetic (nonlinear) | `scalar_tac +nonLin` | manual `have` + `omega` |
| Scalar bounds (UScalar/IScalar) | `scalar_tac` | `agrind` |
| Bitwise operations | `bv_tac 32` | `bvify` + `bv_tac` |
| Modular equivalence | `zmodify` + ring tactics | manual |
| List get/set | `grind` (more lemmas) | `cases` + `simp_lists` |
| If-then-else | `simp_ifs` | `split` |
| Conjunction goal | `split_conjs <;> try agrind` | focus on hard goals manually |
| Boolean/prop | `simp_bool_prop` | `tauto` |
| Concrete computation | `decide` | `native_decide` |
| General automation | `agrind` | `simp [*]; agrind` |

## Common Pitfalls

### 1. Termination Error After `unfold; progress`
**Symptom:** Proof appears done but Lean reports a termination error.
**Cause:** `progress` found and applied the theorem you're currently proving (recursive application). Happens when the function starts with `match` or `if-then-else`.
**Fix:** Split first, then progress:
```lean
-- BAD: termination error
theorem my_spec ... := by
  unfold my_func
  progress  -- applies my_spec recursively!

-- GOOD: split first
theorem my_spec ... := by
  unfold my_func
  split
  · progress  -- now applies inner specs
  · progress
```

### 2. Nat Subtraction is Truncated
**Symptom:** Specification doesn't mean what you expect.
**Cause:** In Lean, `Nat` subtraction floors at 0: `3 - 5 = 0`.
**Fix:**
- Use `Int` when subtraction is involved
- Add preconditions: `(h : a ≥ b)` before using `a - b`
- Rewrite subtractions as additions: instead of `z = x - y`, write `z + y = x`

### 3. `simp_all` Eliminates Needed Hypotheses
**Symptom:** A hypothesis you need disappears after `simp_all`.
**Cause:** `simp_all` can simplify and remove hypotheses it considers redundant.
**Fix:** Use `simp` with an explicit list instead:
```lean
-- BAD: might lose hypotheses
simp_all

-- BETTER: keep hypotheses
simp [h1, h2, h3]

-- ALSO GOOD: use all hypotheses without removing them
simp [*]
```

### 4. `agrind` Fails but `simp [*]; agrind` Works
**Symptom:** `agrind` alone can't solve a goal.
**Cause:** A current issue in grind means it sometimes needs preprocessing.
**Fix:**
```lean
simp [*]; agrind    -- or: simp [*]; grind
```

### 5. `grind` Explodes (Takes Too Long)
**Symptom:** `grind` causes a timeout or uses too many heartbeats.
**Cause:** `grind` has less controlled context expansion than `agrind`.
**Fix:** Always prefer `agrind` over `grind`.

## Useful Tactic Patterns

### `scalar_tac` and `agrind` understand Rust models

`scalar_tac`, `agrind`, and `grind` know how to reason about the models of Rust definitions like `Array`, `Slice`, machine integers (`Usize`, `U32`, `UScalar`, `IScalar`, etc.). For instance, they can see through `Slice.length`. **Always prefer them over `omega`.**

**When to use `omega`:** Only when reasoning about pure specifications with only `Nat`/`Int` — no machine integers. Even then, `scalar_tac` or `agrind` often work. When reasoning about an implementation, you should use `scalar_tac` or `agrind`, never `omega`.

### `progress* n` — surgical stepping

`progress* n` runs progress for exactly `n` steps (each step is a `progress` call or a `split`). Useful when you want to advance through part of a function and stop at a specific point.

### Split conjunctions before agrind
```lean
split_conjs <;> try agrind
```
Each conjunct is easier to prove separately. The `try` lets you focus on the remaining hard goals manually.

### The `progress*?` → automate → refold workflow
1. Use `progress*?` to generate the full expanded proof script
2. Register local lemmas for `agrind`: `attribute [local agrind] my_lemma`
3. Re-run `progress*` — it now handles more sub-goals automatically
4. Repeat until the proof is compact

### Local attribute management
```lean
-- Optional: swap to bit-vector specs (bv_tac/bvify are efficient without this)
attribute [-progress] U32.add_spec U32.mul_spec
attribute [local progress] U32.add_bv_spec U32.mul_bv_spec

-- Add local simp/simp_scalar/simp_lists lemmas
attribute [local simp_scalar_simps] my_scalar_lemma
attribute [local simp_lists_simps] my_list_lemma

-- Add local agrind lemmas and patterns
attribute [local agrind =] my_equality_lemma
attribute [local agrind] my_implication_lemma
```

**Safety note:** `simp_scalar` and `simp_lists` are based on `simp`. Adding many local lemmas does NOT cause complexity explosions (unlike SMT-based tactics). Feel free to activate many ad-hoc lemmas.

Don't hesitate to register local `agrind` lemmas and patterns to make proofs using `progress` or `progress*` work — they work the same as `grind` lemmas and patterns.

### When `simp_scalar` / `simp_lists` don't work

Think about the simplifications you want to see happen, then:
- **If the corresponding lemmas already exist:** give them as additional arguments to these tactics (e.g., `simp_lists [my_lemma]`) or mark them locally with `attribute [local simp_lists_simps] my_lemma`.
- **If the corresponding lemmas don't exist:** introduce them and prove them, then mark them locally with the proper attribute (`simp_scalar_simps` or `simp_lists_simps`).

### The reverse bit-vector lifting trick
When automatic lifting between Nat/Int and BitVec fails, there are two cases:

**Case 1: Can't lift the goal to bit-vectors.** Write the bit-vector equivalent of the goal as a `have`, prove it with `bv_tac`, then convert back to Nat with `natify` and use the resulting hypothesis to prove the original goal:
```lean
have h_bv : (bv_equivalent_of_goal) := by bv_tac 32
natify at h_bv
simp_scalar at h_bv   -- then use h_bv
```

**Case 2: Can't lift a hypothesis to bit-vectors.** Write the bit-vector equivalent of the hypothesis in a `have`, and in its proof use `natify` (etc.) to transform the bit-vector target back into the original hypothesis:
```lean
have h_bv : (bv_equivalent_of_hyp) := by natify; simp [original_hyp]
-- now use h_bv with bv_tac or other bit-vector tactics
```

**When `bv_tac` fails:** Check the error message to identify terms that did not fit into the theories supported by `bv_decide`. If there are such terms, consider lifting them by hand (with the reverse lifting trick).

### Modular arithmetic: choose your domain
- **Modular equivalences** → `zmodify` to lift to ZMod (a ring — enables `ring` tactic and algebraic reasoning)
- **Bounds proofs** → stay in Nat/Int, use `scalar_tac`/`omega`

### Array access with `getElem!`
For inhabited types (common in crypto), use `getElem!`:
```lean
#setup_aeneas_simps   -- put at top of file
```
This configures simp to prefer `getElem!` and `set!` over `getElem`/`set`.

### List get/set reasoning
```lean
-- Try automatic first (grind has more list lemmas than agrind)
grind
-- If too slow, go manual
cases h_idx <;> simp_lists [*]
```

## Debugging

### Tracing tactics
```lean
set_option trace.progress true           -- trace progress tactic decisions
set_option trace.scalar_tac true         -- trace scalar_tac
set_option trace.Aeneas.progress true    -- more detailed progress traces
```

### Checking what progress would do
```lean
progress*?   -- prints the expanded proof script without committing to it
```

## Performance Tips

### Proof time matters
If a proof is slow:
1. **Decompose** into smaller lemmas
2. **Extract `have` statements** to guide automation
3. **Use fold theorems** for large function bodies
4. **Prefer `agrind` over `grind`** — less explosion
5. **Shorten proofs** — shorter proofs check faster

### Heartbeat budget
```lean
set_option maxHeartbeats 5000000 in   -- for a specific theorem
set_option maxRecDepth 2048 in        -- for deep recursion
```
Use these as escape hatches, not default settings. If you need them, consider decomposing the proof instead.

### After completing a proof
Always try to make it shorter:
- Can multiple `simp` calls be merged?
- Can intermediate steps be eliminated?
- Can `progress*` handle more of it with registered lemmas?

Shorter proofs are easier to maintain, faster to check, and easier for others to read.

## Proof Time Budget

**Expected proof times (rough guide):**

| Function complexity | Expected time | Action if exceeded |
|---|---|---|
| Simple (3–5 monadic binds) | 0.5–2s | — |
| Medium (10–15 binds) | 2–10s | — |
| Complex (20+ binds) | 10–60s | Consider decomposition |
| >60s | — | **Decompose** (fold theorems, helper lemmas) |

**Red flags that a proof will be slow:**
- More than ~25 `progress` calls in sequence
- Deeply nested quantifiers in the spec
- Using `grind` instead of `agrind`
- Large `simp` calls with many hypotheses
- Calls to `simp_all` in a big function

**When to use `maxHeartbeats`:**
- Last resort only, after attempting decomposition
- If you need >1,000,000 heartbeats, the proof needs restructuring, not more time

## Quick Reference: Attribute Tags

| Attribute | Used by | Purpose |
|---|---|---|
| `@[progress]` | `progress` tactic | Register function specifications |
| `@[simp_scalar_simps]` | `simp_scalar` | Register scalar simplification lemmas |
| `@[simp_lists_simps]` | `simp_lists` | Register list simplification lemmas |
| `@[bvify_simps]` | `bvify` | Register bit-vector lifting lemmas |
| `@[natify_simps]` | `natify` | Register Nat conversion lemmas |
| `@[zmodify_simps]` | `zmodify` | Register ZMod conversion lemmas |
| `@[simp_bool_prop_simps]` | `simp_bool_prop` | Register boolean/prop lemmas |
| `@[scalar_tac_simps]` | `scalar_tac` | Register arithmetic lemmas |
| `@[agrind]` / `@[agrind =]` | `agrind` | Register agrind lemmas |
| `@[simp]` | `simp` | Standard Lean simp lemmas |

## Reasoning About Constants and Globals

When working with Rust constants/globals translated by Aeneas:

- **Pure constants** (not in the `Result` monad): Mark them with appropriate attributes so automation can use them:
  - `@[simp]`, `@[agrind]`, `@[scalar_tac_simps]`, `@[bvify_simps]`
  - `@[simp_lists_simps]` if they involve lists/arrays

- **Monadic constants** (in the `Result` monad): Treat them like functions and prove a `@[progress]` theorem.
  - First prove a raw equation: `theorem MyConst_eq : MyConst = ok value := by native_decide`
  - Then prove the progress form: `@[progress] theorem MyConst : MyConst ⦃ fun res => res = value ⦄ := by rw [MyConst_eq]; simp [WP.spec_ok]`
  - Now `progress` will handle the constant automatically.
