# Tips, Tricks & Pitfalls

## Tactic Selection Quick Guide

| Goal Shape | Try First | Then Try |
|---|---|---|
| Monadic function call | `progress` | `progress with specific_theorem` |
| Arithmetic (Nat/Int) | `omega` | `scalar_tac` |
| Arithmetic (nonlinear) | `scalar_tac +nonLin` | manual `have` + `omega` |
| Scalar bounds | `scalar_tac` | `simp_scalar` |
| Bitwise operations | `bv_tac 32` | `bvify` + `bv_tac` |
| Modular equivalence | `zmodify` + ring tactics | manual |
| List get/set | `agrind` | `cases` + `simp_lists` |
| If-then-else | `simp_ifs` | `split` |
| Conjunction goal | `split_conjs <;> agrind` | `split_conjs` + manual |
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

### Split conjunctions before agrind
```lean
split_conjs <;> agrind
```
Each conjunct is easier to prove separately, so `split_conjs <;> agrind` will often succeed where `agrind` alone fails.

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
```

**Safety note:** `simp_scalar` and `simp_lists` are based on `simp`. Adding many local lemmas does NOT cause complexity explosions (unlike SMT-based tactics). Feel free to activate many ad-hoc lemmas.

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
-- Try automatic first
agrind
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
