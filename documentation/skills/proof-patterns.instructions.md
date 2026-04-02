---
name: proof-patterns
description: Canonical proof patterns for Aeneas Lean proofs — loop template, function wrappers, and common sub-patterns
---

# Proof Patterns — Reference Examples

Canonical proof patterns for Aeneas-generated Lean code. Each pattern shows the
minimal structure needed; adapt to your specific function.

## Loop — Canonical Template

Every loop proof follows the same skeleton. The only things that change
between loops are: (a) what the loop body does, (b) what the invariant says.

**Three theorems per loop:**
1. `spec_gen` — generalized loop spec with arbitrary start position + invariant
2. `spec` — public `@[step]` wrapper that instantiates `spec_gen` at `start = 0`
3. Top-level function spec — unfolds the wrapper function, delegates to `spec`

### spec_gen — Variant A: `step*` does the work (PREFERRED)

Use this when the loop body is simple enough for `step*` to handle automatically.
Only a few proof obligations remain after `step*` — typically the invariant
rebuild and the base case.

```lean
private theorem my_loop.spec_gen
  (out out0 a : Slice Std.U16)
  (hlen : out.length = a.length)
  (hlen0 : out.length = out0.length)
  (iter : core.ops.range.Range Std.Usize)
  (hlo : iter.start.val ≤ iter.«end».val)
  (hend : iter.«end».val = out.length)
  -- Invariant: entries before start are processed
  (hdone : ∀ j, j < iter.start.val → out[j] = f a[j] out0[j])
  -- Invariant: entries at or after start are untouched
  (hrest : ∀ j, iter.start.val ≤ j → j < out.length → out[j] = out0[j]) :
  my_loop iter out a ⦃ fun res =>
    res.length = out0.length ∧
    ∀ j, j < res.length → res[j] = f a[j] out0[j] ⦄ := by
  unfold my_loop
  step*
  -- Remaining obligations (typically invariant rebuild + base case):
  · -- Invariant rebuild: entries before start+1 are done
    intro j hj
    by_cases hji : j = iter.start.val
    · subst hji; simp [*]   -- freshly written entry
    · apply hdone; agrind  -- previously done entry
  · -- Invariant rebuild: entries after start+1 are untouched
    intro j hlo hhi; apply hrest <;> agrind
  · -- BASE CASE: loop done
    split_conjs <;> agrind
termination_by iter.«end».val - iter.start.val
decreasing_by agrind
```

### spec_gen — Variant B: manual `step as` (when step* can't handle the body)

Use this when the loop body has complex monadic steps that `step*` can't resolve
automatically, or when you need fine control over naming.

```lean
private theorem my_loop.spec_gen
  ... -- same signature as Variant A
  := by
  unfold my_loop
termination_by iter.«end».val - iter.start.val
decreasing_by agrind
```

### spec (public, starts at 0)

```lean
@[step]
theorem my_loop.spec (out a : Slice Std.U16) (hlen : out.length = a.length) :
  my_loop { start := 0#usize, «end» := out.len } out a ⦃ fun res =>
    res.length = out.length ∧
    ∀ j, j < res.length →
      res[j] = f (a[j]) (out[j]) ⦄ := by
  apply WP.spec_mono
  · apply my_loop.spec_gen <;> agrind   -- instantiate spec_gen at start=0
  · intro res ⟨h1, h2⟩; split_conjs <;> agrind   -- derive final postcondition
```
### Top-level function (unfold wrapper, delegate)

```lean
@[step]
theorem my_function.spec (out a : Slice U16) (hlen : out.length = a.length) :
  my_function out a ⦃ fun res => ... ⦄ := by
  unfold my_function
  step*
  · ... -- proof of precondition 1
  · ... -- proof of precondition 2
  · ... -- proof of goal
```

### Key points

- ❌ **Never use `partial_fixpoint_induct`** — it requires an explicit motive,
  a sorry'd `admissible` proof, and manual IH threading.
- ✅ Prefer `step*` (Variant A) over manual `step as` (Variant B).
- ✅ `step*` auto-resolves preconditions of the recursive call from context.
- ✅ `termination_by iter.end.val - iter.start.val` + `decreasing_by agrind`
  is the universal termination pattern (the termination measure and the decreasing proof vary)
- For **nested loops** (outer calls inner): the outer `spec_gen` calls the
  inner loop's `@[step]` spec via `step with inner_loop.spec`, then rebuilds
  the outer invariant.

---

## Common Sub-Patterns

### WP.spec_mono (strengthen postcondition)

When `spec_gen` gives a low-level postcondition and you want something cleaner:
```lean
apply WP.spec_mono
· apply loop.spec_gen <;> agrind   -- gives raw postcondition
· intro res ⟨h1, h2, ...⟩; ... -- derive nice_postcondition from raw
```

---

## Congruence on function equalities

When the goal is `f(impl_args) = f(spec_args)`, use `fcongr 1`
(NOT `congr 1`) to split into per-argument subgoals:

```lean
-- Goal: f(a_impl, b_impl) = f(a_spec, b_spec)
fcongr 1
· -- a_impl = a_spec
  simp [...]
· -- b_impl ≍ b_spec  (HEq when dependent type indices differ)
  ...
```

**Why `fcongr`?** It wraps `congrN` with reducible transparency.
`congr` uses default transparency and may unfold definitions deeply,
causing heartbeat timeouts. `fcongr` produces identical subgoals
without the overhead.

**HEq subgoals:** When arguments are `Vector α n` and `Vector α m`
with `n ≠ m` syntactically but propositionally equal, `fcongr`
produces `HEq` (`≍`) goals. Close by showing the underlying data
is equal and using proof irrelevance.

---

For tactic selection and banned tactics, see the `aeneas-tactics-quickref` skill file.
