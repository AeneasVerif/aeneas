# Proof Patterns — Completed Examples

This document collects fully-worked proof patterns from real-world cryptographic
verification projects. Agents should reference these patterns when writing proofs for similar
functions. Each pattern shows the complete proof with commentary.

## Pattern 1: Simple Range Loop (pointwise map)

**Use when:** A loop iterates `for i in 0..n` and writes `out[i] = f(a[i], out[i])`.

**Example:** `add_loop` — pointwise `out[i] := (a[i] + out[i]) & QMASK`.

**Structure:**
1. A **generalized spec** (`spec_gen`) with an arbitrary starting position
2. A **public spec** (`spec`) that instantiates `spec_gen` at `start = 0`
3. A **top-level spec** that unfolds the wrapper and delegates to the loop spec

### spec_gen (the workhorse)

```lean
private theorem add_loop.spec_gen
  (out out0 a : Slice Std.U16) (p)
  (hlen : out.length = a.length)
  (hlen0 : out.length = out0.length)
  (iter : core.ops.range.Range Std.Usize)
  (hlo : iter.start.val ≤ iter.«end».val)
  (hend : iter.«end».val = out.length)
  -- Invariant part 1: entries before start are "done"
  (hdone : ∀ j (hj : j < iter.start.val),
    out[j]'(by grind) = addZ p (a[j]'(by agrind)) (out0[j]'(by agrind)))
  -- Invariant part 2: entries at or after start are untouched
  (hrest : ∀ j (hj : iter.start.val ≤ j ∧ j < out.length),
    out[j]'(by grind) = out0[j]'(by agrind)) :
  crypto.add_loop (Params p) iter out a ⦃ fun res =>
    ∃ hlen' : res.length = out0.length,
    ∀ j (hj : j < res.length),
      (res[j] : Std.U16) = addZ p (a[j]'(by agrind)) (out0[j]'(by agrind)) ⦄ := by
  -- Step 1: Unfold the recursive function
  unfold crypto.add_loop
  -- Step 2: Process the range iterator
  step with range_next_usize as ⟨ret, h_range⟩
  -- Step 3: Case split on whether loop continues
  by_cases h : iter.start.val < iter.«end».val <;> simp [h] at h_range
  · -- INDUCTIVE CASE: start < end
    obtain ⟨hov, hstart', hend'⟩ := h_range
    simp only [hov]
    -- Step 4: Progress through the loop body
    step as ⟨i1, hi1⟩   -- index a[i]
    step as ⟨i2, hi2⟩   -- index out[i]
    step as ⟨i3⟩        -- wrapping_add
    step as ⟨i4, hi4⟩   -- QMASK
    step as ⟨i5⟩        -- i3 &&& i4
    step as ⟨s, hs_len, hs_eq, hs_ne⟩  -- Slice.update
    -- Step 5: Rebuild the invariant for the next iteration
    have hdone' : ∀ j (hj : j < iter.start.val + 1),
        s[j]'(by grind) = addZ p (a[j]'(by agrind)) (out0[j]'(by agrind)) := by
      intro j hj
      by_cases hji : j = iter.start.val
      · subst hji; grind [addZ]           -- freshly written entry
      · have hj' : j < iter.start.val := by scalar_tac
        have := hdone j hj'; grind         -- previously done entry
    have hrest' : ∀ j (hj : iter.start.val + 1 ≤ j ∧ j < s.length),
        s[j]'(by grind) = out0[j]'(by agrind) := by
      intro j hj; grind                    -- unchanged entry
    -- Step 6: Recursive call
    have hend_val : ret.2.«end».val = iter.«end».val := by rw [hend']
    exact add_loop.spec_gen s out0 a p (by grind) (by grind)
      ret.2 (by scalar_tac) (by grind)
      (fun j hj => hdone' j (by scalar_tac))
      (fun j hj => hrest' j ⟨by scalar_tac, by grind⟩)
  · -- BASE CASE: start ≥ end, loop is done
    obtain ⟨hnone, _⟩ := h_range
    simp only [hnone]
    refine ⟨by scalar_tac, fun j hj => ?_⟩
    have : j < iter.start.val := by scalar_tac
    exact hdone j this
-- Step 7: Termination
termination_by iter.«end».val - iter.start.val
decreasing_by
  have : ret.2.«end».val = iter.«end».val := by rw [hend']
  scalar_tac
```

### spec (public, starts at 0)

```lean
@[step]
theorem crypto.add_loop.spec
  (out a : Slice Std.U16)
  (hlen : out.length = a.length) :
  crypto.add_loop (Params p) { start := 0#usize, «end» := out.len } out a ⦃ fun res =>
    res = Slice.mapIdx out (fun j x hj => addZ p a[j] x) ⦄ := by
  apply WP.spec_mono
  · exact add_loop.spec_gen out out a p hlen rfl
      { start := 0#usize, «end» := out.len } (by simp) rfl
      (fun j hj => by simp at hj) (fun j _ => rfl)
  · intro res ⟨hlen', hall⟩
    apply Slice.ext_getElem (by simp_all) fun i h1 h2 => by
      simp only [Slice.mapIdx, Slice.getElem_Nat_eq, List.getElem_mapFinIdx]
      exact hall i (by agrind)
```

### Top-level (unfold wrapper, delegate)

```lean
@[step]
theorem crypto.add.spec p (out a : Slice Std.U16)
  (hlen : out.length = a.length) :
  crypto.add (Params p) out a ⦃ fun res =>
    res = Slice.mapIdx out (fun j x hj => addZ p a[j] x) ⦄ := by
  unfold crypto.add
  simp only [Slice.len]
  split_ifs with h
  · have : out.len = a.len := h
    step*
  · simp_all [Slice.len]
```

### Matrix-level lifting

```lean
@[step]
theorem add_spec_ext p {m n A B} (a b : Slice Std.U16)
  (halen : a.length = m * n) (ha : Slice.toMatrix a = A)
  (hblen : b.length = m * n) (hb : Slice.toMatrix b = B) :
  crypto.add (Params p) b a ⦃ fun res =>
    ∃ hreslen : res.length = m * n,
    Slice.toMatrix (p := p) res = A + B ⦄ := by
  step as ⟨res, hres⟩
  refine ⟨by grind, ?_⟩
  rw [← ha, ← hb]
  ext i j
  simp only [Slice.toMatrix, Matrix.of_apply, Matrix.add_apply]
  simp_all only [Slice.mapIdx]
  erw [List.getElem_mapFinIdx]
  exact (addZ.spec p _ _).1
```

---

## Pattern 2: Dot-Product Accumulation Loop

**Use when:** A loop accumulates `acc += a[i] * b[i]` in wrapping arithmetic,
then the result is projected to Zq.

**Example:** `mul_bs_loop0_loop0_loop0` — innermost k-loop of B×S multiply.

**Key idea:** The I32 wrapping accumulator tracks the Zq partial dot-product.
Prove a helper `toZq_hcast_step` showing that wrapping arithmetic commutes with
the Zq projection, then use `dotZq_partial_succ` to step the partial sum.

### Helper lemmas needed

```lean
-- Step the partial dot-product
private lemma dotZq_partial_succ ... :
    dotZq_partial ... (k + 1) = dotZq_partial ... k + term_k := by
  simp only [dotZq_partial]; rw [Fin.sum_univ_castSucc]; simp [...]

-- Empty partial dot-product
@[simp]
private lemma dotZq_partial_zero ... : dotZq_partial ... 0 = 0 := by simp [dotZq_partial]

-- Full partial = total
private lemma dotZq_partial_full ... :
    dotZq_partial ... (Spec.n p) = dotZq ... := by simp [dotZq_partial, dotZq]

-- Wrapping arithmetic projects to Zq
private theorem toZq_hcast_step (p) (acc : I32) (a b : U16) :
    toZq p (IScalar.hcast .U16 (wrapping_add acc (wrapping_mul (hcast a) (cast b))))
    = toZq p (IScalar.hcast .U16 acc) + toZq p a * toZq p b := by
  suffices h : ... by rw [h, toZq_wrapping_add, toZq_wrapping_mul]
  bv_tac 16
```

### spec_gen structure

```lean
private theorem inner_loop.spec_gen p (b s : Slice U16)
  (hb hs) (i j : Usize) (hi hj)
  (r : core.ops.range.Range Usize) (hlo hend)
  (acc : I32)
  (hacc : toZq p (IScalar.hcast .U16 acc) =
    dotZq_partial p b s i j hi hj r.start.val) :
  inner_loop ... r b s i j acc ⦃ fun acc' =>
    toZq p (IScalar.hcast .U16 acc') = dotZq p b s i j hi hj ⦄ := by
  unfold inner_loop
  step with range_next_usize as ⟨ret, h_range⟩
  by_cases h : r.start.val < r.«end».val <;> simp [h] at h_range
  · obtain ⟨hov, hstart', hend'⟩ := h_range; simp only [hov]
    -- step through: index b, index s, casts, wrapping_mul, wrapping_add
    step as ⟨...⟩  -- each arithmetic step
    -- Prove accumulator invariant for next iteration
    have hacc1 : toZq p (IScalar.hcast .U16 acc1) =
        dotZq_partial ... (r.start.val + 1) := by
      rw [dotZq_partial_succ ...]; rw [← hacc]; ...
      rw [toZq_hcast_step]
    -- Recurse
    exact inner_loop.spec_gen ... ret.2 ... acc1 (by convert hacc1 ...)
  · -- Base case: r.start ≥ r.end
    simp only [..., WP.spec_ok]
    rw [hacc]; convert dotZq_partial_full ...
termination_by r.«end».val - r.start.val
decreasing_by have : ret.2.«end».val = r.«end».val := by rw [hend']; scalar_tac
```

---

## Pattern 3: Nested Loop (outer calls inner)

**Use when:** An outer loop iterates rows, calling an inner loop for each row.

**Example:** `mul_bs_loop0` — outer i-loop calling the middle j-loop.

### Structure

```lean
@[step]
theorem outer_loop.spec p (out b s : Slice U16)
  (iter : core.ops.range.Range Usize) (hout hb hs hlo hhi)
  -- Invariant: rows before iter.start are already correct
  (hinv : ∀ (i j : Fin NBAR), i < iter.start.val →
    toZq p (out[i * NBAR + j]'...) = dotZq p b s i j ...) :
  outer_loop (Params p) ... iter out b s ⦃ fun res =>
    ∃ hreslen : res.length = NBAR * NBAR,
    ∀ (i j : Fin NBAR), toZq p (res[...]) = dotZq p b s i j ... ⦄ := by
  unfold outer_loop
  step with range_next_usize as ⟨ret, h_range⟩
  by_cases hcont : iter.start.val < iter.«end».val <;> simp [hcont] at h_range
  · obtain ⟨hov, hstart', hend'⟩ := h_range; simp only [hov]
    -- Call the inner/middle loop spec
    step with inner_loop.spec as ⟨out1, hout1_inv⟩
    · exact ...  -- provide required arguments
    -- Unpack the inner loop invariant
    obtain ⟨hout1_len, hout1_done, hout1_rest⟩ := hout1_inv
    -- Recurse on the outer loop
    step as ⟨res, hreslen, hres⟩
    · ...  -- provide length, bounds, invariant for next iteration
    · -- Rebuild invariant: for i < start+1, all entries correct
      intro i j hi_lt
      ... -- use hout1_done for row = start, hinv for rows < start
    exact ⟨hreslen, hres⟩
  · -- Base case
    obtain ⟨hnone, _⟩ := h_range; simp only [hnone, WP.spec_ok]
    exact ⟨by scalar_tac, fun i j => hinv i j (by scalar_tac)⟩
termination_by iter.«end».val - iter.start.val
decreasing_by ...
```

---

## Pattern 4: Constant-Time Comparison (XOR accumulation)

**Use when:** A loop accumulates `diff |= a[i] ^ b[i]` and the result tells
whether all elements were equal.

**Example:** `ct_equal_u16_loop` — XOR-accumulates differences of U16 slices.

### Key: The invariant is an iff

```lean
-- Invariant: diff = 0 ↔ all pairs before start are equal
(hinv : diff = 0#u16 ↔ ∀ j, (hj : j < iter.start.val) →
    a.val[j]'... = b.val[j]'...)
```

### Rebuilding the invariant

```lean
have hinv' : diff1 = 0#u16 ↔ ∀ j, (hj : j < iter.start.val + 1) → ... := by
  rw [show diff1 = diff ||| (a_i ^^^ b_i) by bv_tac]
  constructor
  · rw [U16.eq_or, U16.eq_xor]; grind
  · grind
```

---

## Pattern 5: Top-Level Function (unfold + delegate)

**Use when:** The top-level function does setup then calls the loop.

```lean
@[step]
theorem mul_bs.spec p (out b s : Slice U16) (hout hb hs) :
  crypto.mul_bs (Params p) out b s ⦃ fun res => ... ⦄ := by
  unfold crypto.mul_bs
  -- step through setup (creating ranges, getting parameters)
  step as ⟨n_p, hn_p⟩      -- (Params p).N
  step as ⟨nbar, hnbar⟩    -- crypto.NBAR
  -- now the loop call appears
  step with mul_bs_loop0.spec as ⟨res, hreslen, hres⟩
  · ... -- provide preconditions
  exact ⟨hreslen, hres⟩
```

---

## Pattern 6: Wrapper with Length Check (split_ifs)

**Use when:** The function starts with an `if len_a == len_b` guard.

```lean
@[step]
theorem add.spec p (out a : Slice U16) (hlen : out.length = a.length) :
  crypto.add (Params p) out a ⦃ fun res => ... ⦄ := by
  unfold crypto.add
  simp only [Slice.len]
  split_ifs with h
  · have : out.len = a.len := h
    step*
  · simp_all [Slice.len]   -- contradiction: lengths must be equal
```

---

## Common Sub-Patterns

### Slice.update reasoning (after `step` on a write)

After `step as ⟨s, hs_len, hs_eq, hs_ne⟩` on a Slice.update:
- `hs_eq`: `s[idx] = new_value` (written entry)
- `hs_ne`: `∀ j ≠ idx, s[j] = old[j]` (unchanged entries)

```lean
-- Freshly written entry
have h_written : s[idx]'... = new_value := by
  grind  -- or: simp [hs_eq]

-- Unchanged entry
have h_unchanged : s[j]'... = out[j]'... := by
  grind  -- uses hs_ne since j ≠ idx
```

### getElem! ↔ getElem bridge

When `step` gives `getElem!` but you need proof-bounded `getElem`:
```lean
have h : s.val[i]! = s[i]'proof := getElem!_pos _ _ proof
```

### Termination proof (always the same)

```lean
termination_by iter.«end».val - iter.start.val
decreasing_by
  have : ret.2.«end».val = iter.«end».val := by rw [hend']
  scalar_tac
```

### Rebuilding bounds after range_next_usize

```lean
step with range_next_usize as ⟨ret, h_range⟩
by_cases h : iter.start.val < iter.«end».val <;> simp [h] at h_range
· obtain ⟨hov, hstart', hend'⟩ := h_range
  simp only [hov]
  -- hov: ret.1 = some iter.start
  -- hstart': ret.2.start = iter.start + 1
  -- hend': ret.2.end = iter.end
```

### WP.spec_mono (strengthen postcondition)

When spec_gen gives a low-level postcondition and you want something cleaner:
```lean
@[step]
theorem loop.spec ... :
  loop ... ⦃ fun res => nice_postcondition res ⦄ := by
  apply WP.spec_mono
  · exact loop.spec_gen ...  -- gives raw postcondition
  · intro res ⟨h1, h2, ...⟩
    ... -- derive nice_postcondition from raw
```

### Index arithmetic helpers

```lean
-- (i * NBAR + j) / NBAR = i when j < NBAR
private lemma mul_NBAR_add_div (i j : ℕ) (hj : j < NBAR) :
    (i * NBAR + j) / NBAR = i := by simp_all [NBAR]; scalar_tac

-- (i * NBAR + j) % NBAR = j when j < NBAR
private lemma mul_NBAR_add_mod (i j : ℕ) (hj : j < NBAR) :
    (i * NBAR + j) % NBAR = j := by simp [NBAR]; scalar_tac
```

---

For tactic selection and banned tactics, see `aeneas-tactics-quickref.instructions.md`.
