# Proof Strategies for Aeneas + Lean

## The Standard Proof Structure

The basic pattern for verifying an Aeneas-generated function:

```lean
@[progress]
theorem my_function_spec (x : U32) (h : precondition) :
  my_function x ⦃ result => postcondition result ⦄ := by
  unfold my_function
  progress           -- applies specs of called functions
  -- finish remaining goals
```

The `⦃ result => postcondition ⦄` notation is the weakest-precondition spec notation. For functions returning `Result T`, it means "if the function succeeds, the result satisfies the postcondition."

For functions with backward continuations:
```lean
@[progress]
theorem choose_spec {T : Type} (b : Bool) (x y : T) :
  choose b x y ⦃ z back =>
    (b → z = x ∧ ∀ z', back z' = (z', y)) ∧
    (¬b → z = y ∧ ∀ z', back z' = (x, z')) ⦄ := by ...
```

## The `progress*?` Workflow

This is one of the most effective proof strategies:

1. **Generate a complete proof script** by using `progress*?`. This interactively applies `progress` repeatedly, doing case splits on branches, and outputs the full expanded proof script.

2. **Review the generated script.** It will be verbose but complete. Each line applies one `progress` step or handles a case.

3. **Automate proof obligations.** Many of the intermediate goals left by `progress` can be automated. Register lemmas locally for `agrind`:
   ```lean
   attribute [local agrind] my_lemma1 my_lemma2
   ```
   This way, `progress*` will discharge those goals automatically on the next run.

4. **Refold the proof.** Progressively replace the expanded script with `progress*`, which now handles more goals automatically thanks to the registered lemmas. The final proof might be a single `progress*` call followed by a small finishing script.

**Example from tests/lean/Tutorial/Solutions.lean:**
```lean
-- Using progress* to do most of the work
theorem list_nth_mut1_spec'' {T: Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.toList.length) :
  list_nth_mut1 l i ⦃ x back =>
    x = l.toList[i.val]! ∧
    ∀ x', (back x').toList = l.toList.set i.val x' ⦄ := by
  unfold list_nth_mut1 list_nth_mut1_loop
  /- `progress*` repeatedly applies `progress`, while doing a case disjunction whenever it
      encounters a branching. Note that one can automatically generate the corresponding
      proof script by using `progress*?`. -/
  progress*
  simp_all
```

## Dealing with Monadic Code

Aeneas-generated code uses the `Result` error monad with `do` notation:

```lean
def my_function (x : U32) (y : U32) : Result U32 := do
  let z ← x + y          -- monadic bind; may fail on overflow
  let w ← z * 2#u32      -- another potentially-failing operation
  ok w                    -- explicit success
```

**Key monadic patterns:**
- `let x ← expr` — monadic bind (may fail)
- `let x := expr` — pure let binding (cannot fail)
- `ok v` — return success
- `fail` — return failure
- `massert condition` — monadic assert (fails if condition is false)

When proving specs of monadic code, `progress` handles the bind steps one at a time. Each call to `progress` peels off one `let x ← f args` and applies the specification of `f`.

## Recursive Functions and the Termination Pitfall

**The pitfall:** If you write:
```lean
theorem my_recursive_fn_spec ... :=  by
  unfold my_recursive_fn
  progress
```
and the proof appears finished but Lean reports a termination error, it's because `progress` found your own theorem (the one you're currently proving) and applied it recursively. This typically happens when the function starts with a `match` or `if-then-else`.

**The fix:** Case-split first before calling `progress`:
```lean
theorem my_recursive_fn_spec ... := by
  unfold my_recursive_fn
  split         -- or: cases ..., or: simp_ifs
  . progress    -- first branch
    ...
  . progress    -- second branch
    ...
```

By splitting first, `progress` sees a non-recursive goal shape and applies the correct inner specs rather than the theorem being proved.

## Loop Reasoning with `loop.spec`

Rust loops are translated to a fixed-point operator `loop`. To reason about loop correctness, use:

- **`loop.spec_decr_nat`** (most common) — requires a `Nat` termination measure, a loop invariant, and a postcondition:

```lean
theorem loop.spec_decr_nat
  (measure : α → Nat)
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → Result (ControlFlow α β)) (x : α)
  (hBody : ∀ x, inv x → body x ⦃ r =>
    match r with
    | .done y => post y
    | .cont x' => inv x' ∧ measure x' < measure x ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄
```

- **`loop.spec`** — general version with an arbitrary well-founded termination measure (use when `Nat` isn't convenient).

**Proof pattern:**
1. Identify the loop invariant (what holds at each iteration)
2. Choose a termination measure (typically a `Nat` that decreases)
3. Apply `loop.spec_decr_nat` (or `loop.spec`)
4. Prove the body preserves the invariant and decreases the measure on `cont`
5. Prove the body establishes the postcondition on `done`

## Splitting Large Functions (Function Decomposition)

When a Rust function is large, the Aeneas-generated Lean code may contain long sequences of monadic binds that are difficult to verify in one shot. The solution: **introduce helper definitions on the Lean side** that extract portions of the function body.

**Pattern from symcrust's Ntt.lean:**

1. Define a helper function that captures a subsequence of operations:
```lean
private def reduce_add_mont_reduce (a : U32) : Result U32 := do
  let i2 ← lift (core.num.U32.wrapping_mul a ntt.NEG_Q_INV_MOD_R)
  let inv ← lift (i2 &&& ntt.RMASK)
  let i3 ← inv * ntt.Q
  let i4 ← a + i3
  let a1 ← i4 >>> ntt.RLOG2
  pure a1
```

2. Prove a "fold" theorem that shows the inlined version equals the helper:
```lean
private theorem fold_reduce_add_mont_reduce (a : U32) (f : U32 → Result α) :
  (do
    let i2 ← lift (core.num.U32.wrapping_mul a ntt.NEG_Q_INV_MOD_R)
    let inv ← lift (i2 &&& ntt.RMASK)
    let i3 ← inv * ntt.Q
    let i4 ← a + i3
    let a1 ← i4 >>> ntt.RLOG2
    f a1) =
  (do
    let a1 ← reduce_add_mont_reduce a
    f a1)
  := by
  simp only [reduce_add_mont_reduce, bind_assoc_eq, bind_tc_ok, pure]
```

3. Use `simp only [fold_reduce_add_mont_reduce]` in the main proof to replace the inline sequence with the helper function call.

4. Prove specs for the helper functions independently.

This technique makes large proofs tractable by breaking them into manageable pieces.

## Finding Existing Specifications

**Before writing a new spec, always search for an existing one.** Many functions already have specs.

### Where to look:

1. **Same file or companion Properties file:**
   ```
   grep -r "theorem.*<function_name>.*spec" .
   ```

2. **Aeneas library primitives** (already have specs):
   - `U32.add_spec`, `U64.mul_spec`, etc. — scalar arithmetic
   - `Vec.push_spec`, `Vec.index_spec`, etc. — vector operations
   - `Array.index_spec`, `Array.update_spec`, etc. — array operations
   - These are imported with `import Aeneas`

3. **External function models:**
   - Check `FunsExternal.lean` / `TypesExternal.lean` for hand-written models

4. **Already-proved specs in the project:**
   ```
   grep -r "@\[progress\]" . --include="*.lean"
   ```

### When to write a new spec:

- The function is Aeneas-generated and has no existing spec
- An existing spec doesn't provide the postcondition you need (write a more specific variant)
- The function is a helper you decomposed (fold theorem pattern)

## Intermediate Pure Specifications (Auxiliary Specs)

When the refinement proof (proving that the Aeneas code matches a high-level spec) is complex, introduce an **auxiliary specification** that:
- Closely follows the implementation structure
- But is pure (doesn't live in the error monad)
- Acts as a bridge between the high-level mathematical spec and the low-level Aeneas code

**The symcrust CompressEncode proofs demonstrate this pattern well:**

```
Nist spec ⟷₁ Lean spec ⟷₂ Auxiliary spec ⟷₃ Aeneas translation
```

Where:
- **Nist spec** = the mathematical specification (e.g., FIPS 203)
- **Lean spec** = direct Lean translation of the Nist spec. Always pure — may use monadic notation (Id monad) but never the Result monad.
- **Auxiliary spec** = intermediate spec that mirrors the code structure, also pure
- **Aeneas translation** = the generated Lean code (lives in the Result monad)

Prove equivalences between adjacent levels separately. Each proof is simpler because the specs are structurally similar at each level.

**Example header from CompressEncode.lean:**
```lean
/-!
`Nist spec ⟷₁ Lean spec ⟷₂ Auxiliary spec ⟷₃ Aeneas translation`
  - `Nist spec` corresponds to (4.7) (Compress) and Algorithm 5 (ByteEncode).
  - `Lean spec` corresponds to `Symcrust.Spec.compress` and `Symcrust.Spec.byteEncode`.
  - `Auxiliary spec` corresponds to `Symcrust.SpecAux.compress` and `Stream.encode`.
  - `Aeneas translation` corresponds to `Symcrust.ntt.poly_element_compress_and_encode`.
-/
```

Compare with the `progress_spec_aux` / `progress_spec` layering:
- `encode_coefficient.progress_spec_aux` — proves a low-level property relating to the auxiliary spec
- `encode_coefficient.progress_spec` — proves the full specification using the aux result

## Locally Activating/Deactivating Attributes

Control which specifications tactics use by locally managing attributes:

```lean
-- Use bit-vector specs instead of default integer specs
attribute [-progress] U32.add_spec U32.mul_spec
attribute [local progress] U32.add_bv_spec U32.mul_bv_spec

-- Use simpler cast specification
attribute [-progress] UScalar.cast.progress_spec
attribute [local progress] UScalar.cast_inBounds_spec

-- Add custom simplification lemmas locally
attribute [local simp_scalar_simps] my_custom_scalar_lemma
attribute [local simp_lists_simps] my_custom_list_lemma
```

**Safety of local lemma activation for simp-based tactics:** `simp_scalar` and `simp_lists` are based on `simp`, which performs local rewriting. Unlike SMT solvers, adding many lemmas does not lead to long chains of reasoning or complexity explosions. It's perfectly safe (and often necessary) to locally activate many ad-hoc lemmas for these tactics.

## Nat Subtraction Pitfall

**Critical:** In Lean, `Nat` subtraction is **truncated** — it floors at 0. This means `3 - 5 = 0`, not `-2`.

When writing specifications that use Nat subtraction:
```lean
-- DANGER: this might not mean what you think!
theorem my_spec (n : Nat) : some_function n ⦃ r => r = n - 1 ⦄
-- When n = 0, this says r = 0, which might not be the intended semantics
```

**Solutions:**
- Use `Int` when subtraction is involved
- Add explicit preconditions: `(h : n ≥ 1)`
- Rewrite subtractions as additions: instead of `z = x - y`, write `z + y = x`
- Be aware that Nat subtraction in specifications can silently give wrong results

## Inhabited Types and `getElem!`

In cryptographic code, types are often inhabited (e.g., arrays of known size). In this context, prefer `getElem!` (the bang version) over `getElem`:
- `getElem!` returns a default value for out-of-bounds access (no proof obligation for the index)
- `getElem` requires a proof that the index is in bounds

**Setup:** Add `#setup_aeneas_simps` at the top of your file. This:
- Deactivates lemmas that convert `getElem!` to `getElem?`/`getD`
- Activates lemmas that convert `getElem` to `getElem!` and `set` to `set!`

```lean
#setup_aeneas_simps

-- Now getElem! is the preferred access pattern
```

## Bit-Vector Reasoning

### When to use which tactic:
- **`bvify` + `bv_tac`**: For proving identities involving bitwise operations (AND, OR, XOR, shifts)
- **`scalar_tac`**: For arithmetic bounds and overflow checking
- **`natify` + `simp`/`simp_scalar`**: When you need to convert bit-vector results back to natural numbers

### The Reverse Lifting Trick
When `bv_tac` doesn't automatically lift a Nat/Int proposition to bit-vectors:

1. Write the expected bit-vector proposition manually with `have`:
```lean
have h_bv : (some BitVec expression) = (expected value) := by bv_tac 32
```
2. Convert back to Nat:
```lean
natify at h_bv
simp_scalar at h_bv   -- then use h_bv
```

## Modular Arithmetic Strategy

- **For modular reasoning** (e.g., `a % n = b % n`): Use `zmodify` to lift to `ZMod`, then reason algebraically. ZMod is a ring, so `ring` and algebraic lemmas apply directly.
- **For bounds** (e.g., `a < n`): Stay in `Nat`/`Int` and use `scalar_tac`, `omega`

**Example from Montgomery reduction:**
```lean
-- Use zmodify to reason about modular equivalence
zmodify at h_q_minus_1
-- Stay in Nat/Int for bounds
scalar_tac +nonLin
```

## List Reasoning (get/set)

When reasoning about list operations with `get` and `set`:
- **First try** `agrind` — it handles many get/set patterns automatically
- **If too slow**, switch to more manual proofs: use `cases` to case-split on index comparisons, then `simp_lists`/`simp` for each case

```lean
-- Automatic approach (try first)
agrind

-- Manual fallback (if agrind is too slow)
cases h_idx
· simp_lists
· simp_lists [*]
```

## The `simp [*]; agrind` Trick

Due to a current issue in `grind`, `simp [*]; agrind` can solve goals that `agrind` alone cannot. When `agrind` fails on a goal, try prepending `simp [*]`:

```lean
-- If this fails:
agrind
-- Try this:
simp [*]; agrind
```

## Splitting Conjunctions Before `agrind`

When the goal is a conjunction, split it before calling `agrind`:

```lean
split_conjs <;> agrind
```

This is more effective than calling `agrind` on the conjunction directly: each conjunct is easier to prove separately, so `split_conjs <;> agrind` will often succeed where `agrind` alone fails.

## Proof Brevity and Performance

**After completing a proof, try to make it shorter.** Shorter proofs are:
- Easier to maintain when the codebase evolves
- Faster to type-check
- Easier for others to understand

**Proof time matters.** If a proof takes too long to check:
- Decompose it into smaller lemmas
- Extract helper `have` statements to guide automation
- Consider the function decomposition technique (fold theorems)
- Use `set_option maxHeartbeats N` as a last resort, not a first response

## Summary: Proof Development Flow

1. Start with `unfold foo`
2. If the function starts with match/if: use `split` first
3. Try `progress*` — if it works, great!
4. If not, use `progress*?` to generate a full script
5. Identify hard sub-goals and prove them manually or register automation lemmas
6. For loops: use `loop.spec_decr_nat` with an invariant and termination measure
7. For large functions: decompose with fold theorems
8. For complex refinements: introduce auxiliary specs
9. Refold the proof to be as short as possible
10. Check proof time — decompose if too slow

## What To Do Next (Decision Tree)

When you're stuck after a tactic, use `goal` (via lean_lsp.py) to inspect the current proof state, then follow this guide:

**The goal has a monadic bind (`let x ← f args; ...`):**
→ `progress` (or `progress with <thm>` if auto-resolution fails)
→ If `progress` fails: does `f` have a spec? Search with `grep -r "theorem.*f.*spec"`.
→ If no spec exists: you need to write one first.

**The goal is arithmetic (`a + b ≤ c`, `x < 2^32`, etc.):**
→ Linear: `omega` or `scalar_tac`
→ Nonlinear: `scalar_tac +nonLin`
→ Simplification needed first: `simp_scalar` then `omega`/`scalar_tac`

**The goal involves bit operations (`&&&`, `|||`, `>>>`, `<<<`):**
→ `bv_tac 32` (or 64, matching the bit-width)
→ If goal is about Nat but involves bitwise: `bvify 32; bv_tac 32`
→ If `bvify` fails: use the reverse lifting trick (see Bit-Vector Reasoning)

**The goal involves modular arithmetic (`a % n`, ZMod):**
→ `zmodify; ring` (ZMod is a ring, so `ring` works well there)
→ For bounds (`a < n`): stay in Nat/Int, use `scalar_tac`/`omega`

**The goal involves lists/arrays (`getElem!`, `set`):**
→ `agrind`
→ If slow: `cases idx <;> simp_lists [*]`

**The goal is a conjunction (`A ∧ B ∧ C`):**
→ `split_conjs <;> agrind` (each conjunct is easier to prove separately)

**The goal has an if-then-else:**
→ `simp_ifs` or `split`

**Nothing works:**
→ Try `simp [*]; agrind`
→ Still stuck? Inspect the goal carefully — you may need a `have` with a key intermediate fact
→ Check if preconditions in your theorem are strong enough
