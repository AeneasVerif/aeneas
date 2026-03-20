# Aeneas + Lean Core Skill File

## Context
Aeneas translates Rust programs to pure Lean code via the LLBC intermediate representation. The generated code uses the `Result` error monad. Proofs verify functional correctness by writing specification theorems tagged with `@[step]`.

## PREREQUISITE: Use lean_lsp.py for All Proof Work

**Before writing or editing any Lean proof**, start a `lean_lsp.py` REPL session:

```bash
python3 scripts/lean_lsp.py --repl --json
```

This gives you incremental checking, proof goal inspection, and error feedback without rebuilding the full file. See the `lean-lsp-tool` skill file for the complete command reference.

**Minimal workflow:**
1. `open <file.lean>` — open and elaborate the file
2. `sorry` — find proof obligations
3. `goal <line>` — see what needs to be proved
4. `edit <line> <tactic>` — try a tactic
5. `errors` — check if it worked
6. Repeat 3–5 until done

## Reading Aeneas-Generated Code

### File layout
- `Types.lean` — Rust types → Lean inductive types
- `Funs.lean` — Rust functions → Lean monadic functions (Result monad)
- `FunsExternal.lean` — Hand-written models of external (e.g., std library) functions
- `TypesExternal.lean` — Hand-written models of external types

### Scalar types
`U8`, `U16`, `U32`, `U64`, `U128`, `Usize` (unsigned), `I8`, `I16`, `I32`, `I64`, `I128`, `Isize` (signed).
- `.val` gives the `Nat` (unsigned) or `Int` (signed) value
- `.bv` gives the `BitVec` representation
- Literals: `0#u32`, `1#i64`, etc.
- Arithmetic operations return `Result` (may fail on overflow)

### Translation patterns
| Rust | Lean |
|---|---|
| `&mut T` param | `T` param (by value) |
| Return `&'a mut T` | Returns `Result (T × (T → ...))` — backward continuation |
| `&T` (shared) | `T` param (may be copied) |
| `panic!()` | `fail` |
| Integer overflow | `fail` |
| `Box<T>` | `T` |
| `Vec<T>` | `Vec T` (Aeneas Vec, backed by `List`) |
| `[T; N]` | `Array T N` |
| Pattern match | `match` |
| Traits | Type classes |

### The backward continuation pattern
When a Rust function returns a mutable borrow, the Lean translation returns a tuple `(value, backward_fn)`:
```lean
def choose {T : Type} (b : Bool) (x : T) (y : T) :
  Result (T × (T → T × T)) :=
  if b then ok (x, fun z => (z, y))
  else ok (y, fun z => (x, z))
```
The backward function propagates updates back to the original variables.

### Writing models of Rust code
When writing hand-written models of Rust functions (e.g., in `FunsExternal.lean`):
- **Do NOT use `partial`** — `partial` definitions are opaque and cannot be unfolded or
  reasoned about. If the function lives in `Result`, use `partial_fixpoint` instead.
- **Do NOT use `private`** — we need access to all definitions so that we can unfold
  them and reason about them in proofs.

## The Specification Pattern

### Template
```lean
/-- **Spec theorem for `crate_name::module::function_name`**
Concise natural-language description of the spec. -/
@[step]
theorem function_name.spec (params : Types) (preconditions : hypotheses) :
    function_name params ⦃ (result : ResultType) =>
      postcondition result ⦄ := by
  unfold function_name
  step  -- or step* for automation
  -- finish remaining goals
```

### With backward function
```lean
@[step]
theorem function_name.spec (param1 : U32) (param2 : Slice U16)
    (hpre : param1.val < param2.length) :
    function_name param1 param2 ⦃ (result : U32) (back : U32 → Slice U16) =>
      postcondition_on_result ∧
      postcondition_on_backward_function back ⦄ := by ...
```

### Indentation rules for spec theorems
- `@[step]` and `theorem name`: base indentation (0 additional)
- Arguments, preconditions, and the line with the function application: +4 spaces
- Postconditions inside `⦃ ⦄`: +6 spaces
- Proof body (after `:= by`): +2 spaces
- Always annotate the result with its type: `(result : ResultType) =>`

### Key guidelines for spec theorems
- **Docstring**: add a `/-- **Spec theorem for \`full::rust::path\`** ... -/` docstring
  with a concise natural-language description of the spec.
- **Naming**: the theorem name is the function's full Lean name with suffix `.spec`.
  Open namespaces so the identifier prefix doesn't clutter the code.
- **Argument names**: name the spec theorem arguments exactly like the corresponding
  entities in the original Lean function definition.
- **Result type annotation**: always annotate the result binder with its type,
  e.g., `⦃ (result : U32) =>` — this makes the postcondition readable and helps
  type inference.
- **Postconditions**: write them as a conjunction `post1 ∧ post2 ∧ ...` inside `⦃ ⦄`.
- **Dependent postconditions**: if type-checking `b` in `a ∧ b` requires `a` to hold
  (e.g., `b` contains a `getElem` expression and `a` provides the index bound), use
  `∃ (_ : a), b` instead. This makes the proof of `a` available when elaborating `b`:
  ```lean
  -- BAD: won't type-check because res[i] needs hlen
  hlen : res.length = n ∧ res[i] = 42
  -- GOOD: hlen is in scope when type-checking res[i]
  ∃ (hlen : res.length = n), res[i] = 42
  ```
- **`@[step]` attribute**: always add it so the Aeneas `step` tactic can
  find the theorem. Start a new line after the attribute.

### The `⦃ ⦄` notation
Weakest precondition: `f ⦃ x => P x ⦄` means "if f succeeds with value x, then P x holds."

When the result is a tuple, decompose it directly in the binder — no need to
destructure manually:
```lean
-- Result is (U32 × Slice U16)
fun_name a b ⦃ (x : U32) (s : Slice U16) =>
  x.val < 100 ∧ s.length = a.length ⦄
```

## Proof Development Workflow

### Decision tree for starting a proof:

1. Does the function start with `match`/`if`?
   - YES → `unfold fn; split` then `step` per branch
   - NO → `unfold fn; step`

2. Is the function simple (few monadic steps, say ≤ 5)?
   - YES → `unfold fn; step*` may complete it directly
   - NO → Use `step*?` to generate an expanded proof script, then work from there

3. Is the function large/complex (10+ monadic steps)?
   - Start with `step*?` to generate the step-by-step script
   - Work through the generated script, fixing any sub-goals that fail
   - Once the whole proof is done, try collapsing back into `step*` if possible
   - You can increase `set_option maxHeartbeats` if needed (it's fine to do so)

### The step*? → fix → collapse workflow:
1. `step*?` — generates expanded proof script (one `step` per monadic call)
2. Copy the generated script into your proof
3. Work through it: fix failing sub-goals, add lemmas, adjust tactics
4. Once the full proof works, try collapsing sections back to `step*`
5. If `step*` works on the whole body, use that (shorter is better)
6. If not, keep the expanded script for the parts that need manual intervention

## Tactic Quick Reference

### Primary tactics (Aeneas-specific)
| Tactic | Use for | Syntax |
|---|---|---|
| `step` | Apply function spec | `step`, `step as ⟨x, h⟩`, `step with thm` |
| `step*` | Repeated step | `step*` |
| `step*?` | Generate proof script | `step*?` |
| `scalar_tac` | Integer arithmetic/bounds | `scalar_tac`, `scalar_tac +nonLin` |
| `simp_scalar` | Simplify scalar exprs | `simp_scalar [lemmas]` |
| `simp_lists` | Simplify list get/set | `simp_lists [lemmas]` |
| `bvify` | Lift to BitVec | `bvify N`, `bvify N at h` |
| `bv_tac` | Decide BitVec goals | `bv_tac N` |
| `natify` | Convert to Nat | `natify`, `natify at h` |
| `zmodify` | Convert to ZMod | `zmodify`, `zmodify [to N]` |
| `simp_ifs` | Simplify if-then-else | `simp_ifs` |
| `simp_bool_prop` | Simplify bool/prop | `simp_bool_prop` |
| `fcongr` | Congruence (safe whnf) | `fcongr`, `fcongr N` |
| `split_conjs` | Split ∧ recursively | `split_conjs`, `split_conjs at h` |

### Lean builtins (commonly used)
| Tactic | Use for |
|---|---|
| `agrind` | General automation (prefer over `grind` — faster) |
| `grind` | General automation (slower but more powerful — try if `agrind` fails) |
| `simp [*]` | Simplification with all hypotheses |
| `tauto` | Propositional tautologies |
| `decide` | Concrete finite computations |

### ⛔ BANNED TACTICS — NEVER USE THESE

**`omega`, `linarith`, `nlinarith` are BANNED in all Aeneas proofs.** This is the single
most important rule for writing idiomatic Aeneas proofs. These tactics do not understand
Aeneas scalar types (U8, U16, U32, U64, U128, Usize, I8, ..., Isize), do not know their
bounds (e.g., `U32.max`), do not understand `Slice.length`, `Vec.length`, or any Aeneas
container. They will either fail silently or produce fragile proofs that break on model changes.

| Banned tactic | Why it fails | Use instead (in preference order) |
|---|---|---|
| `omega` | Cannot reason about `.val`, `.bv`, scalar bounds, list/slice lengths | `agrind` > `grind` > `scalar_tac` |
| `linarith` | Same: no knowledge of scalar types, no `.val` reasoning | `agrind` > `grind` > `scalar_tac` |
| `nlinarith` | Same, plus explosion risk on nonlinear goals | `agrind` > `grind` > `scalar_tac +nonLin` or `simp_scalar` |

**Preference order for replacements: `agrind` first, then `grind`, then `scalar_tac`.**
`agrind` is fast and handles most goals. `grind` is slower but more powerful. `scalar_tac`
is specialized for arithmetic bounds and should be used when the goal is purely arithmetic.

**This applies everywhere:** in `step` theorem proofs, in helper lemmas, in `have` steps,
in `termination_by`/`decreasing_by` blocks, in `calc` chains — everywhere, including pure
`Nat` arithmetic in `decreasing_by` clauses. There are **no exceptions**.

**If you see a proof using these banned tactics, it must be rewritten.** Replace:
- `omega` → `agrind` (or `grind`, or `scalar_tac`)
- `linarith` → `agrind` (or `grind`, or `scalar_tac`)
- `nlinarith` → `agrind` (or `grind`, or `scalar_tac +nonLin`, or `simp_scalar`)

### Bitwise reasoning: `bv_tac` and `bvify`

**Always use `bv_tac N` for goals involving bitwise operations** (`&&&`, `|||`, `^^^`, `~~~`, `>>>`, `<<<`, `%` on bounded types). The `N` is the bit width (e.g., `bv_tac 8` for U8, `bv_tac 16` for U16).

**How `bv_tac N` works internally:**
1. **`bvify N`** — rewrites the goal to work over `BitVec N` by applying `@[bvify_simps]` lemmas (e.g., `(x &&& y).bv = x.bv &&& y.bv`, `(x ^^^ y).bv = x.bv ^^^ y.bv`)
2. **`bv_decide`** — decides the resulting BitVec goal via SAT solving

**Diagnosing `bv_tac` failures:** If `bv_tac` fails with a goal that contains non-decomposed expressions (e.g., `(x &&& y).bv` instead of `x.bv &&& y.bv`, or `(someOp x).val` not reduced), it means the `bvify` preprocessing step is stuck because a `@[bvify_simps]` lemma is missing. In that case:
- Identify the non-decomposed subexpression in the error
- Add the missing `@[bvify_simps]` simp lemma to the Aeneas standard library
- Then retry `bv_tac`

**Common identity lemmas** (already in Aeneas, marked `@[simp]`):
- `U8.and_allOnes`: `x &&& 255#u8 = x`, `U16.and_allOnes`: `x &&& 65535#u16 = x`, etc.
- `U8.val_and_max`: `x.val &&& 255 = x.val`, etc.
- `U8.bv_mod_size`: `x.bv % 256#8 = x.bv`, etc.
- `U8.val_mod_size`: `x.val % 256 = x.val`, etc.

## Key Patterns

### Pattern 1: Simple function spec
```lean
@[step]
theorem add_overflow.spec (a b : U32) (h : a.val + b.val ≤ U32.max) :
  add_overflow a b ⦃ c => c.val = a.val + b.val ⦄ := by
  unfold add_overflow
  step
```

### Pattern 2: Recursive function with case split
```lean
@[step]
theorem list_len.spec {T : Type} (l : CList T) :
  list_len l ⦃ n => n.val = l.toList.length ⦄ := by
  unfold list_len list_len_loop
  split
  · step as ⟨ n ⟩   -- Cons case
    simp [*]
  · simp_all              -- Nil case
```

### Pattern 3: Function with backward continuation
```lean
@[step]
theorem list_nth_mut.spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.toList.length) :
  list_nth_mut l i ⦃ x back =>
    x = l.toList[i.val]! ∧
    ∀ x', (back x').toList = l.toList.set i.val x' ⦄ := by
  unfold list_nth_mut list_nth_mut_loop
  step*
  simp_all
```

### Loop Translation: Prefer `-loops-to-rec`

Aeneas supports two loop translation modes:
- **`-loops-to-rec`** (recommended): Translates loops to recursive Lean functions. This is the mode used for most verified proofs so far. The resulting code uses direct recursion with `termination_by` / `decreasing_by`, and proofs use `unfold` + `step` (Pattern 4 below).
- **Fixed-point combinator** (default): Translates loops using a `loop` fixed-point operator. Proofs use `loop.spec_decr_nat` (Pattern 5 below). The proof infrastructure for this mode is less mature — fewer lemmas, less automation, and less battle-tested.

We are in the process of switching the default translation style to use the fixed-point combinator, but the proof infrastructure for it is not yet fully developed. Until it matures, **use `-loops-to-rec`** for any project where you need to write proofs.

### Pattern 4: Recursive loop (most common loop pattern)
```lean
-- Loops become _loop auxiliary functions. Write a separate theorem for each.
-- The loop invariant is both the precondition and postcondition.
@[step]
theorem zero_loop.spec (x : alloc.vec.Vec U32) (i : Usize) (h : i.val ≤ x.length) :
  zero_loop x i ⦃ x' =>
    x'.length = x.length ∧
    (∀ j, j < i.val → x'[j]! = x[j]!) ∧
    (∀ j, i.val ≤ j → j < x.length → x'[j]! = 0#u32) ⦄ := by
  unfold zero_loop
  simp; split
  · step ...    -- step applies zero_loop.spec recursively
  · simp; scalar_tac
termination_by x.length - i.val
decreasing_by scalar_decr_tac
```

### Pattern 5: Loop with `loop.spec_decr_nat` (fixed-point combinator)
```lean
-- Some loops use the `loop` combinator instead of direct recursion
@[step]
theorem my_loop.spec (x : MyState) (h : x.inv) :
  my_loop_body.loop x ⦃ r => r.post ⦄ := by
  apply loop.spec_decr_nat (measure := fun s => s.remaining) (inv := fun s => s.inv)
  · intro s hs
    unfold my_loop_body
    step*
    split_conjs <;> (try scalar_tac) <;> agrind
  · exact h
```

### Pattern 6: Bit-vector operation spec
```lean
@[step]
theorem bitwise_op.spec (x : U32) (h : x.val < 65536) :
  bitwise_op x ⦃ r => r.val = x.val % 256 ⦄ := by
  unfold bitwise_op
  step*
  bv_tac 32
```

### Pattern 7: Large function with fold decomposition
```lean
-- 1. Define helper
private def helper (a : U32) : Result U32 := do
  let b ← a + 1#u32; let c ← b * 2#u32; pure c

-- 2. Fold theorem
private theorem fold_helper (a : U32) (f : U32 → Result α) :
  (do let b ← a + 1#u32; let c ← b * 2#u32; f c) =
  (do let c ← helper a; f c) := by
  simp only [helper, bind_assoc_eq, bind_tc_ok, pure]

-- 3. Helper spec
@[local step]
theorem helper.spec (a : U32) (h : a.val < 1000) :
  helper a ⦃ c => c.val = (a.val + 1) * 2 ⦄ := by ...

-- 4. Main proof uses simp only [fold_helper]
```

## Proof Style and Maintainability

### Address all warnings
Lean warnings are not optional — they indicate problems that must be fixed:
- **"This simp argument is unused"**: Remove the unused lemma from `simp only [...]`.
- **"Too many ids provided"**: Reduce binder count in `step as ⟨...⟩`.
- **"'...' tactic does nothing"** / **"'...' tactic is never executed"**: Remove the dead tactic.
- **"unused variable"**: Remove or prefix with `_`.
The only acceptable warning is `"declaration uses 'sorry'"` for remaining proof obligations.

### Spaces around binary operators in comments
Always put spaces around binary operators (`<`, `>`, `=`, `≤`, `≥`, `+`, `*`, etc.) in
comments and doc strings. Write `j < N`, not `j<N`. This avoids a VS Code highlighter bug
that misinterprets `<` as an HTML tag opening, causing broken syntax highlighting in the file.

### Avoid large `simp only` calls in implementation proofs
Do **not** leave big `simp only [lemma1, lemma2, ..., lemma20]` or `simp_all only [...]`
calls in proofs about the generated Rust code. The generated model can be unstable (names
change when Rust code is re-extracted), making such proofs hard to maintain. Prefer
`simp [*]`, `agrind`, or targeted rewrites.

**Exception:** Large `simp only` calls are fine in proofs about auxiliary specifications
(pure mathematical lemmas), where the definitions are stable.

### Extract auxiliary lemmas for complex sub-proofs
When a proof step requires complex non-linear arithmetic, bitwise reasoning, or
multi-step calculation, **extract it as a separate auxiliary lemma** rather than
inlining it in the middle of a `step*` proof. This:
- Gives the sub-proof its own small context (faster, less noise)
- Keeps the main proof clean and readable
- Makes maintenance easier when the model changes

```lean
-- BAD: complex arithmetic inlined in the middle of step*
theorem main.spec ... := by
  unfold main_fn
  step*
  -- 15 lines of manual arithmetic here
  step*

-- GOOD: extract as auxiliary lemma
private theorem aux_arith (a b : Nat) (h1 : ...) (h2 : ...) :
  a * b % q = ... := by
  simp_scalar
  ...

theorem main.spec ... := by
  unfold main_fn
  step*
  · apply aux_arith ...
  step*
```

### Structuring non-linear arithmetic proofs

### Avoid early case splits on parameters in step proofs
In cryptographic code, functions are often parameterized by a parameter set (e.g.,
`p : Spec.Frodo.parameterSet` in FrodoKEM) from which lengths, dimensions, and bounds
are derived. **Do NOT case-split on such parameters at the beginning of a `step` proof.**
This duplicates the entire proof for each parameter variant (3× for FrodoKEM) and makes
the proof unmaintainable.

Instead:
- **Do case splits locally** inside specific proof obligations that need concrete values:
  ```lean
  -- BAD: duplicates the entire proof 3 times
  theorem my_fn.spec (p : Spec.Frodo.parameterSet) ... := by
    cases p <;> (unfold my_fn; step*; ...)

  -- GOOD: case split only where needed
  theorem my_fn.spec (p : Spec.Frodo.parameterSet) ... := by
    unfold my_fn
    step*
    · cases p <;> simp_all [Spec.Frodo.n, NBAR] <;> scalar_tac  -- only this sub-goal needs it
    step*
  ```

- **Give definitions/lemmas to `agrind`/`grind`** so they can case-split automatically:
  ```lean
  -- Give agrind the parameter definition so it can case-split internally
  attribute [local agrind] Spec.Frodo.n Spec.Frodo.nbar in
  theorem my_fn.spec ... := by
    unfold my_fn
    step*  -- agrind (used by step for preconditions) now auto-splits on p
  ```
  This is especially effective because `agrind` is the default tactic used by `step`
  to discharge preconditions — giving it the right definitions lets it handle parameter-
  dependent bounds without any manual case splits.

- **Write auxiliary lemmas** for arithmetic facts that depend on the parameter:
  ```lean
  private lemma n_mul_nbar_bound (p : Spec.Frodo.parameterSet) :
      Spec.Frodo.n p * Spec.Frodo.nbar < 2^16 := by
    cases p <;> native_decide
  ```

When proving non-linear arithmetic goals (with modulo, division, shifts, etc.) that
require multiple steps:

1. **Decompose into a chain of `have` steps**, each provable by `simp_scalar`:
```lean
have h1 : a * b < 2^32 := by simp_scalar
have h2 : (a * b) / q < q := by simp_scalar
have h3 : (a * b) % q = a * b - q * ((a * b) / q) := by simp_scalar
simp only [h3]; simp_scalar
```

2. **Or use `calc`** for equational chains:
```lean
calc a * b % (2^16)
    _ = a * b % (2^16) := rfl
    _ = (a * b) - (2^16) * ((a * b) / 2^16) := by simp_scalar
    _ = ... := by simp_scalar
```

3. **Use `ring`** in `have`/`calc` steps for purely algebraic equalities (no
   inequalities, no modulo, no division — just `+`, `*`, `-` rearrangements):
```lean
have h : (a + b) * c = a * c + b * c := by ring
calc (x + 1) * (x + 1)
    _ = x * x + 2 * x + 1 := by ring
```

4. **If `simp_scalar` can't close a step**: either provide more lemmas
   (`simp_scalar [my_lemma]`), mark lemmas for simp_scalar
   (`attribute [local simp_scalar_simps] my_lemma`), or apply the relevant
   theorem manually. If no suitable theorem exists, prove it as an auxiliary lemma.

4. **Always simplify shifts to modulo/division**: rewrite `x >>> n` as `x / 2^n`
   and `x <<< n` as `x * 2^n` (or `x % 2^n` for the relevant bits). Use
   `Nat.shiftRight_eq_div_pow` and `Nat.shiftLeft_eq_mul_pow` or the corresponding
   scalar lemmas.

## Critical Pitfalls

1. **Termination error after unfold + step**: Function starts with match/if → use `split` first
2. **Nat subtraction truncated**: `3 - 5 = 0` in Nat → use Int, add preconditions, or rewrite as addition (`z + y = x` instead of `z = x - y`)
3. **`simp_all` removes hypotheses**: Use `simp [*]` or `simp [h1, h2]` instead
4. **`agrind` fails**: Try `simp [*]; agrind`
5. **`grind` explodes**: Use `agrind` instead (controlled context)
6. **Progress applies wrong spec**: Use `step with specific_theorem`
7. **"Too many ids provided" from `step`**: You gave more binder names in `step as ⟨...⟩` than the tactic produced. Remove excess names until the count matches. Check `goal` to see how many binders the postcondition actually has.
8. **"This simp argument is unused"**: A lemma in `simp only [...]` or `simp_all only [...]` didn't fire. **Always fix this** — remove the unused lemma from the list. Don't ignore these warnings.
9. **"'...' tactic does nothing"** / **"'...' tactic is never executed"**: The tactic call is dead code. **Always fix this** — remove the tactic entirely. Don't leave dead tactics in proofs.
10. **NEVER unfold Aeneas stdlib definitions in a proof.** When in the middle of a proof, you should never need to unfold definitions from `Aeneas.Std` (Slice, Array, UScalar, IScalar, iterator types, core.*, etc.). If you feel the need to unfold:
   - **Stop.** This is a sign that a lemma is missing.
   - **Search** the Aeneas library for an existing lemma (grep for related names, check simp/step attributes).
   - **If it doesn't exist:** state and prove the missing lemma yourself, then use it in the proof.
   - **This principle extends to all auxiliary definitions**, including project-local ones. When in the middle of a big proof, you should not have to unfold many auxiliary definitions. If you find yourself unfolding too many, step back and introduce auxiliary lemmas to bridge the gap.
11. **NEVER increase `maxRecDepth`.** If you hit a `maxRecDepth` error, it signals a real problem — either the proof is poorly structured (causing unbounded unfolding), or there is a bug in a tactic. For tactics that internally use `simp` (like `agrind`, `grind`, `scalar_tac`, `simp_scalar`), check whether hypotheses in the goal trigger a simp loop — if so, `clear` the offending hypothesis or use `simp only [...]`. If it's not a simp loop, **report the issue to the user** as a possible tactic bug.
12. **Report misbehaving tactics.** If a tactic doesn't do what it should — for example, `progress` fails to make progress even though the appropriate `@[progress]` lemma exists, or `scalar_tac` can't close a pure arithmetic goal it should handle — **report this to the user**. It may indicate a bug or missing feature worth fixing upstream.

## Attribute Management

```lean
-- File-level setup for crypto/array proofs
#setup_aeneas_simps

-- Register lemmas for tactics
attribute [local simp_scalar_simps] my_lemma
attribute [local simp_lists_simps] my_lemma
attribute [local agrind] my_lemma
```

Safe to activate many local lemmas for `simp_scalar`/`simp_lists` — simp-based, no complexity explosion.
