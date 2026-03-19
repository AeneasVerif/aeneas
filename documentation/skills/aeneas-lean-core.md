# Aeneas + Lean Core Skill File

## Context
Aeneas translates Rust programs to pure Lean code via the LLBC intermediate representation. The generated code uses the `Result` error monad. Proofs verify functional correctness by writing specification theorems tagged with `@[progress]`.

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

## The Specification Pattern

### Template
```lean
@[progress]
theorem function_name_spec (params : Types) (preconditions : hypotheses) :
  function_name params ⦃ result => postcondition result ⦄ := by
  unfold function_name
  progress  -- or progress* for automation
  -- finish remaining goals
```

### With backward function
```lean
@[progress]
theorem function_name_spec (params...) (preconditions...) :
  function_name params ⦃ result back =>
    postcondition_on_result ∧
    postcondition_on_backward_function back ⦄ := by ...
```

### The `⦃ ⦄` notation
Weakest precondition: `f ⦃ x => P x ⦄` means "if f succeeds with value x, then P x holds."

## Proof Development Workflow

### Decision tree for starting a proof:

1. Does the function start with `match`/`if`?
   - YES → `unfold fn; split` then `progress` per branch
   - NO → `unfold fn; progress`

2. Is the function simple (few monadic steps)?
   - YES → `unfold fn; progress*` may complete it
   - NO → Use `progress*?` to generate script, then optimize

3. Is the function large/complex?
   - YES → Decompose with fold theorems (see Function Decomposition)
   - NO → Direct proof

### The progress*? → automate → refold workflow:
1. `progress*?` — generates expanded proof script
2. Review script, identify hard sub-goals
3. Register lemmas: `attribute [local agrind] my_lemma`
4. Re-run `progress*` — now handles more automatically
5. Repeat until compact

## Tactic Quick Reference

### Primary tactics (Aeneas-specific)
| Tactic | Use for | Syntax |
|---|---|---|
| `progress` | Apply function spec | `progress`, `progress as ⟨x, h⟩`, `progress with thm` |
| `progress*` | Repeated progress | `progress*` |
| `progress*?` | Generate proof script | `progress*?` |
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
| `agrind` | General automation (PREFER over `grind`) |
| `omega` | Linear Nat/Int arithmetic |
| `simp [*]` | Simplification with all hypotheses |
| `tauto` | Propositional tautologies |
| `decide` | Concrete finite computations |

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
@[progress]
theorem add_overflow_spec (a b : U32) (h : a.val + b.val ≤ U32.max) :
  add_overflow a b ⦃ c => c.val = a.val + b.val ⦄ := by
  unfold add_overflow
  progress
```

### Pattern 2: Recursive function with case split
```lean
@[progress]
theorem list_len_spec {T : Type} (l : CList T) :
  list_len l ⦃ n => n.val = l.toList.length ⦄ := by
  unfold list_len list_len_loop
  split
  · progress as ⟨ n ⟩   -- Cons case
    simp [*]
  · simp_all              -- Nil case
```

### Pattern 3: Function with backward continuation
```lean
@[progress]
theorem list_nth_mut_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.toList.length) :
  list_nth_mut l i ⦃ x back =>
    x = l.toList[i.val]! ∧
    ∀ x', (back x').toList = l.toList.set i.val x' ⦄ := by
  unfold list_nth_mut list_nth_mut_loop
  progress*
  simp_all
```

### Loop Translation: Prefer `-loops-to-rec`

Aeneas supports two loop translation modes:
- **`-loops-to-rec`** (recommended): Translates loops to recursive Lean functions. This is the mode used for most verified proofs so far. The resulting code uses direct recursion with `termination_by` / `decreasing_by`, and proofs use `unfold` + `progress` (Pattern 4 below).
- **Fixed-point combinator** (default): Translates loops using a `loop` fixed-point operator. Proofs use `loop.spec_decr_nat` (Pattern 5 below). The proof infrastructure for this mode is less mature — fewer lemmas, less automation, and less battle-tested.

We are in the process of switching the default translation style to use the fixed-point combinator, but the proof infrastructure for it is not yet fully developed. Until it matures, **use `-loops-to-rec`** for any project where you need to write proofs.

### Pattern 4: Recursive loop (most common loop pattern)
```lean
-- Loops become _loop auxiliary functions. Write a separate theorem for each.
-- The loop invariant is both the precondition and postcondition.
@[progress]
theorem zero_loop_spec (x : alloc.vec.Vec U32) (i : Usize) (h : i.val ≤ x.length) :
  zero_loop x i ⦃ x' =>
    x'.length = x.length ∧
    (∀ j, j < i.val → x'[j]! = x[j]!) ∧
    (∀ j, i.val ≤ j → j < x.length → x'[j]! = 0#u32) ⦄ := by
  unfold zero_loop
  simp; split
  · progress ...    -- progress applies zero_loop_spec recursively
  · simp; scalar_tac
termination_by x.length - i.val
decreasing_by scalar_decr_tac
```

### Pattern 5: Loop with `loop.spec_decr_nat` (fixed-point combinator)
```lean
-- Some loops use the `loop` combinator instead of direct recursion
@[progress]
theorem my_loop_spec (x : MyState) (h : x.inv) :
  my_loop_body.loop x ⦃ r => r.post ⦄ := by
  apply loop.spec_decr_nat (measure := fun s => s.remaining) (inv := fun s => s.inv)
  · intro s hs
    unfold my_loop_body
    progress*
    split_conjs <;> (try scalar_tac) <;> agrind
  · exact h
```

### Pattern 6: Bit-vector operation spec
```lean
-- Optional: swap to bv specs (bv_tac/bvify are efficient without this)
attribute [-progress] U32.add_spec
attribute [local progress] U32.add_bv_spec

@[progress]
theorem bitwise_op_spec (x : U32) (h : x.val < 65536) :
  bitwise_op x ⦃ r => r.val = x.val % 256 ⦄ := by
  unfold bitwise_op
  progress*
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
@[local progress]
theorem helper_spec (a : U32) (h : a.val < 1000) :
  helper a ⦃ c => c.val = (a.val + 1) * 2 ⦄ := by ...

-- 4. Main proof uses simp only [fold_helper]
```

## Critical Pitfalls

1. **Termination error after unfold + progress**: Function starts with match/if → use `split` first
2. **Nat subtraction truncated**: `3 - 5 = 0` in Nat → use Int, add preconditions, or rewrite as addition (`z + y = x` instead of `z = x - y`)
3. **`simp_all` removes hypotheses**: Use `simp [*]` or `simp [h1, h2]` instead
4. **`agrind` fails**: Try `simp [*]; agrind`
5. **`grind` explodes**: Use `agrind` instead (controlled context)
6. **Progress applies wrong spec**: Use `progress with specific_theorem`
7. **NEVER unfold Aeneas stdlib definitions in a proof.** When in the middle of a proof, you should never need to unfold definitions from `Aeneas.Std` (Slice, Array, UScalar, IScalar, iterator types, core.*, etc.). If you feel the need to unfold:
   - **Stop.** This is a sign that a lemma is missing.
   - **Search** the Aeneas library for an existing lemma (grep for related names, check simp/progress attributes).
   - **If it doesn't exist:** state and prove the missing lemma yourself, then use it in the proof.
   - **This principle extends to all auxiliary definitions**, including project-local ones. When in the middle of a big proof, you should not have to unfold many auxiliary definitions. If you find yourself unfolding too many, step back and introduce auxiliary lemmas to bridge the gap.

## Attribute Management

```lean
-- File-level setup for crypto/array proofs
#setup_aeneas_simps

-- Optional: swap specs (bv_tac/bvify are efficient without this)
attribute [-progress] U32.add_spec
attribute [local progress] U32.add_bv_spec

-- Register lemmas for tactics
attribute [local simp_scalar_simps] my_lemma
attribute [local simp_lists_simps] my_lemma
attribute [local agrind] my_lemma
```

Safe to activate many local lemmas for `simp_scalar`/`simp_lists` — simp-based, no complexity explosion.
