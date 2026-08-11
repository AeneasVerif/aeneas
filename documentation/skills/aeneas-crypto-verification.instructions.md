---
name: aeneas-crypto-verification
description: Crypto-specific proof strategies including Montgomery, NTT, modular arithmetic, and bit-vectors for Aeneas Lean proofs
---

# Aeneas Crypto Verification Skill File

## Context

This skill file covers strategies for verifying cryptographic Rust code translated by Aeneas to Lean. Techniques drawn from real-world cryptographic verification projects.

**PREREQUISITE:** Always use the lean-lsp-mcp tools for interactive proof development. See the `lean-lsp-mcp` skill file.

## File Setup Template

```lean
import Aeneas
import MyProject.Code
import MyProject.Spec
import MyProject.Properties.Basic

open Aeneas Std Result

#setup_aeneas_simps

-- Simpler cast spec when values fit in target type
attribute [-step] UScalar.cast.step_spec
attribute [local step] UScalar.cast_inBounds_spec

-- Register crypto constants for all tactics
@[simp, scalar_tac_simps, bvify_simps, agrind =]
theorem Q_val : Q.val = 3329 := by decide
```

## The Multi-Level Verification Pipeline

```
NIST spec ⟷₁ Lean spec ⟷₂ Auxiliary spec ⟷₃ Aeneas code
```

### When to introduce each level:

- **Always have:** NIST spec (pure math) + Aeneas code (auto-generated)
- **Add auxiliary spec when:** The code structure differs significantly from the mathematical spec (loops vs. closed-form, array indexing vs. polynomial operations, bit-packing vs. abstract operations)
- **For loops:** Use `loop.spec_decr_nat` with a loop invariant and a `Nat` termination measure (or `loop.spec` for general well-founded measures)
- **Specs are always pure:** They may use monadic notation (Id monad) but never the Result monad
- **The auxiliary spec:** Also pure, closely follows code structure

### Proving equivalences:

- Prove each `⟷` separately — each gap is small
- Name convention: `spec_aux` for code↔aux, `spec` for full specification
- Use `step_spec_aux` for code↔auxiliary spec properties, `step_spec` for full spec with invariants

### Spec adequacy: direct equality, not relational

<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Postcondition quality" -->

Every `@[step]` theorem must have a **direct equality** postcondition:
`repr(output) = Spec.algorithmName(repr(input1), repr(input2), ...)`.
Relational specs and structural-only specs are not acceptable.
See aeneas-lean-core "Postcondition quality" for full rules, examples, and the
vacuity test.

### Template:

```lean
/-!
`Nist spec ⟷₁ Lean spec ⟷₂ Auxiliary spec ⟷₃ Aeneas translation`
  - `Nist spec`: [reference to standard section]
  - `Lean spec`: [Lean definition name] (always pure — may use Id monad notation, never Result)
  - `Auxiliary spec`: [Lean definition name] (also pure)
  - `Aeneas translation`: [generated function name] (lives in Result monad)
-/
```

## Function Decomposition

### Phase analysis (mandatory — do BEFORE attempting any proof)

Phase analysis and fold decomposition are **MANDATORY** before writing any proof
for a function body with >10 monadic steps. Do NOT attempt a direct proof
and then decompose after it fails — analyze and decompose first.

**Analyze the body** and identify distinct **algorithmic phases**. An algorithmic
phase is a contiguous sequence of monadic steps that implements a recognizable
high-level operation with a concise specification. Examples:

- **Montgomery reduction**: multiply, mask, multiply-add, shift →
  spec: `a1 ≡ a · R⁻¹ (mod Q)` with bound `a1 < 2Q`
- **Modular addition/subtraction**: add/sub with conditional correction →
  spec: `c ≡ a + b (mod Q)` with bound `c < Q`
- **Constant-time range reduction**: wrapping subtract, arithmetic shift,
  mask-and-add (possibly repeated) → spec: `result = input % Q` with `result < Q`
- **Repeated array load + type cast**: when the same array-index-then-cast
  pattern appears multiple times, factor it into a single fold helper

### Signals that a phase needs its own fold helper

A phase MUST be extracted into a fold helper when it contains any of:
- Bitwise operations (AND, OR, XOR, shifts) — these need `bv_tac` or `bvify`
- Non-linear arithmetic (multiply-then-shift, multiply-then-mask)
- Wrapping arithmetic (`wrapping_add`, `wrapping_sub`, `wrapping_mul`)
- Signed↔unsigned casts (`IScalar.hcast`, `UScalar.hcast`)
- Any combination that produces bounds requiring `native_decide` or exhaustive
  case analysis

When none of these signals are present (e.g., a single array index), the phase can stay
inline, though it is recommended to introduce an auxiliary function for any phase with > 5
lines of code.

### Decomposition workflow

1. **Identify phases**: Read the function body, draw phase boundaries
2. **Search for existing lemmas**: Before writing any helper spec, search:
   - `Properties/Ntt/MontReduction.lean` for `mont_reduce_spec`
   - `Properties/Ntt/ModArith.lean` for modular arithmetic helpers
   - `Properties/Basic.lean` for array/polynomial conversion lemmas
   - Aeneas stdlib for `wrapping_*_val_eq` lemmas
   If an existing lemma covers the phase, use it — do not reprove the same
   mathematical property from scratch.
3. **Create fold helpers**: For each complex phase, extract:
   - A `private def` copying the monadic steps
   - A fold theorem proving `(do <inline>; f result) = (do let r ← helper; f r)`
   - A `@[local step]` spec theorem with focused pre/postconditions
4. **Factor bounds into helper lemmas**: When the same bounds derivation
   (e.g., "given `a ≤ B`, derive `a1 ≤ B'`") appears in multiple goals,
   extract it as a standalone `private theorem`. Keep the main proof clean.
5. **Assemble**: In the main proof, `simp only [fold_phase1, fold_phase2, ...]`
   then `step*`. Remaining goals should be manageable and each closeable in
   1–3 lines with focused `·` blocks.

### Template:

```lean
-- 1. Extract helper
private def helper_name (a : U32) (b : Slice U16) : Result U32 := do
  -- copy the relevant subsequence of monadic operations
  ...

-- 2. Fold theorem (proves inline = helper call)
private theorem fold_helper_name (a : U32) (b : Slice U16) (f : U32 → Result α) :
  (do /- ...inline operations... -/ f result) =
  (do let r ← helper_name a b; f r)
  := by simp only [helper_name, bind_assoc_eq, bind_tc_ok, pure]

-- 3. Helper spec
@[local step]
theorem helper_name_spec (a : U32) (b : Slice U16) (hpre : a.val < b.length) :
  helper_name a b ⦃ r => postcondition r ⦄ := by ...

-- 4. In main proof:
--    simp only [fold_helper_name, fold_other_helper]
--    step*  -- now uses helper specs
```

## Modular Arithmetic Decision Tree

```
Goal involves modular equivalence (a ≡ b [MOD n])?
  ├─ YES → Use zmodify to lift to ZMod (a ring — enables ring tactic)
  │        Then: ring, simp, or algebraic reasoning
  │        Example: zmodify at h; simp [Int.mul_emod]
  │
  └─ NO → Goal involves bounds (a < n, 0 ≤ a)?
           ├─ YES → Stay in Nat/Int
           │        Use: agrind, grind, scalar_tac / scalar_tac +nonLin
           │
           └─ NO → Mixed? Split into separate goals
                    split_conjs
                    · zmodify; ...   -- modular part
                    · scalar_tac     -- bounds part
```

### Montgomery/Barrett reduction pattern:

```lean
-- Prove modular equivalence in ZMod
have hMod : (result.val : ZMod q) = (input.val : ZMod q) * montgomery_factor := by
  have ⟨ hMont, _ ⟩ := mont_reduce_spec q R R_inv input.val ...
  zify at h_intermediate_eq
  zify
  simp [h_intermediate_eq, hMont, Int.mul_emod]

-- Prove bounds in Nat/Int
have hBounds : result.val ≤ bound := by
  have hB := bounds_lemma input.val (by scalar_tac)
  zify at h_intermediate_eq
  scalar_tac
```

## Bit-Vector Reasoning Decision Tree

```
Goal involves bitwise ops (AND, OR, XOR, shifts)?
  ├─ Direct bv goal → bv_tac N
  │
  ├─ Nat/Int goal about bitwise result?
  │   ├─ Can bvify lift it? → bvify N; bv_tac N
  │   │
  │   └─ bvify can't lift? → Reverse trick (two cases):
  │       Case 1 (goal): have h : (bv_prop) := by bv_tac N; natify at h; simp_scalar at h; exact h
  │       Case 2 (hyp):  have h : (bv_prop) := by natify; simp [original_hyp]
  │
  └─ Need to prove scalar bounds after bitwise op?
      → Use bv_tac for the bitwise part,
        then agrind/scalar_tac for bounds
```

## Array/Polynomial Proof Patterns

### Setup for inhabited types:

```lean
#setup_aeneas_simps  -- enables getElem!/set! patterns
```

### Array access reasoning:

```lean
-- Automatic (try first)
agrind

-- Manual fallback (if agrind too slow)
cases h_idx <;> simp_lists [*]
```

### Polynomial-to-array correspondence:

```lean
-- Define conversion using map (not ofFn)
def to_poly (arr : Array U32 256) : Spec.Polynomial :=
  arr.map (fun x => (x.val : ZMod q))

-- Prove element-wise correspondence
theorem to_poly_getElem (arr : Array U32 256) (i : Fin 256) :
  (to_poly arr)[i] = (arr[i].val : ZMod q) := by simp [to_poly]
```

## Crypto Proof Spec Template

```lean
@[local step]  -- or @[step] if used globally
theorem crypto_operation_spec
  (input : U32)
  (h_bounds : input.val ≤ INPUT_BOUND)
  :
  crypto_operation input ⦃ result =>
    -- Bounds on result
    result.val ≤ OUTPUT_BOUND ∧
    -- Functional correctness (modular equivalence)
    (result.val : ZMod q) = spec_function (input.val : ZMod q) ⦄
  := by
  unfold crypto_operation
  -- Apply monadic step specs, then handle sub-goals individually
  step*
  · bv_tac 32     -- bitwise sub-goal 1
  · bv_tac 32     -- bitwise sub-goal 2
  -- Split bounds vs modular goals
  split_conjs
  · -- Bounds: stay in Nat/Int
    scalar_tac
  · -- Modular equivalence: lift to ZMod
    zmodify
    simp [*]
```

## Performance Checklist

1. ☐ Decompose functions with >10 monadic steps (fold theorems)
2. ☐ Use `agrind` not `grind`
3. ☐ Split modular/bounds goals before proving
4. ☐ Register constants for all tactics (`@[simp, scalar_tac_simps, bvify_simps, agrind =]`)
5. ☐ Monitor proof times — decompose if slow
6. ☐ Shorten proofs after completion
7. ☐ Use `step*?` to find automation opportunities

## Axiomatizing SIMD/Intrinsic Operations

When verifying code that uses SIMD intrinsics (SSE2/AVX, NEON, etc.) or assembly
wrappers, the operations cannot be translated by Aeneas and must be axiomatized.

### Reference-driven axiomatization

**Always look up the vendor reference documentation** (Intel Intrinsics Guide, ARM
NEON Reference, AMD manuals, etc.) for the precise semantics of each intrinsic. Use
the reference semantics — not guesses or reverse engineering — to formalize the axiom.

- **If the reference provides an executable pseudocode/spec**, formalize it as a Lean
  `def` (the model) and state the axiom as: intrinsic result equals the model applied
  to the inputs. If the reference pseudocode is short (< 25 lines), include it in the
  docstring for easy cross-checking. Follow the same rules as formalizing cryptographic
  specifications (see the `formalizing-crypto-specs` skill file).
- **If no executable spec is available**, an axiomatized step theorem with a precise
  postcondition is acceptable — but the postcondition must capture the full semantics,
  not just partial properties.
- **If no reference document could be found** for a specific intrinsic, report this
  to the user. Do not guess the semantics.

### Documentation requirements

Every SIMD axiom must include a docstring that:
1. **Names the intrinsic** (e.g., `_mm_add_epi16`, `vaddq_u16`)
2. **Links to the reference** (URL to Intel Intrinsics Guide, ARM docs, etc.)
3. **Quotes or summarizes the operation** from the reference (e.g., "Adds packed
   16-bit integers in `a` and `b`")

```lean
/-- **Axiom for `_mm_add_epi16` (SSE2)**
Adds packed 16-bit signed integers in `a` and `b`.
Ref: https://www.intel.com/content/www/us/en/docs/intrinsics-guide/...
Operation: `FOR j := 0 to 7: dst[j] := a[j] + b[j]` -/
axiom vec128_add_spec (a b : XmmVec128) : ...
```

### SIMD lemma library

When axiomatizing SIMD operations, build a **complete lemma library** for reasoning
about the vector type. If a lemma is needed for one operation (e.g., element access
for addition), equivalent lemmas are typically needed for related operations
(subtraction, multiplication, shifts, etc.). The library should cover:

- Element access (`v.val[i]!` for each lane)
- Conversion between the vector type and arrays/lists
- Well-formedness propagation (e.g., `wfVec` preservation through operations)
- Commutativity, associativity, and other algebraic properties where applicable

Aim for completeness: a missing lemma in the SIMD library often blocks proofs in
unrelated parts of the codebase.

## Anti-Patterns to Avoid

- ❌ Trying to prove NIST spec ↔ Aeneas code in one theorem (too big a gap)
- ❌ No intermediate auxiliary spec
- ❌ Monolithic proofs without helper lemmas
- ❌ Using `grind` where `agrind` suffices (explosion risk)
- ❌ Not decomposing large functions
- ❌ SIMD axioms without reference documentation links
- ❌ SIMD axioms that only assert partial properties (e.g., length but not values)

## `congr` WHNF Explosion on Crypto Functions

Crypto spec functions (sampling, encoding, transforms) typically contain loops
iterated hundreds of times, recursive helpers, and dependent-type parameters.
This makes them especially vulnerable to the `congr` WHNF explosion described
in the `aeneas-lean-core` skill file (Pitfall #29): `congr N` uses default
transparency, and when arguments don't match definitionally it WHNF-reduces
the function body — causing deterministic timeout on these large functions.

**Always use `fcongr N`** (reducible transparency — never unfolds function bodies).

In crypto proofs, the typical trigger is `step*`-generated cast variables
(e.g., `i : U32`, `i_post : ↑i = n`) that make arguments propositionally but
not definitionally equal — enough for `congr` to attempt WHNF.

```lean
-- Goal: specFn V₁ = specFn V₂
-- (V₁ and V₂ have propositionally-equal but not definitionally-equal types)

-- BAD: congr tries to WHNF specFn's loop body → timeout
congr 1

-- GOOD: fcongr decomposes without unfolding
fcongr 1
· ...  -- argument equalities (may use HEq if types differ)
```

If `fcongr 1` produces `HEq` subgoals and you prefer plain `Eq`, try rewriting
the cast variable away first:
```lean
simp only [i_post] at h ⊢  -- may fail with "motive not type correct"
-- If simp fails, use fcongr and handle HEq
```
