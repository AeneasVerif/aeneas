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

### When to use:

- Function body has >10 monadic steps
- Contains repeated sub-patterns (e.g., Montgomery reduction appears multiple times)
- Proof is timing out or unmanageable

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

## Anti-Patterns to Avoid

- ❌ Trying to prove NIST spec ↔ Aeneas code in one theorem (too big a gap)
- ❌ No intermediate auxiliary spec
- ❌ Monolithic proofs without helper lemmas
- ❌ Using `grind` where `agrind` suffices (explosion risk)
- ❌ Not decomposing large functions
