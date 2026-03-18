# Verifying Cryptographic Code with Aeneas and Lean

## Overview

This guide presents strategies and techniques for verifying cryptographic code with Aeneas and Lean. The techniques are drawn from the SymCrypt verification project, which verifies ML-KEM (NIST FIPS 203, also known as Kyber) — a post-quantum key encapsulation mechanism originally written in Rust as part of Microsoft's SymCrypt library.

Cryptographic code presents unique verification challenges:
- Heavy use of modular arithmetic (polynomial rings over ZMod q)
- Bit-level manipulations (shifts, masks, bitwise AND/OR)
- Fixed-size arrays accessed with computed indices
- Performance-critical code with complex inline computations
- Multi-level specifications (NIST standard → mathematical spec → implementation)

## The Multi-Level Verification Pipeline

The most important structural pattern for crypto verification is the multi-level pipeline:

```
Nist spec ⟷₁ Lean spec ⟷₂ Auxiliary spec ⟷₃ Aeneas translation
```

Each level has a specific role:

### Level 1: NIST Specification
The mathematical specification from the standard (e.g., FIPS 203). Written directly in Lean as pure mathematical definitions. Example: polynomials as `Vector (ZMod q) 256`, compress/decompress as mathematical functions.

### Level 2: Lean Specification
A direct Lean translation of the NIST spec. **Specifications are always pure** — they never live in the `Result` error monad. They may use monadic notation (via the `Id` monad) for readability, but semantically they are pure functions.

### Level 3: Auxiliary Specification (optional)
An intermediate specification that closely follows the implementation structure but remains pure. This is the key bridge between the mathematical spec and the Aeneas-generated code.

**Why this level exists:** The Aeneas translation follows the Rust code structure (loops, array indexing, bit-packing), which may differ significantly from the NIST spec. The auxiliary spec mirrors the code structure but in pure math, making the refinement proof tractable.

### Level 4: Aeneas Translation
The automatically generated Lean code from the Rust implementation. This code lives in the `Result` monad (it may fail on overflow, out-of-bounds, etc.).

### Proving equivalences between levels

Prove equivalences between adjacent levels separately. Each proof is simpler because the specs are structurally similar.

**Example from CompressEncode.lean:**
```lean
/-!
`Nist spec ⟷₁ Lean spec ⟷₂ Auxiliary spec ⟷₃ Aeneas translation`
  - `Nist spec` corresponds to (4.7) (Compress) and Algorithm 5 (ByteEncode).
  - `Lean spec` corresponds to `Symcrust.Spec.compress` and `Symcrust.Spec.byteEncode`
    (pure definitions — may use monadic notation via Id monad, but not Result).
  - `Auxiliary spec` corresponds to `Symcrust.SpecAux.compress` and `Stream.encode`.
  - `Aeneas translation` corresponds to `Symcrust.ntt.poly_element_compress_and_encode`.
  - `⟷₂` corresponds to `compress_eq` and `Stream.encode.spec`.
  - `⟷₃` corresponds to `Symcrust.SpecAux.poly_element_compress_and_encode.spec`.
-/
```

The proof is structured as:
- `compress_coeff.spec_aux` — low-level correctness (code → aux spec)
- `compress_coeff.spec` — full specification (code → Lean spec), using the aux result
- `encode_coefficient.progress_spec_aux` — encoding correctness with auxiliary spec
- `encode_coefficient.progress_spec` — full encoding specification with invariants

### CompressEncode: A Model for Proof Structure

The CompressEncode module in SymCrypt is a good model for well-structured proofs:

- Clear separation into `spec_aux` (auxiliary spec proof) and `spec` (full spec proof)
- Explicit documentation of the verification pipeline at the top of the file
- Clean layering: each theorem builds on the previous level
- Manageable proof sizes

**Lesson:** Always introduce intermediate specs and layer your proofs. Don't try to bridge the gap between the NIST spec and the Aeneas translation in a single theorem.

## Ntt.lean: A Key Reference

The file `Symcrust/Properties/Ntt/Ntt.lean` is one of the richest sources of proof techniques for crypto verification. It contains:
- Function decomposition patterns (fold theorems)
- Local attribute management for bit-vector specs
- Montgomery and Barrett reduction integration
- Complex array-based reasoning
- Proof of NTT (Number Theoretic Transform) correctness

## Function Decomposition for Tractability

Crypto implementations often have large functions with many sequential operations. Aeneas faithfully translates these, resulting in long monadic chains that are hard to verify directly.

**Solution:** Introduce private helper definitions on the Lean side that extract subsequences of operations.

**Pattern from Ntt.lean:**

Step 1 — Define a helper:
```lean
private def reduce_add_mont_reduce (a : U32) : Result U32 := do
  let i2 ← lift (core.num.U32.wrapping_mul a ntt.NEG_Q_INV_MOD_R)
  let inv ← lift (i2 &&& ntt.RMASK)
  let i3 ← inv * ntt.Q
  let i4 ← a + i3
  let a1 ← i4 >>> ntt.RLOG2
  pure a1
```

Step 2 — Prove a fold theorem:
```lean
private theorem fold_reduce_add_mont_reduce (a : U32) (f : U32 → Result α) :
  (do
    let i2 ← lift (core.num.U32.wrapping_mul a ntt.NEG_Q_INV_MOD_R)
    -- ... inline operations ...
    f a1) =
  (do
    let a1 ← reduce_add_mont_reduce a
    f a1)
  := by
  simp only [reduce_add_mont_reduce, bind_assoc_eq, bind_tc_ok, pure]
```

Step 3 — Prove specs for the helper:
```lean
@[local progress]
theorem reduce_add_mont_reduce_spec (a : U32) (h1 : a.val ≤ reduceAddInputBound) :
  reduce_add_mont_reduce a ⦃ a1 =>
    a1.val ≤ reduceAddStepBound ∧
    (a1.val : Spec.Zq) = (a.val : Spec.Zq) * 169 ⦄
  := by ...
```

Step 4 — In the main proof, use `simp only [fold_reduce_add_mont_reduce]` to replace inline code with the helper.

## Modular Arithmetic Strategy

Crypto code is fundamentally about modular arithmetic. The key strategy:

- **For modular equivalences** (e.g., `a ≡ b [MOD q]`): Use `zmodify` to lift to `ZMod`, then reason algebraically. ZMod is a ring, so the `ring` tactic and standard algebraic lemmas apply directly.
- **For bounds** (e.g., `0 ≤ a < q`): Stay in `Nat`/`Int` and use `scalar_tac`, `omega`.

**Example from Montgomery reduction (MontReduction.lean):**
```lean
-- Lifting to ZMod for modular reasoning
zmodify at h_q_minus_1
zmodify [t, f]

-- Staying in Int for bounds reasoning
scalar_tac +nonLin
```

**Example from Barrett reduction (BarrettReduction.lean):**
The Barrett reduction proof demonstrates multi-domain reasoning:
- Rational arithmetic (`ℚ`) for the mathematical analysis
- Integer arithmetic (`ℤ`) for the concrete bounds
- Natural numbers (`ℕ`) for the final result
Uses `field_simp` for rational arithmetic, `scalar_tac +nonLin` for nonlinear bounds.

## Bit-Vector Reasoning in Crypto

Crypto code is full of bitwise operations. Strategy:

### `bv_tac` and `bvify`
`bv_tac` (which uses `bvify` under the hood) is quite efficient and can often handle bit-vector goals directly without any special setup. It can be useful to swap to bit-vector specifications by activating/deactivating progress theorems, but it's not strictly necessary:
```lean
-- Optional: swap to bit-vector specs if you find it helps
attribute [-progress] U32.add_spec U32.mul_spec
attribute [local progress] U32.add_bv_spec U32.mul_bv_spec
```

### Common proof patterns
```lean
-- Direct bit-vector decision
have h : (some bv expression) = (expected) := by bv_tac 32

-- Lifting to bit-vectors then deciding
bvify 32
bv_tac 32

-- The reverse trick (two cases):
-- Case 1: can't lift goal to bv → prove bv equivalent, convert back to Nat
have h_bv : (bv_equivalent_of_goal) := by bv_tac 32
natify at h_bv
simp_scalar at h_bv   -- then use h_bv

-- Case 2: can't lift hypothesis to bv → write bv equivalent, prove via natify
have h_bv : (bv_equivalent_of_hyp) := by natify; simp [original_hyp]
```

### Registering constants for tactics
Make crypto constants available to all relevant tactics:
```lean
@[simp, scalar_tac_simps, bvify_simps, agrind =]
theorem Q_val : Q.val = 3329 := by decide

@[simp, scalar_tac_simps, bvify_simps, agrind =]
theorem NEG_Q_INV_MOD_R_val : NEG_Q_INV_MOD_R.val = 3327 := by decide
```

## Inhabited Types and `getElem!`

Crypto code often works with fixed-size arrays of known types (e.g., `Array U32 256`). These are always inhabited.

**Prefer `getElem!` over `getElem`** for array access in specifications:
- `getElem!` returns a default value for out-of-bounds (no index proof needed)
- Makes specifications cleaner and refinement proofs easier

**Setup:**
```lean
#setup_aeneas_simps
```
This deactivates lemmas that convert `getElem!` to `getElem?`/`getD`, and locally activates lemmas that convert `getElem` to `getElem!` and `set` to `set!`.

## List Reasoning for Crypto Arrays

When reasoning about array operations with `get` and `set`:

1. **First try `agrind`** — handles many get/set patterns automatically
2. **If too slow**, use `cases` on index comparisons, then `simp_lists`/`simp` for each case:
```lean
-- Try this first
agrind
-- Fallback if agrind is too slow
cases h_idx <;> simp_lists [*]
```

## Proof Patterns in Crypto

### Specification theorem with bounds and modular equivalence
```lean
@[local progress]
theorem reduce_add_mont_reduce_spec (a : U32) (h1 : a.val ≤ reduceAddInputBound) :
  reduce_add_mont_reduce a ⦃ a1 =>
    a1.val ≤ reduceAddStepBound ∧
    (a1.val : Spec.Zq) = (a.val : Spec.Zq) * 169 ⦄ := by
  unfold reduce_add_mont_reduce
  -- Apply progress for each monadic step, naming results
  let* ⟨ amul, amul_post ⟩ ← core.num.U32.wrapping_mul.progress_spec
  let* ⟨ inv, inv_post_1, inv_post_2 ⟩ ← UScalar.and_spec
  let* ⟨ invq, invq_post_1, invq_post_2 ⟩ ← U32.mul_bv_spec
  let* ⟨ ainvq, ainvq_post_1, ainvq_post_2 ⟩ ← U32.add_bv_spec
  let* ⟨ a1, a1_post_1, a1_post_2 ⟩ ← U32.ShiftRight_spec
  -- Prove bit-vector equality
  have ha1_eq : a1.val = (a.val + inv.val * Q.val) / 2^16 := by bv_tac 32
  -- Prove modular equivalence using zmodify
  have hPost1 : (a1.val : Spec.Zq) = (a.val : Spec.Zq) * 169 := by
    have ⟨ hMont, _ ⟩ := mont_reduce_spec 3329 (2^16) 3327 a.val ...
    zify at ha1_eq
    zify
    simp [ha1_eq, hMont, Int.mul_emod]
  -- Prove bounds using scalar_tac
  have hPost2 : a1.val ≤ 4711 := by
    have hBound := mlKem_mont_reduce_bounds_reduce_add a.val (by scalar_tac)
    zify at ha1_eq
    scalar_tac
  simp [hPost1, hPost2]
```

### Compression with intermediate spec bridging
```lean
theorem compress_coeff.spec (d coeff : U32) (hd : d.val ≤ 12) (hc: coeff.val < Spec.Q) :
  compress_coefficient d coeff ⦃ coeff' =>
    (coeff'.val : ZMod (Spec.m d.val)) =
      (SpecAux.compressOpt d.val coeff.val : ZMod (Spec.m d.val)) ∧
    coeff'.val < Spec.m d.val ⦄ := by
  progress with compress_coeff.spec_aux as ⟨ coeff', h1 ⟩
  have : NeZero (Spec.m d.val) := by constructor; simp [Spec.m]; split <;> simp
  simp only [SpecAux.compressOpt, Nat.cast_ofNat, Spec.m] at *
  split <;> simp_all
  zify
  simp_scalar
```

## Performance Considerations

Crypto proofs can be expensive. Strategies:

1. **Proof time matters.** If a proof is slow, invest time in decomposing it into smaller lemmas.
2. **Function decomposition** (fold theorems) is the primary tool for managing proof complexity.
3. **Use `maxHeartbeats`/`maxRecDepth` judiciously:**
   ```lean
   set_option maxHeartbeats 5000000 in
   theorem my_expensive_proof ...
   ```
4. **After completing a proof, try to make it shorter.** Shorter proofs check faster.
5. **Track proof times** — the SymCrypt project maintains a `proof-time.md` document.
6. **Prefer `agrind` over `grind`** — `grind` calls tend to explode in proof time.

## Summary: Crypto Verification Checklist

1. ☐ Set up `#setup_aeneas_simps` and attribute management at top of file
2. ☐ Define the multi-level spec pipeline for your algorithm
3. ☐ Write auxiliary specs that mirror the code structure in pure math
4. ☐ Decompose large functions with private defs + fold theorems
5. ☐ Use bit-vector specs for bitwise operations
6. ☐ Use `zmodify`/ZMod for modular reasoning, Nat/Int for bounds
7. ☐ Register crypto constants for all relevant tactics
8. ☐ Prefer `getElem!` for array access
9. ☐ Monitor proof times and decompose if too slow
10. ☐ Shorten proofs after they work
