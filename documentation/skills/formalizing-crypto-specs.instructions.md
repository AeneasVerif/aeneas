# Formalizing Cryptographic Specifications — Skill File

## Overview

This skill file describes how to formalize cryptographic algorithms from their
official specifications (typically NIST standards or RFCs) into executable Lean
definitions. The goal is a mechanization that is **syntactically as close as
possible to the reference document**, executable against test vectors, and suitable
as a verification target for Rust implementations.

**For general agent management rules** (resource budgets, file isolation, spawning
rules, etc.), see `agent-fleet-management.instructions.md`. This file only covers
the formalization-specific workflow.

## Supervisor Workflow

### Step 1: Identify the specification document

The supervisor (not the agent) handles document identification:

1. **Search for the official specification** — typically a NIST standard, RFC,
   or IETF draft. Look for the most authoritative source (FIPS publication >
   NIST draft > RFC > academic paper).
2. **List all candidate documents** to the user with brief descriptions:
   > "Found these candidates for ML-KEM:
   > - FIPS 203 (final, Aug 2024) — ML-KEM standard
   > - NIST SP 800-227 (draft) — recommendations for ML-KEM
   > - RFC 9xxx (draft) — ML-KEM for TLS
   > Which should I use?"
3. **Wait for user confirmation** before dispatching any formalization agent.

### Step 2: Plan the project structure

Before dispatching any agents, the supervisor plans and presents the project
structure to the user for approval:

1. **File layout** — which `.lean` files will be created and what each contains.
   **Each algorithm's complete formalization lives in a single file.** In practice,
   all cryptographic algorithms are small enough to fit comfortably in one file —
   even complex ones like ML-KEM (NTT, compress, encrypt, decrypt, keygen, encaps,
   decaps) amount to a few hundred lines of Lean. Do not split across files.

   **Tests, efficient implementations, and equivalence proofs go in a separate
   folder** — the reference spec files must remain clean and close to the RFC.

   Typically, multiple algorithms are formalized in a shared `Spec/` folder.

   ```
   Spec/
   ├── FrodoKem.lean         -- Complete FrodoKem spec (single file)
   ├── MlKem.lean            -- Complete ML-KEM spec (single file)
   └── Test/
       ├── FrodoKem/         -- FrodoKem test infrastructure
       │   ├── Efficient.lean
       │   ├── Equivalence.lean
       │   └── Vectors.lean
       └── MlKem/            -- ML-KEM test infrastructure
           └── ...
   ```

2. **Agent assignments** — which agent formalizes which algorithm, and any
   dependency order between spec files (e.g., if one algorithm imports another).

3. **Wait for user approval** before proceeding. The user may want to adjust
   naming, file organization, etc.

### Step 3: Dispatch formalizer agents

Once the project structure is approved, the supervisor dispatches formalizer agents.

**Parallelization:** Each algorithm gets its own agent working on its own file.
For example:
- Agent A: FrodoKem (`Spec/FrodoKem.lean`)
- Agent B: ML-KEM (`Spec/MlKem.lean`)

**Each agent produces exactly one `.lean` file** containing the complete formalization
of its algorithm. Follow the file isolation rules from
`agent-fleet-management.instructions.md`.

### Step 4: Review loop

When a formalizer agent finishes:
1. **Spawn a reviewer agent** that checks the mechanization against the rules below.
2. If issues are found, spawn a formalizer agent to fix them.
3. Repeat until the reviewer approves.
4. **Report to the user** at each step — what was formalized, what issues were
   found, what remains.

### Step 5: Test against official test vectors

Once the reference spec is reviewed and approved:

1. **Locate official test vectors** — NIST KATs, RFC appendix vectors, or reference
   implementation test suites. Present candidates to the user for confirmation.
2. **Dispatch a testing agent** that writes the test infrastructure in the `Test/`
   folder (separate from the reference spec):
   - **Efficient implementations** using `Array`, `ByteArray`, `UInt32`, etc.
   - **Equivalence proofs** showing the efficient version equals the reference spec
   - **Test vector checks** using `#eval` or `native_decide`
3. The reference spec files must NOT be modified for testing purposes — all test
   infrastructure lives in the `Test/` folder.

## Formalizer Agent Instructions

### Closeness to the RFC

The mechanized specification in Lean must be **syntactically as close as possible**
to the reference document. This is the primary design goal — reviewers should be
able to read the Lean code side-by-side with the RFC and verify correspondence.

**Structural rules:**
- Go through sections/algorithms **one by one**, in the order they appear in the RFC.
- For each Lean definition, include a comment referencing the RFC:
  ```lean
  /-- ML-KEM KeyGen — FIPS 203, Algorithm 16 -/
  def mlkem.keygen ...
  ```
- Name definitions to match the RFC where possible (e.g., `ntt`, `Compress`,
  `K_PKE.Encrypt`).

**Use `do` notation (Id monad)** when the RFC is written algorithmically:
```lean
def ntt (f : Polynomial) := Id.run do
  let mut f := f
  let mut i := 1
  for h0: len in [128 : >1 : /= 2] do
    for h1: start in [0 : 256 : 2*len] do
      let zeta := ζ ^ (bitRev 7 i)
      i := i + 1
      for h: j in [start : start+len] do
        let t := zeta * f[j + len]
        f := f.set (j + len) (f[j] - t)
        f := f.set j         (f[j] + t)
  pure f
```

Range notations (as defined in Aeneas) can be used to match RFC loop syntax
(e.g., `[0 : 256 : 2*len]` for strided ranges).

**Array initialization:** When the informal specification uses an array without
explicitly initializing it (e.g., `bytesToBits` declares an output array and
immediately starts writing to it), initialize it with default values (typically
zeros). In Lean, use `Vector.replicate n 0` or `Vector.mkVector n default`
as appropriate.

### Mathlib integration

Use mathlib notations and definitions wherever they match the RFC's mathematical
objects:
- `ZMod q` for modular arithmetic
- `Polynomial (ZMod q)` or custom polynomial types as appropriate
- `Matrix` for matrix operations
- `Bool` for individual bits (not `Nat`, not `UInt8`, not `Fin 2`)
- `BitVec n` for fixed-width bit strings
- Standard algebraic typeclasses (`Ring`, `CommRing`, etc.)

### Executability

**The mechanization should be executable** (computable by `#eval`) whenever possible.
This enables testing against official test vectors.

If a definition relies on non-computable mathlib constructs, provide both:
1. A **reference definition** that is syntactically close to the RFC (may be
   non-computable) — this stays in the spec file.
2. An **executable definition** using efficient data structures (arrays, etc.)
   with a proof of equivalence — these go in the `Test/` folder.

### Notation

It is fine to introduce notations, as long as they are:
- Simple and genuinely improve readability
- Documented with a comment explaining what they represent
- Scoped (using `scoped notation` or `local notation`) to avoid polluting the
  global namespace

### Documenting ambiguities and mechanization choices

**If anything in the RFC is ambiguous**, or the agent must make a mechanization
choice that is not obvious (e.g., how to represent a mathematical object in Lean,
how to interpret an underspecified operation), **document it explicitly**:

```lean
/-- NOTE (mechanization choice): The RFC says "sample uniformly from {0,...,q-1}"
    but doesn't specify the sampling algorithm. We model this as a function
    `sample : ByteStream → ZMod q` that consumes bytes from a stream.
    See Section 4.2.1 of FIPS 203. -/
```

### Handling randomness

Cryptographic functions often use random inputs. This is the ONE case where we
**intentionally depart from the RFC structure**:

1. **Define an `_internal` function** that receives the random values as explicit
   parameters:
   ```lean
   /-- Internal encapsulation — takes random bytes `m` as explicit input.
       FIPS 203, Algorithm 17 (modified to take randomness explicitly). -/
   def mlkem.encaps_internal (p : ParameterSet)
       (ek : 𝔹 (384 * k p + 32))
       (m : 𝔹 32) :
       𝔹 32 × 𝔹 (32 * (dᵤ p * k p + dᵥ p)) :=
     ...
   ```

2. **Define the "real" function** using state-passing with a random tape.
   The random tape is a stream of bits (some algorithms consume bits, others
   bytes — bits are the most general). Reading consumes bits by shifting the
   tape forward:
   ```lean
   /-- A random tape is an infinite stream of bits.
       Reading advances the tape (the head is at index 0). -/
   def RandomTape := ℕ → Bool

   /-- Read `n` bits from the head of the tape.
       Returns the bits and the tape shifted by `n`. -/
   def readBits (tape : RandomTape) (n : ℕ) :
       BitVec n × RandomTape :=
     (BitVec.ofFn (fun i => tape i), fun i => tape (n + i))
   ```
   Define `RandomTape` and `readBits` (and convenience wrappers like `readBytes`)
   once, shared across all spec functions. Then the "real" function threads the
   tape through:
   ```lean
   def mlkem.encaps (p : ParameterSet)
       (ek : 𝔹 (384 * k p + 32))
       (tape : RandomTape) :
       𝔹 32 × 𝔹 (32 * (dᵤ p * k p + dᵥ p)) × RandomTape :=
     let (m, tape) := readBits tape (32 * 8)
     let (K, c) := mlkem.encaps_internal p ek m.toBytes
     (K, c, tape)
   ```

3. **Only the `_internal` function** will be used for verification (proving
   refinement of the Rust code). The wrapper with the random tape is for
   completeness and composability.

### Static bounds checking

**Always use bounds-checked accessors** — never use the `!` (panicking) variants:
- Use `getElem` (i.e., `a[i]` with a proof), **not** `getElem!` (i.e., `a[i]!`)
- Use `Vector.set` / `Array.set`, **not** `Vector.set!` / `Array.set!`

This ensures all index accesses are statically verified to be in bounds. The proof
obligations are discharged by the `get_elem_tactic` override described below.

### Proofs and `getElem` bounds

The mechanization will need proofs here and there, typically to satisfy `getElem`
bounds (array/vector index proofs). Guidelines:

- It is fine to locally override `get_elem_tactic` to handle these automatically:
  ```lean
  scoped macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| scalar_tac)
  ```
  This makes `a[i]` notation work without explicit bound proofs — `scalar_tac` will
  try to discharge the bound automatically. Place this in a `namespace` / `end` block
  and `open` it where needed.
- For parameter-dependent bounds (e.g., array sizes that depend on the parameter
  set), see the "Avoid early case splits on parameters" section in
  `aeneas-lean-core.instructions.md` — prefer `attribute [local agrind]` or
  local auxiliary lemmas over top-level `cases p`.
- Keep proofs minimal — they should not distract from the specification. If a
  bound proof requires more than 2-3 lines, extract it as an auxiliary lemma.
- If the same tactic calls appear repeatedly (e.g., `by cases p <;> simp_all`
  for every `getElem` bound), introduce a **local macro** to avoid clutter:
  ```lean
  local macro "param_bounds_tac" : tactic => `(tactic| cases p <;> simp_all [n, nbar])
  ```
  Then use `(by param_bounds_tac)` throughout the spec instead of repeating the
  full tactic sequence.

### Interactive development

**Use `lean_lsp.py` for interactive development** — see `lean-lsp-tool.instructions.md`.
Do NOT use `lake build` loops.

## Testing Against Test Vectors

**All test infrastructure lives in the `Test/` folder** — separate from the reference
spec files. This keeps the reference spec clean and readable. The `Test/` folder
contains efficient implementations, equivalence proofs, and test vector checks.

### Strategy

1. **Start with small tests** — don't immediately run the full test suite. Begin
   with the smallest test vector (e.g., a single NTT of a known polynomial) to
   verify basic correctness.

2. **Profile early** — `#eval` on cryptographic functions can be slow. If a test
   takes more than a few seconds:
   - Check for compilation issues (non-computable definitions leaking in)
   - Check for inefficient representations (e.g., `List` where `Array` would be
     faster)
   - Consider using `native_decide` or `#eval` with optimized definitions

3. **If direct evaluation is too slow**, introduce an optimized executable
   definition in `Test/Efficient.lean`:
   - Write an alternative implementation using efficient data structures
     (`Array`, `ByteArray`, `UInt32`, etc.)
   - Prove it equivalent to the reference definition (in `Test/Equivalence.lean`)
   - Test the optimized version against test vectors (in `Test/Vectors.lean`)
   - The reference definition remains the one used for verification proofs —
     it is never modified for performance

4. **Debug thoroughly** — mismatches with test vectors often indicate:
   - Byte ordering issues (big-endian vs little-endian)
   - Off-by-one errors in loop bounds
   - Different conventions for polynomial representation
   - Modular reduction applied at different points

### Test vector sources

Official test vectors are typically published alongside the standard:
- NIST provides Known Answer Tests (KATs) for post-quantum algorithms
- RFCs include test vectors in appendices
- Reference implementations include test suites

The supervisor should locate test vectors and provide them to the agent (as file
paths or inline data).

## Reviewer Agent Checklist

The reviewer checks the mechanization against all rules above:

1. **RFC correspondence**: Can each Lean definition be traced to a specific
   algorithm/section in the RFC? Are the references documented?
2. **Syntactic closeness**: Does the Lean code read naturally alongside the RFC?
   Are unnecessary deviations justified and documented?
3. **Mathlib usage**: Are standard mathlib types used where appropriate?
4. **Executability**: Can the definitions be `#eval`'d? If not, is a computable
   alternative provided with an equivalence proof?
5. **Ambiguity documentation**: Are all non-obvious mechanization choices documented?
6. **Randomness handling**: Do functions with randomness follow the `_internal`
   pattern? Is the random function defined once and reused (not duplicated)?
7. **Notation**: Are introduced notations simple, documented, and scoped?
8. **Proof overhead**: Are `getElem` bound proofs minimal and non-distracting?
9. **Test separation**: Are all test infrastructure, efficient implementations, and
   equivalence proofs in the `Test/` folder? The reference spec files must not
   contain test-only code.
10. **Test coverage**: Were test vectors run? Do they pass?
11. **File builds cleanly**: Run `lake build <module>` — 0 errors required.

## Common Failure Modes

| Failure | Cause | Fix |
|---------|-------|-----|
| Non-computable definition | Used mathlib construct without `Decidable` | Provide computable alternative + equivalence proof |
| Test vector mismatch | Byte ordering or representation mismatch | Check endianness, polynomial conventions |
| Slow `#eval` | Inefficient data structures | Use Array/ByteArray for testing, prove equivalence |
| Unreadable code | Drifted from RFC structure | Restructure to match RFC section by section |
| Missing documentation | Ambiguous choices not documented | Add mechanization notes for every non-obvious choice |
| `getElem` proof explosion | Many array accesses with complex bounds | Configure `get_elem_tactic` locally, extract bound lemmas |
