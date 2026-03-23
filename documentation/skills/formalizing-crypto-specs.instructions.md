---
name: formalizing-crypto-specs
description: Formalizing crypto algorithms from NIST/RFC specs into executable Lean definitions
---

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

**Prerequisite skill files:** All agents (formalizer, reviewer, fixer) MUST read
the following skill files before starting work:
- `formalizing-crypto-specs.instructions.md` (this file — includes PDF handling)
- `aeneas-lean-core.instructions.md` — Aeneas translation model and Lean idioms
- `aeneas-tactics-quickref.instructions.md` — tactic decision tree, banned tactics
- `aeneas-crypto-verification.instructions.md` — crypto proof strategies

The supervisor MUST include these file paths in every agent dispatch prompt.

## Supervisor Workflow

### Step 1: Identify the specification document

The supervisor (not the agent) handles document identification:

1. **Search for the official specification** — typically a NIST standard, RFC,
   or IETF draft. Look for the most authoritative source (FIPS publication >
   NIST draft > RFC > academic paper).
2. **Obtain the specification document.** Download the PDF and extract text
   using `pdftohtml -xml` (see "Handling Unreadable File Formats" section below).
   **If the document cannot be downloaded or read** (paywall, restricted access,
   network issues), **inform the user explicitly and immediately** — do NOT
   silently fall back to training knowledge. The user may provide a local copy
   or choose an alternative source.
3. **List all candidate documents** to the user with brief descriptions:
   > "Found these candidates for ML-KEM:
   > - FIPS 203 (final, Aug 2024) — ML-KEM standard
   > - NIST SP 800-227 (draft) — recommendations for ML-KEM
   > - RFC 9xxx (draft) — ML-KEM for TLS
   > Which should I use?"
4. **Wait for user confirmation** before dispatching any formalization agent.

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

**Every agent prompt MUST include:**
1. Paths to all prerequisite skill files (listed in Overview above)
2. The specification document (extracted text or XML from the PDF)
3. The instruction to read the skill files before starting work

If the specification PDF could not be obtained, do NOT dispatch agents — inform
the user and wait for them to provide the document.

**Parallelization:** Each algorithm gets its own agent working on its own file.
For example:
- Agent A: FrodoKem (`Spec/FrodoKem.lean`)
- Agent B: ML-KEM (`Spec/MlKem.lean`)

**Each agent produces exactly one `.lean` file** containing the complete formalization
of its algorithm. Follow the file isolation rules from
`agent-fleet-management.instructions.md`.

### Step 4: Fix → Review → Fix convergence loop

The supervisor drives an iterative convergence loop until each spec file
passes review with zero issues.

**Round structure:**

1. **Review round:** Dispatch one reviewer agent per spec file (in parallel).
   Each reviewer checks against the full Reviewer Agent Checklist below and
   returns a list of issues with severities (Critical / High / Medium / Low).

   **Every review round is a FULL review.** Do NOT tell reviewers to "confirm
   fixes" or "check only new issues." Reviewers must read the spec and the
   code from scratch every time. Do NOT mention prior rounds, prior issues,
   or prior fix agents in the reviewer prompt — this biases the agent toward
   rubber-stamping. The prompt should be identical to a first-time review.

2. **Triage:** The supervisor consolidates review results across all files and
   reports to the user:
   - Number of issues per file and severity breakdown
   - Summary of each issue (one line)
   The supervisor does NOT ask permission to fix — it proceeds immediately
   unless a review finding is ambiguous (in which case, ask the user).

3. **Fix round:** Dispatch one fixer agent per file that has issues (in parallel).
   Each fixer agent receives:
   - The file path
   - The exact list of issues to fix (copy-pasted from the reviewer output)
   - The instruction: "Fix ALL listed issues. Do NOT introduce new issues.
     Run `lake build <module>` after fixing to verify 0 errors."
   Fixer agents work on **separate files** — no two agents touch the same file.
   Cross-file issues (e.g., "add RandomTape threading") may require sequential
   fixing if the change spans multiple files.

4. **Verify build:** After all fixers complete, the supervisor runs
   `lake build` on the full project to confirm 0 errors.

5. **Repeat:** Go back to step 1 (review round) with the updated files.
   Continue until a review round returns zero issues for all files.

**Convergence guarantee:** Each round must strictly reduce the number of issues.
If a fix round introduces new issues or fails to fix existing ones, the
supervisor should:
- Re-dispatch the fixer with more specific instructions
- Or fix the issue directly if it's small
- After 3 failed rounds on the same issue, escalate to the user

**Parallelization rules:**
- Reviewers: always parallel (they are read-only)
- Fixers: parallel when working on different files; sequential when a fix
  in file A affects file B (e.g., changing a type in Common.lean)
- Build verification: always sequential (one `lake build` at the end)

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

**What "syntactically close" means concretely:**
Every line of pseudocode in the RFC should map to a recognizable line in the Lean
code. The correspondence must hold at the **expression level**, not just at the
structural level:
- If the RFC says `zeta ← ζ^{BitRev₇(i)} mod q`, the Lean code must say
  something like `let zeta := ζ ^ (bitRev7 i)` (with `ζ : ZMod q` handling
  the modular reduction). It must NOT wrap this in a helper function like
  `zetaNTT i` — that breaks the 1:1 line correspondence even if semantically
  equivalent.
- If the RFC says `a ← (a − b[i·d + j])/2`, the Lean code must write the
  subtraction and division, not simplify to `a / 2`.
- Helper functions are allowed ONLY for operations that the RFC itself defines
  as subroutines (e.g., `BitRev₇` is defined in the RFC, so `bitRev7` is fine).
  Do NOT introduce helpers for subexpressions that the RFC writes inline.

**The test:** for each line of Lean code annotated `-- line N`, a reviewer must be
able to look at RFC line N and confirm the expressions match without needing to
unfold any definitions that don't appear in the RFC.

**Structural rules:**
- Go through sections/algorithms **one by one**, in the order they appear in the RFC.
- For each Lean definition, include a **doc-comment that quotes the relevant RFC
  pseudocode verbatim** (or as close as plain text allows). This lets reviewers
  verify correspondence without opening the RFC:
  ```lean
  /-- ML-KEM KeyGen — FIPS 203, Algorithm 16
      ```
      (ek, dk) ← ML-KEM.KeyGen()
      z ← B32
      ek ← ByteEncode₁₂(t̂) ‖ ρ
      dk ← ...
      ``` -/
  def mlkem.keygen ...
  ```
- Name definitions to match the RFC where possible (e.g., `ntt`, `Compress`,
  `K_PKE.Encrypt`).

**Unicode naming conventions:**
- When a variable in the RFC has a hat/circumflex (e.g., f̂, t̂, k̂), use Lean's
  **escaped identifier syntax** `«f̂»` (French quotes `«»` around the letter +
  combining circumflex U+0302). Lean normally rejects combining characters in
  identifiers, but the `«»` escape allows any Unicode string as an identifier.
  This works everywhere: `def`, `let`, `let mut`, function parameters, pattern
  matching, etc.
  ```lean
  -- «f̂» = U+00AB, f, U+0302 (combining circumflex), U+00BB
  def ntt (f : Poly) : Poly := Id.run do
    let mut «f̂» := f              -- f̂ ← f
    for h : j in [0 : 256] do
      «f̂» := «f̂».set ⟨j, by agrind⟩ (...)
    return «f̂»

  def multiplyNTTs («f̂» «ĝ» : Poly) : Poly := ...
  ```
  **Which characters need `«»` escaping?** Only those without a precomposed
  Unicode form. In practice:
  - **Need `«»`**: f̂, t̂, k̂, Â (no precomposed form for f/t/k/A + circumflex)
  - **No `«»` needed**: ĉ, ĝ, ĥ, ĵ, ŝ, ŵ, ŷ, ẑ (precomposed forms exist)
  
  To type `«f̂»` in your editor: type `«`, then `f`, then the combining
  circumflex (often via compose key or character picker), then `»`.

- When a variable has a bar/macron (e.g., n̄, m̄), use the `bar` suffix:
  `nbar`, `mbar`. (No precomposed form exists for most of these, and `«n̄»`
  is less readable than `nbar`.)
- Greek letters (ζ, ρ, σ, η, μ, θ, etc.) work fine — they are single codepoints.
- Subscripts (η₁, η₂, dᵤ, dᵥ) work fine in struct fields.

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
- **Never** use `.getD` (default-value fallback) to avoid bounds proofs. `.getD`
  silently returns a default on out-of-bounds, masking bugs. Use bounds-checked
  access with `by sorry` if `agrind` can't discharge the proof.

**Prefer `Vector n α` over `Array α`** when the size is known statically (which
is almost always the case in crypto specs — polynomials are degree-256, matrices
are n×n, etc.). `Vector` carries the size in the type, making bounds proofs
automatic via `get_elem_tactic`. For example:
```lean
abbrev Poly := Vector (ZMod q) 256

def ntt (f : Poly) : Poly := Id.run do
  let mut «f̂» := f              -- Vector (ZMod q) 256, size tracked
  ...
  «f̂» := «f̂».set ⟨j + len, by agrind⟩ (...)  -- bounds-checked
```

When a function builds an array incrementally (via `push` in a loop), use `Array`
locally, then convert to `Vector` at the return point via `⟨arr, by sorry⟩` (not
`Vector.ofFn fun i => if h : i.val < arr.size then arr[i.val] else 0` — that
pattern silently maps out-of-bounds to a default, same problem as `.getD`).

**`Vector.set` over `Array.push`:** When the RFC pseudocode builds an array inside
a loop, ask: (1) is the final size known before the loop starts? (2) can each
element's destination index be computed from the loop variables? If both are true,
initialize the collection as `Vector.replicate n default` and use
`Vector.set idx val` — do NOT start with `#[]` and `Array.push`. This keeps the
`Vector` type throughout the loop body, avoids a size proof at the return point,
and makes every index access bounds-checked (the `get_elem_tactic` override
discharges the implicit bound via `agrind`, or leaves a `sorry` if it can't).

Example — `bytesToBits` builds `8*ℓ` elements where element `8*i+j` is known at
each step:
```lean
let mut bits : Vector Nat (8 * ℓ) := Vector.replicate (8 * ℓ) 0
for h:i in [0 : ℓ] do
  for h2:j in [0 : 8] do
    bits := bits.set (8 * i + j) (...)
```

**When a bounds check cannot be discharged by `agrind`:** use `by sorry` to fill
the proof obligation — **never** fall back to `!` (panicking) accessors, `.getD`,
`Array` conversions, or restructuring the code away from the RFC's loop structure.
`by sorry` makes the proof debt explicit and preserves syntactic fidelity.
Example:
```lean
for h:i in [0 : 8 * ℓ] do
  have hByte : i / 8 < ℓ := by sorry  -- TODO: bounds obligation
  B := B.set ⟨i / 8, hByte⟩ (...)
```
Agents must report all `sorry`s in their final output. These are proof
obligations for a later proof agent to close.

**NEVER** convert `Vector` to `Array` (via `.toArray`) or `𝔹 n` to `ByteArray`
(via `.toByteArray`) just to avoid bounds proofs. This defeats the purpose of
carrying sizes in types.

### Proofs and `getElem` bounds

The mechanization will need proofs here and there, typically to satisfy `getElem`
bounds (array/vector index proofs). Guidelines:

- **Never use `omega`** for discharging bounds. Use the following tactics, in
  order of preference:
  1. `agrind` — first choice; handles most arithmetic goals
  2. `grind` — fallback when `agrind` doesn't close the goal
  3. `scalar_tac` — last resort for simple linear arithmetic on scalars
- It is fine to locally override `get_elem_tactic` to handle these automatically:
  ```lean
  scoped macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| agrind)
  ```
  This makes `a[i]` notation work without explicit bound proofs — `agrind` will
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

**Every review is a full review from scratch.** Do not assume prior rounds were
correct. Read the spec and the code independently.

The supervisor should dispatch **two separate reviewer agents per file**:

### Agent A: Syntactic fidelity reviewer

This agent's ONLY job is to compare the Lean code against the RFC line by line.
It must NOT comment on code quality, correctness, or style — only on whether
the Lean expressions match the RFC expressions.

**Required output format — a comparison table for each algorithm:**

```
## Algorithm 9: NTT (FIPS 203, §4.3)

| RFC line | RFC expression                  | Lean expression                    | Match? |
|----------|---------------------------------|------------------------------------|--------|
| 1        | f̂ ← f                          | let mut «f̂» := f.toArray          | ⚠ toArray not in RFC |
| 5        | zeta ← ζ^{BitRev₇(i)} mod q    | let zeta := ζ_root ^ (bitRev7 i)  | ✅     |
| 8        | t ← zeta · f̂[j + len]          | let t := zeta * «f̂»[j + len]!    | ⚠ uses ! |
...
```

If the reviewer cannot fill in the "RFC expression" column, it hasn't read the
spec. Every row must have both columns filled.

**Signature types check:** For every algorithm, verify that function input/output
types carry the RFC's dimension constraints. When the RFC specifies a fixed-size
collection (e.g., `b ∈ {0,1}^{8ℓ}`, `B ∈ 𝔹^ℓ`, `f ∈ ℤ^{256}_q`), the Lean
signature must use `Vector` with the matching size — not `Array`. Flag any
`Array α` parameter or return type where the RFC gives an explicit dimension.

**Additionally, list all `def`s in the Lean file that do NOT correspond to a
named algorithm/function in the RFC:**

```
## Non-RFC definitions audit

| Lean def          | RFC counterpart?  | Verdict                          |
|-------------------|-------------------|----------------------------------|
| ζ_root            | ζ (FIPS §4.3)     | ✅ Justified — module-level constant |
| arrayToPoly       | (none)            | ❌ Spurious — should be inlined  |
| polyAdd           | (none)            | ❌ Spurious — use + instance     |
```

### Agent B: Semantic correctness reviewer

This agent checks everything EXCEPT syntactic fidelity (that's Agent A's job):

1. **Mathlib usage**: Are standard mathlib types used where appropriate?
2. **Executability**: Can the definitions be `#eval`'d?
3. **Ambiguity documentation**: Are all mechanization choices documented?
4. **Randomness handling**: `_internal` pattern, RandomTape shared?
5. **Notation**: Simple, documented, scoped?
6. **Proof overhead**: Minimal, non-distracting?
7. **Test separation**: No test code in spec files?
8. **Banned tactics**: No `omega` — only `agrind`/`grind`/`scalar_tac`.
9. **No `!` / `.getD` / type-stripping** — flag ANY use of:
   - `!` accessors (`get!`, `set!`, `[i]!`)
   - `.getD` (default-value fallback that silently masks out-of-bounds)
   - `.toArray` / `.toByteArray` conversions that strip size information
   - `Vector.ofFn fun i => if h : i.val < arr.size then arr[i.val] else 0`
     (silently maps out-of-bounds to default — same problem as `.getD`)
   - `let mut x := #[]` followed by `x := x.push` inside a loop — ask: is the
     final size known before the loop? Can each element's index be computed from
     loop variables? If both yes, flag: should use `Vector.replicate` + `.set`.
   The correct fix for all of these is bounds-checked access with `by sorry`.
10. **File builds cleanly**: `lake build <module>` — 0 errors.

## Common Failure Modes

| Failure | Cause | Fix |
|---------|-------|-----|
| Non-computable definition | Used mathlib construct without `Decidable` | Provide computable alternative + equivalence proof |
| Test vector mismatch | Byte ordering or representation mismatch | Check endianness, polynomial conventions |
| Slow `#eval` | Inefficient data structures | Use Array/ByteArray for testing, prove equivalence |
| Unreadable code | Drifted from RFC structure | Restructure to match RFC section by section |
| Missing documentation | Ambiguous choices not documented | Add mechanization notes for every non-obvious choice |
| `getElem` proof explosion | Many array accesses with complex bounds | Configure `get_elem_tactic` locally, extract bound lemmas |
| Spurious helper functions | Subexpression wrapped in helper not in RFC | Inline the expression; only RFC-named subroutines are allowed as helpers |
| Algebraic simplification | Expression simplified relative to RFC | Write the RFC's form, even if a simpler equivalent exists |

## Handling Unreadable File Formats

### Critical Rule

**If the user asks you to read or use a file and you cannot actually read it (e.g., a PDF, a binary file, an image with embedded text), say so immediately and upfront.** Do NOT silently rely on training knowledge or guess the content. Be explicit about what you can and cannot access.

**Examples:**

- User: "Read the FIPS 203 PDF and formalize the algorithms"
  - ✅ Correct: "I cannot read PDF files directly. Let me install pymupdf to extract the text, or you can provide the relevant sections."
  - ❌ Wrong: Silently writing code based on training knowledge without disclosing you didn't read the PDF.

- User: "Check the spec in spec.pdf"
  - ✅ Correct: "I can't read PDFs natively. I can install pymupdf to extract the text — shall I?"
  - ❌ Wrong: Pretending to have read it, or guessing the content.

### Reading PDFs with `pdftohtml -xml`

Use poppler's `pdftohtml` to extract PDF content as XML. The XML output contains
per-span font size, position (top/left), and width — enough for an agent to
interpret superscripts, subscripts, and indentation directly.

**Requirement:** `pdftohtml` from poppler. **Do not install it without asking the user
first.** If poppler is not available, ask the user for permission before installing
(`brew install poppler` on macOS, `apt install poppler-utils` on Linux).

#### Usage

```bash
pdftohtml -xml -f <start_page> -l <end_page> -stdout file.pdf
```
Pages are 1-indexed. Extract a few pages at a time to keep token cost manageable.

#### How to read the XML

The output contains `<fontspec>` declarations and `<text>` spans:
```xml
<fontspec id="5" size="18" family="LatinModernMath" color="#000000"/>
<fontspec id="7" size="13" family="LatinModernMath" color="#000000"/>
<text top="273" left="147" width="21" height="15" font="2">for</text>
<text top="309" left="266" width="38" font="12">BitRev</text>
```

**Interpreting the spans:**
- **Font size** distinguishes baseline text from super/subscripts. The baseline
  font is typically the most common size (e.g., size 18). Spans with smaller size
  (e.g., size 13) are superscripts or subscripts.
- **`top` position** distinguishes superscript from subscript: smaller `top` =
  higher on page = superscript; larger `top` = lower = subscript. Compare against
  the `top` of baseline-sized spans on the same line.
- **`left` position** encodes indentation. Deeper nesting = larger `left` value.
  This is critical for reading algorithm pseudocode with nested loops.
- **`width="0"`** spans are combining characters (e.g., hat `̂`, tilde). They
  modify the previous character but carry no width.

#### Quality notes

- **Greek letters** (θ, ρ, π, χ, ι, ζ): ✅ Preserved in Unicode
- **Math symbols** (⊕, ≤, ⋅, ∈): ✅ Preserved in Unicode
- **Superscripts/subscripts**: ✅ Detectable via font size + top position
- **Indentation**: ✅ Encoded in `left` coordinates
- **Algorithm pseudocode**: ✅ All information present (nesting, line numbers)
- **Tables**: ⚠️ May require careful `left`-position grouping
- **Figures/diagrams**: ❌ Not extractable as text

#### Fallback: pdftotext -layout

When you just need readable text without super/subscript detection:
```bash
pdftotext -layout file.pdf - | sed -n '100,200p'
```
Preserves indentation but loses font-size metadata.

#### When poppler is not available

If poppler is not installed, **ask the user** which approach they prefer:
1. Install poppler: `brew install poppler` (macOS) or `apt install poppler-utils` (Linux) — **only with user permission**
2. User pastes relevant sections into the chat
3. User converts PDF to text themselves
4. Look for HTML versions of the same document (e.g., IETF drafts on datatracker.ietf.org)

### General principle

**Transparency over convenience.** It is always better to tell the user "I cannot read this file" than to silently fabricate or guess content. This applies to:
- PDF files
- Binary files (`.bin`, `.dat`, compiled objects)
- Images with text (`.png`, `.jpg` of documents)
- Encrypted or password-protected files
- Files in formats you have no parser for
