# Aeneas Lean Tactics Reference

## Core Tactics

### `step`
The main workhorse tactic for Aeneas proofs. It applies function specifications (theorems tagged with `@[step]`) to make progress on goals involving monadic function calls.

**How it works:** When the goal contains a monadic bind like `do let x ← f args; ...`, `step` looks for a theorem tagged with `@[step]` whose conclusion matches `f args ⦃ x => ... ⦄`, applies it, and leaves the preconditions and remaining goals for the user to prove.

**Syntax:**
```lean
step                        -- basic: apply matching step theorem
step as ⟨ x, h1, h2 ⟩  -- name the result and hypotheses
step with my_theorem    -- use a specific theorem
step*                   -- repeatedly apply step
step*?                  -- like step* but prints the proof script
```

**Naming hypotheses with `step as`:** When `step` applies a spec theorem, it
introduces the result variable and any postcondition components into the context.
Without `as`, these get inaccessible names (`✝`, `✝¹`, etc.). Use
`step as ⟨...⟩` to name them one by one, in order:

```lean
-- Suppose foo_spec has postcondition: ⦃ r => r.length = n ∧ ∀ i, r[i]! = 0 ⦄
step as ⟨ r ⟩              -- name the result only; postcondition components are unnamed
step as ⟨ r, h_len ⟩       -- name result + first conjunct (r.length = n)
step as ⟨ r, h_len, h_val ⟩ -- name result + both conjuncts
```

Each name binds one component of the postcondition's top-level structure
(conjunction components, existential witnesses). If unsure how many components
there are, use `lean_goal` after a plain `step` to inspect the unnamed
hypotheses, then add names to `step as ⟨...⟩` to match. If you provide too
many names, Lean warns `"Too many ids provided"` — remove the excess.

**The `@[step]` attribute:** Tag your specification theorems with `@[step]` so they are automatically found:
```lean
@[step]
theorem my_func_spec (x : U32) (h : x.val < 100) :
  my_func x ⦃ r => r.val = x.val + 1 ⦄ := by ...
```

**The `step*?` workflow:**
A very useful workflow: use `step*?` to automatically generate a complete, expanded proof script. Then review the generated script, automate individual proof obligations (e.g., by registering local lemmas for `agrind`), and progressively refold the script back into a compact `step*` call plus a small finishing script.

**Termination pitfall:** If your proof starts with `unfold foo; step` and the proof appears finished but you get a termination error, it's likely because `step` applied the specification theorem recursively (this typically happens when the function starts with a `match` or `if-then-else`). Fix: start with `split` (or `cases`) before calling `step`, to case-split on the match/if first.

**Loop reasoning:** Loops are translated to a fixed-point operator `loop`. To prove specs of loop-based code, use:
- `loop.spec_decr_nat` — provide a `Nat` termination measure, a loop invariant, and a postcondition. This is the practical workhorse for most loop proofs.
- `loop.spec` — general version with an arbitrary well-founded termination measure.

### `scalar_tac`
Arithmetic reasoning over Rust integer types. Handles bounds checking, overflow verification, and integer arithmetic.

**What it does:** Solves arithmetic goals involving scalar types (U8, U16, U32, U64, U128, I8, I16, I32, I64, I128, Usize, Isize). It understands the bounds of each type and can reason about addition, subtraction, multiplication, division, modulo, etc.

**Syntax:**
```lean
scalar_tac              -- basic usage
scalar_tac +nonLin      -- enable nonlinear arithmetic reasoning
```

**Known limitation:** `scalar_tac` sometimes struggles with Int ↔ Nat conversions. When this happens, try explicit `zify` or `natify` conversions first, or use `agrind`/`grind`.

### `simp_scalar`
Simplifies arithmetic expressions. Essentially equivalent to `simp (discharger := scalar_tac) [simp_bool_prop_simps, simp_scalar_simps]` but with the preprocessing step of `scalar_tac` factored out for better performance.

**What it does:** Automatically simplifies expressions like:
- `min a b` → `a` when `a ≤ b`
- `a % n` → `a` when `a < n`
- Various other arithmetic simplifications

**Syntax:**
```lean
simp_scalar                        -- basic
simp_scalar [my_lemma1, my_lemma2] -- with extra lemmas
```

**Custom lemmas:** Tag lemmas with `@[simp_scalar_simps]` for automatic use.

**IMPORTANT: It's safe to locally activate many ad-hoc lemmas with `simp_scalar` (and `simp_lists`). Because these tactics are based on `simp`, they perform local rewriting without long chains of reasoning — unlike SMT solvers, there's no risk of complexity explosions from adding many lemmas.**

### `simp_lists`
Simplifies expressions involving lists, particularly with getters and setters.

**What it does:** Simplifies expressions like:
- `List.get (List.set (List.set l i v0) j v1) i` → `v1` when `i ≠ j`
- `List.get (l0 ++ l1) i` → `List.get l1 (i - l0.length)` when `i ≥ l0.length`

**Syntax:**
```lean
simp_lists                         -- basic
simp_lists [my_lemma1, my_lemma2]  -- with extra lemmas
```

**Custom lemmas:** Tag lemmas with `@[simp_lists_simps]` for automatic use.

**Same safety note as simp_scalar:** safe to locally activate many lemmas without complexity explosion.

### `bvify`
Lifts propositions about `Nat`, `Int`, etc. to `BitVec`. Inspired by `zify`.

**Syntax:**
```lean
bvify 8          -- lift to BitVec 8
bvify 32         -- lift to BitVec 32
bvify 8 at h     -- lift a specific hypothesis
```

**Example:**
```lean
example (x y : U8) (h : x.val < y.val) : x.bv < y.bv := by
  bvify 8 at h
  apply h
```

**Custom lemmas:** Tag with `@[bvify_simps]`.

**Note:** Conversions require proof obligations (e.g., `a < 2^n` for `BitVec.ofNat n a`).

### `bv_tac`
Bit-vector decision procedure. Often used after `bvify` or directly on bit-vector goals.

**Syntax:**
```lean
bv_tac 32    -- decide with 32-bit vectors
```

**Reverse lifting trick:** When automatic lifting between Nat/Int and BitVec fails, there are two cases:

1. **Can't lift the goal to bit-vectors:** Write the bit-vector equivalent of the goal as a `have`, prove it with `bv_tac`, then convert back to Nat with `natify` and use the resulting hypothesis to prove the original goal.
   ```lean
   have h_bv : (bv_equivalent_of_goal) := by bv_tac 32
   natify at h_bv
   simp_scalar at h_bv   -- then use h_bv
   ```

2. **Can't lift a hypothesis to bit-vectors:** Write the bit-vector equivalent of the hypothesis in a `have`, and in its proof use `natify` (etc.) to transform the bit-vector target back into the original hypothesis.
   ```lean
   have h_bv : (bv_equivalent_of_hypothesis) := by natify; simp [original_hyp]
   -- now use h_bv with bv_tac or other bit-vector tactics
   ```

### `natify`
Converts propositions about `ZMod`, `ℤ`, `BitVec`, etc. to propositions about `ℕ`.

**Syntax:**
```lean
natify                         -- convert goal
natify at h                    -- convert hypothesis
natify [my_lemma1, my_lemma2]  -- with extra lemmas
```

**Custom lemmas:** Tag with `@[natify_simps]`.

### `zmodify`
Converts propositions about `ℕ`, `ℤ`, `BitVec`, etc. to propositions about `ZMod`.

**Syntax:**
```lean
zmodify                 -- auto-infer modulus from context
zmodify [to 256]        -- specify modulus explicitly
zmodify at h            -- convert hypothesis
```

**When to use:** Use `zmodify` (and ZMod) when reasoning about modular arithmetic operations (e.g., `a % n = b % n`). ZMod is a ring, so once you've lifted to ZMod you can use `ring` and algebraic reasoning. Stay in Nat/Int when proving bounds (e.g., `a < n`). The Montgomery and Barrett reduction proofs in SymCrypt demonstrate this nicely.

### `simp_bool_prop`
Simplifies boolean and propositional expressions. Uses lemmas tagged with `@[simp_bool_prop_simps]`.

### `simp_ifs`
Simplifies `if-then-else` expressions exclusively. Useful when you want to simplify conditionals in the goal without affecting other parts of the expression.

**Syntax:**
```lean
simp_ifs     -- simplify if-then-else in the goal
```

### `fcongr`
Like Lean's `congr` but with a tweak: it works at `.reducible` transparency to prevent Lean from trying to whnf (weak head normal form) too many things, which can cause performance issues.

**Syntax:**
```lean
fcongr       -- apply congruence
fcongr 3     -- limit depth to 3
```

### `split_conjs`
Fully recursively splits nested conjunctions (`∧`) into atomic goals. Unlike Lean's `And.intro` or `constructor`, this handles deeply nested conjunctions.

**Syntax:**
```lean
split_conjs       -- split the goal
split_conjs at h  -- split a hypothesis
```

**Useful pattern with agrind:**
```lean
split_conjs <;> agrind   -- each conjunct is easier to prove separately; often succeeds where agrind alone fails
```

## Lean Builtins Commonly Used

### `agrind` (preferred over `grind`)
A variant of `grind` that uses theorems tagged with `@[agrind]` instead of `@[grind]`. Prefer `agrind` over `grind` because `grind` calls tend to explode (uncontrolled context expansion).

**The `simp [*]; agrind` trick:** Due to a current issue in grind, `simp [*]; agrind` (or `simp [*]; grind`) can solve goals that `agrind`/`grind` alone cannot. Use this combination when `agrind` fails.

**Tag lemmas:** Use `@[agrind]` or `@[agrind =]` to register lemmas for agrind.

### `omega`
**⚠️ NEVER use `omega` in Aeneas proofs.** It cannot reason about scalars (U8, U32, etc.), does not know `U32.max`, list lengths, etc. Use `scalar_tac`, `agrind`, or `grind` instead.

### `simp` / `simp_all`
Standard Lean simplifier. 

**Pitfall with `simp_all`:** `simp_all` can eliminate hypotheses you need. When this happens, use `simp` with an explicit list of lemmas, or `simp [*]` to use all hypotheses without removing them.

### `tauto`
Propositional tautology solver.

### `decide`
Computational decidability checker. Useful for concrete finite computations.

## The `#setup_aeneas_simps` Command

A setup command for files that work with `getElem!` (bang-version of getElem). Common in cryptographic code where types are inhabited.

**What it does:**
1. Deactivates `simp` lemmas that turn `getElem!` into `getElem?`/`getD`
2. Locally activates lemmas that convert `getElem` to `getElem!` and `set` to `set!`
3. Deactivates `List.reduceReplicate` (causes blowups in crypto specs)
4. Deactivates `Bool.exists_bool` (problematic with existentially quantified booleans)

**Usage:** Put at the top of your proof file:
```lean
#setup_aeneas_simps
```

## Attribute Management

You can locally activate or deactivate attributes to control which specifications tactics use:

```lean
-- Disable default cast spec, use simpler version
attribute [-step] UScalar.cast.step_spec
attribute [local step] UScalar.cast_inBounds_spec

-- Add local simp lemmas
attribute [local simp] my_custom_lemma
attribute [local simp_scalar_simps] my_scalar_lemma
attribute [local simp_lists_simps] my_list_lemma
```

This is particularly useful when the default specification is more general than needed and the proof is easier with a specialized version.
