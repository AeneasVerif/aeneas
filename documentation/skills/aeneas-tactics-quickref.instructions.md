# Aeneas Tactics Quick Reference

## Decision Tree: Which Tactic?

**PREREQUISITE:** Always use `lean_lsp.py --repl --json` for interactive proof development. Use `goal <line>` to inspect the proof state before choosing a tactic. See the `lean-lsp-tool` skill file.

```
What does the goal look like?

├─ Monadic function call (let x ← f args; ...)
│  → progress / progress* / progress with <thm>
│
├─ Loop fixed-point (loop body x)
│  → apply loop.spec_decr_nat (Nat measure) or loop.spec (general)
│
├─ Recursive _loop function
│  → unfold + split + progress (invariant = pre + post), termination_by + scalar_decr_tac
│
├─ Arithmetic
│  ├─ Any with UScalar/IScalar → scalar_tac (NEVER omega)
│  ├─ Linear Nat/Int only → scalar_tac (NEVER omega)
│  ├─ Nonlinear → scalar_tac +nonLin
│  └─ Scalar simplification (min, max, %) → simp_scalar
│
├─ Bit-vector / Bitwise
│  ├─ **Always use `bv_tac N` for bitwise ops** (&&&, |||, ^^^, ~~~, >>>, <<<, %)
│  ├─ Pure BitVec goal → bv_tac N
│  ├─ Nat goal about bitwise result → bvify N; bv_tac N
│  ├─ bvify fails → have h : bv_prop := by bv_tac N; natify at h; simp_scalar
│  └─ bv_tac error shows non-decomposed expr (e.g. `(x &&& y).bv`) → missing @[bvify_simps] lemma
│
├─ Modular arithmetic
│  ├─ Equivalence (a ≡ b [MOD n]) → zmodify; ring / simp
│  └─ Bounds (a < n) → stay Nat/Int; scalar_tac / agrind
│
├─ List/Array (get/set)
│  ├─ Automatic → agrind first; if fails, try grind (slower, more list lemmas)
│  └─ Slow → cases idx <;> simp_lists [*]
│
├─ Slice/List getElem mismatch
│  ├─ Use #setup_aeneas_simps at file top (auto-converts getElem → getElem!)
│  ├─ Manual bridge → List.Inhabited_getElem_eq_getElem! s.val i proof
│  └─ Slice getElem! → List getElem! → rw [Slice.getElem!_Nat_eq]
│
├─ If-then-else → simp_ifs / split
├─ Conjunction (∧) → split_conjs <;> agrind
├─ Boolean/Propositional → simp_bool_prop / tauto
├─ Concrete computation → decide / native_decide
├─ Congruence → fcongr
│
└─ General / stuck
   ├─ Try → agrind
   └─ If fails → simp [*]; agrind
```

## Tactic Reference Table

### Aeneas-Specific Tactics

| Tactic | Purpose | Syntax | Key Attributes |
|---|---|---|---|
| `progress` | Apply function spec | `progress`, `progress as ⟨x,h⟩`, `progress with thm` | `@[progress]` |
| `progress*` | Repeat progress + case split | `progress*`, `progress* n` (n steps) | Use for final compact proof |
| `progress*?` | Generate proof script | `progress*?` | Start here when developing proofs |
| `scalar_tac` | Integer arithmetic/bounds | `scalar_tac`, `scalar_tac +nonLin` | `@[scalar_tac_simps]` |
| `simp_scalar` | Simplify scalar exprs | `simp_scalar`, `simp_scalar [lemmas]` | `@[simp_scalar_simps]` |
| `simp_lists` | Simplify list get/set | `simp_lists`, `simp_lists [lemmas]` | `@[simp_lists_simps]` |
| `bvify` | Lift to BitVec | `bvify N`, `bvify N at h` | `@[bvify_simps]` |
| `bv_tac` | Decide BitVec goals | `bv_tac N` | — |
| `natify` | Convert to Nat | `natify`, `natify at h` | `@[natify_simps]` |
| `zmodify` | Convert to ZMod | `zmodify`, `zmodify [to N]`, `zmodify at h` | `@[zmodify_simps]` |
| `simp_ifs` | Simplify if-then-else | `simp_ifs` | — |
| `simp_bool_prop` | Bool/prop simplification | `simp_bool_prop` | `@[simp_bool_prop_simps]` |
| `fcongr` | Congruence (safe whnf) | `fcongr`, `fcongr N` | — |
| `split_conjs` | Split nested ∧ | `split_conjs`, `split_conjs at h` | — |

### Commonly Used Lean Builtins

| Tactic | Purpose | Notes |
|---|---|---|
| `agrind` | General automation | Prefer over `grind` — faster. If it fails, try `grind` |
| `omega` | **NEVER use** — use `scalar_tac`, `agrind`, or `grind` instead |
| `simp` / `simp [*]` | Simplification | Use `simp [*]` to keep hypotheses |
| `simp_all` | Aggressive simplification | **Caution:** may remove needed hypotheses |
| `tauto` | Propositional tautologies | |
| `decide` | Concrete decidable goals | |
| `ring` | Ring equalities | |
| `split` | Case-split match/if | |
| `cases` | Structural case analysis | |

## Common Tactic Combinations

| Pattern | Use When |
|---|---|
| `split_conjs <;> agrind` | Goal is a conjunction |
| `simp [*]; agrind` | `agrind` alone fails (grind issue workaround) |
| `progress* <;> bv_tac 32` | Monadic code with bitwise ops |
| `bvify N; bv_tac N` | Nat goal about bitwise operation |
| `have h := ...; natify at h; simp_scalar at h` | Reverse bv lifting (goal → bv → back to Nat) |
| `zify at h; zify; simp [h, Int.mul_emod]` | Modular equivalence via Int |
| `unfold fn; split; progress` | Recursive function (avoid termination issue) |
| chain of `have` + `simp_scalar` | Non-linear arithmetic (modulo, division) |
| `calc _ = _ := by simp_scalar` | Equational chains for arithmetic |

## Proof Style Rules

- **Remove unused simp lemmas** when warned — don't leave dead arguments
- **No big `simp only [...]` in implementation proofs** — model names are unstable. Use `simp [*]` or targeted rewrites. (OK in spec lemmas.)
- **Extract complex sub-proofs** as auxiliary lemmas — don't inline 15 lines of arithmetic inside `progress*`
- **Simplify shifts early**: rewrite `>>>` as `/ 2^n`, `<<<` as `* 2^n`

## Attribute Management Cheatsheet

```lean
-- Setup for crypto/array proofs
#setup_aeneas_simps

-- Swap to simpler cast spec
attribute [-progress] UScalar.cast.progress_spec
attribute [local progress] UScalar.cast_inBounds_spec

-- Register lemma for specific tactic
attribute [local simp_scalar_simps] my_lemma
attribute [local simp_lists_simps] my_lemma
attribute [local agrind] my_lemma

-- Register constant for all tactics
@[simp, scalar_tac_simps, bvify_simps, agrind =]
theorem MY_CONST_val : MY_CONST.val = 42 := by decide
```

**Safety:** simp_scalar/simp_lists are simp-based. Activating many local lemmas is safe (no complexity explosion).

## Key Lemmas Reference

| Lemma | Statement | Use Case |
|---|---|---|
| `WP.spec_ok` | `spec (ok x) p ↔ p x` | Proving `@[progress]` for constants that reduce to `ok v` |
| `bind_assoc_eq` | `(x >>= f) >>= g = x >>= (λ a => f a >>= g)` | Fold theorem proofs (reassociate binds) |
| `bind_tc_ok` | `(do let y ← .ok x; f y) = f x` | Fold theorem proofs (eliminate trivial ok binds) |
| `Slice.Inhabited_getElem_eq_getElem!` | `s[i] = s[i]!` for Slice | Bridge proof-based → default-based access |
| `Slice.getElem!_Nat_eq` | `s[i]! = s.val[i]!` | Bridge Slice getElem! → List getElem! |
| `List.Inhabited_getElem_eq_getElem!` | `l[i] = l[i]!` for List | Bridge proof-based → default-based access |

## Critical Pitfalls

| Pitfall | Symptom | Fix |
|---|---|---|
| Recursive progress | Termination error after unfold+progress | `split` before `progress` |
| Nat subtraction | Spec is wrong (truncated at 0) | Use Int, add `h : a ≥ b`, or rewrite as addition |
| `simp_all` drops hyps | Needed hypothesis gone | Use `simp [*]` or `simp [h1,h2]` |
| `grind` explodes | Timeout | Use `agrind` instead |
| `agrind` fails | Goal unsolved | Try `simp [*]; agrind` |
| Wrong progress spec | Unexpected behavior | `progress with specific_thm` |

## Debugging Commands

```lean
set_option trace.progress true        -- trace progress decisions
set_option trace.scalar_tac true      -- trace scalar_tac
set_option trace.Aeneas.progress true -- detailed progress
set_option maxHeartbeats 5000000      -- increase timeout (last resort)
set_option maxRecDepth 2048           -- increase recursion depth
```
