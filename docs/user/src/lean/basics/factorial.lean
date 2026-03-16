import Base
import Mathlib.Data.Nat.Factorial.Basic

/-!

# Computing factorial

Test 1, test 2, test 3.

-/

open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace factorial

/- [factorial::factorial]:
   Source: 'src/factorial.rs', lines 1:0-1:27 -/
divergent def factorial (n : U64) : Result U64 :=
  if n = 0#u64
  then Result.ok 1#u64
  else do
       let i ← n - 1#u64
       let i1 ← factorial i
       n * i1

end factorial

/-!

We will need some lemmas on factorials lifted to ℤ and U64
to prove theorems about factorial.

This will be useful to introduce arithmetic work in Aeneas.

First, we would like to prove that the factorial of natural number as integers possess
the recursive property of factorials.
-/

lemma Int.mul_factorial_pred: ∀ {n: ℤ}, 0 < n → n * (n - 1).toNat.factorial = n.toNat.factorial := by
  intro n n_pos
  -- This is a generic tactic to lift types to another types while discharging conditions, e.g. positivity, etc.
  lift (n: ℤ) to ℕ
  -- `omega` is another generic tactic to close arithmetic goals automatically, `linarith` is another option
  -- for linear arithmetic.
  omega
  -- `simp` here is used as a normalization tactic, then we normalize the casts themselves
  -- and finally, we use the natural number version of the recursive property.
  -- `exact_mod_cast` is a "here's the term modulo casts" tactic.
  simp; norm_cast; exact Nat.mul_factorial_pred (by exact_mod_cast n_pos)


lemma U64.mul_factorial_pred: ∀ {n: U64}, 0#u64 < n → (n: ℤ) * (n.toNat - 1).factorial = n.toNat.factorial := by
  intro n n_pos
  -- `convert` is a "here's the term, please match it as much as you can and let me discharge the differences".
  convert (Int.mul_factorial_pred _)
  . simp
  . scalar_tac

/-!

We will need a mathematical theorem relating machine integers
as Rust cannot compute factorials larger than 2^64 - 1 using u64s.

As factorial is a nice function, i.e. is increasing, we can just reduce
the proof to proving that our domain's max value fits in a U64, i.e. 20! ≤ 2^64 - 1.

In Lean, certain goals can be "decided", e.g. we can just use a fast algorithm
to produce a proof certificate that something is true.
-/
theorem factorial_bounds: ∀ {n: ℕ}, n ≤ 20 → n.factorial ≤ U64.max := by
  intro n n_pos
  -- Our strategy will be to write this in ℕ to reuse natural number theorems.
  rw [U64.max]
  norm_cast
  -- We use transitivity of ≤ to use the natural number theorem _and_ decision.
  transitivity
  . exact Nat.factorial_le n_pos
  . decide

/-! 

We define a restricted scalar factorial to U64.
To construct a scalar, we need to prove that it fits both of the ends of the scalar.
For unsigned scalar, we only need to prove positivity _and_ it fits the max.

We leave the problem to `scalar_tac`, an Aeneas tactic that performs pre-processing step
and knows facts about scalars to discharge scalar-related goals. This tactic calls internally `omega`,
so it is _at least_ powerful as `omega`.

For the upper-bound, we reuse our just-proven theorem.
-/
def scalar_factorial {n: ℕ} (bounds: n ≤ 20): U64 :=
  Scalar.ofIntCore n.factorial ⟨ by scalar_tac, factorial_bounds bounds ⟩

/-!

We are ready to create the specification of factorial.

That is, under the precondition of having an integer smaller than 20, the Rust's extracted factorial function
coincides with the theoretical scalar factorial function lifted from the mathematical scalar factorial function.

Nonetheless, we will not be able to finish the formalization with the proposed signature.

`@[pspec]`, a decorator, marks the following theorem as a specification, which can be searched by Aeneas tactics on specifications.
-/

@[pspec]
theorem factorial_spec_mistaken: ∀ (n: ℕ), 
  (bounds: n ≤ 20) → 
  -- We cast the input natural number it in a scalar.
  factorial.factorial (Scalar.ofIntCore n ⟨ by scalar_tac, by scalar_tac ⟩) = Result.ok (scalar_factorial bounds)  := by
  intro n bounds
  -- We unfold the Rust definition.
  rw [factorial.factorial]
  -- Distinguish the trivial case and the complicated case.
  by_cases hzero : n = 0
  . 
    -- We let Lean reduce this to a trivial equation.
    simp [hzero, scalar_factorial]
  . 
    -- We simplify the branching using our negation hypothesis.
    simp [hzero]
    /-
      Here, we need to reuse a specification on scalar substraction regarding `n - 1`
      `k` will be the new integer in the context and `Hk` the term that links `k`
      to its value.
      This specification can be discovered automatically and pasted by `progress?`.
      `progress` is one of the Aeneas tactics on specifications.
    -/
    progress with Primitives.U64.sub_spec as ⟨ k, Hk ⟩
    -- We have a problem here, the goal ask us to reuse our specification
    -- but with a `k`, not with a `Scalar.ofIntCore ...`
    -- rw [Hk]
    -- progress with factorial_spec
    stop

/-!
In general, specifications in Aeneas are written with an existential-style, that is, we will write there's a result
to some operation and we will attach additional conditions to the value of the result.

This avoids to depend on things like proofs of boundness of a given scalar which could be arbitrary.

Here's a fixed proposal.
-/

@[pspec]
theorem factorial_spec: ∀ (n: U64), (bounds: n.val ≤ 20) → ∃ v, factorial.factorial n = Result.ok v ∧ v.val = n.val.toNat.factorial := by
  intro n bounds
  rw [factorial.factorial]
  by_cases hzero : n = 0#u64
  . 
    -- We let Lean reduce this to a trivial equation.
    simp [hzero, scalar_factorial]
  . 
    -- We simplify the branching using our negation hypothesis.
    simp [hzero]
    -- Here, we need to reuse a specification on scalar substraction regarding `n - 1`
    -- `k` will be the new integer in the context and `Hk` the term that links `k`
    -- to its value.
    -- This specification can be discovered automatically and pasted by `progress?`.
    progress with Primitives.U64.sub_spec as ⟨ k, Hk ⟩
    -- Here, we have the recursive call to `factorial`
    -- Lean will figure out automatically that calling ourselves with a smaller argument
    -- is sufficient to prove termination of this specification proof.
    progress with factorial_spec as ⟨ p, Hp ⟩
    -- We still need to prove that np is a valid U64 scalar
    -- and its value is what is expected.
    progress with Primitives.U64.mul_spec as ⟨ y, Hy ⟩
    -- We replace our collected equalities in the previous progresses.
    . 
      rw [Hp, Hk]
      -- We do various wrangling with the equalities to simplify
      -- their casts, their form, remove the definitions (U64.max).
      simp only [Scalar.ofInt_val_eq, Int.pred_toNat]
      -- We leave it to Aeneas automation to discharge the non-negativity of the scalar.
      rw [U64.mul_factorial_pred (by scalar_tac)]
      simp only [U64.toNat]
      -- Our original bound live in ℤ, we need it in ℕ, let's lift it quickly.
      have bounds' : n.toNat ≤ 20 := by {
        -- Let's lift the goal, i.e. the inequality in ℕ, to ℤ and conclude immediately.
        zify; simp [bounds]
      }
      exact factorial_bounds bounds'
    . rw [Hy, Hp, Hk]
      simp only [Scalar.ofInt_val_eq, Int.pred_toNat]
      rw [U64.mul_factorial_pred (by scalar_tac)]
-- We need to prove that we are calling the specification with a smaller scalar.
-- Let's prove it over the cast to natural numbers.
termination_by n => n.val.toNat
decreasing_by
  simp_wf -- We simplify the well-founded relation definition.
  rw [Hk] -- Inject the definition of `k`.
  simp -- Let a Lean tactic conclude trivially.
