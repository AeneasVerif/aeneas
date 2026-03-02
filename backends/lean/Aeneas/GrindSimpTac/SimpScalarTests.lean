import Aeneas.GrindSimpTac.SimpScalar
import Aeneas.ScalarTac.Lemmas

/-!
# Tests for `gsimp_scalar`

These mirror the examples from `Aeneas.SimpScalar.Tests`.
-/

example {n d} : n * (d / (8 * n)) = n * (d / 8 / n) := by
  gsimp_scalar

example (d k : ℕ) (hdn : d < k) :
  let nBits := d ⊓ k;
  2 < 2 ^ k → 2 ^ nBits < 2 ^ k := by
  intros nBits h
  gsimp_scalar

example (x y : ℕ) (h : x < y) : x < y := by gsimp_scalar

example (a b : ℕ) (h : a + 1 ≤ b) : a ≤ b := by gsimp_scalar

example (a b : ℕ) (h : a + 1 ≤ b) : a > b → False := by gsimp_scalar
