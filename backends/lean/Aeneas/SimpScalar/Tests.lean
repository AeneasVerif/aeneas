import Aeneas.SimpScalar.SimpScalar

example {n d} : n * (d / (8 * n)) = n * (d / 8 / n) := by
  simp_scalar

example (d k : ℕ) (hdn : d < k) :
  let nBits := d ⊓ k;
  2 < 2 ^ k → 2 ^ nBits < 2 ^ k := by
  intros nBits h
  simp_scalar

example (x y : ℕ) (h : x < y) : x < y := by simp_scalar

example (a b : ℕ) (h : a + 1 ≤ b) : a ≤ b := by simp_scalar

example (a b : ℕ) (h : a + 1 ≤ b) : a > b → False := by simp_scalar
