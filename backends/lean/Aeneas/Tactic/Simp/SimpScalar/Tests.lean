import Aeneas.Tactic.Simp.SimpScalar.Lemmas

/-!
# simp_scalar regression tests

Tests for `simp_scalar`: simplification and decision of Nat/Int scalar arithmetic
(div, mod, pow, testBit, shiftRight, etc.).
-/

/-! ## Basic arithmetic -/

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

/-! ## Mod / div -/

example (j : ℕ) (hj : j < 8) : j % 8 = j := by
  simp_scalar

example (i j : ℕ) (hj : j < 8) : (8 * i + j) / 8 = i := by
  simp_scalar

example (i j : ℕ) (hj : j < 8) : (8 * i + j) % 8 = j := by
  simp_scalar

example (a i : ℕ) (ha : 0 < a) : a * i / a = i := by
  simp_scalar

example (a b : ℕ) (hb : 0 < b) : (a - a % b) / b = a / b := by
  simp_scalar

example (a b : ℕ) (hb : 0 < b) (h : a % b = 0) : (a + b) / b = a / b + 1 := by
  simp_scalar

example (x n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hnm : n < m)
    (h1 : 2 < 2 ^ m) (h2 : 2 ^ n < 2 ^ m) (hx : x < 2 ^ m) :
    x % (2 ^ n % 2 ^ m) = x % 2 ^ n := by
  simp_scalar

example (d n i nbits : ℕ) (hdn : d < 8 * n) (hinv1 : 8 * nbits = d * i)
    (h : d * i % (8 * n) = 0) :
    8 * (nbits + n) = d * (i + 1) + (8 * n - min d (8 * n)) := by
  simp_scalar [mul_add]

/- Partial progress: leaves `n * (d * i / (8 * n)) + n = n * (d * i / (8 * n) + 1)` -/
/--
error: unsolved goals
bi n d i : ℕ
hn : 0 < n
hdn : d < 8 * n
hd : 0 < d
h2 : bi = n * (d * i / (8 * n))
hd2 : d * (i + 1) / (8 * n) = bi / n + 1
⊢ n * (d * i / (8 * n)) + n = n * (d * i / (8 * n) + 1)
-/
#guard_msgs in
example (bi n d i : ℕ) (hn : 0 < n) (hdn : d < 8 * n) (hd : 0 < d)
    (h2 : bi = n * (d * i / (8 * n)))
    (hd2 : d * (i + 1) / (8 * n) = bi / n + 1) :
    bi + n = n * (d * (i + 1) / (8 * n)) := by
  simp_scalar [hd2, h2]

/-! ## Power arithmetic -/

example (n : ℕ) (hn : 1 < n) : 2 < 2 ^ n := by
  simp_scalar

example (a b : ℕ) (hab : a < b) : 2 ^ a < 2 ^ b := by
  simp_scalar

example (k : ℕ) (hk : k < 8) (a : ℕ) :
    (decide (k < 8) && a.testBit k) = a.testBit k := by
  simp_scalar

/-! ## BitVec / testBit -/

example (x : BitVec 8) (j : ℕ) (hj : j ≥ 8) : x.toNat < 2 ^ j := by
  simp_scalar

example (j j' : ℕ) (hj : j < 8) (hj' : j ≤ j') (hj'' : j' < 8) :
    ((2 ^ j) >>> j).testBit (j' - j) = (2 ^ j).testBit j' := by
  simp_scalar

example (n m : ℕ) (h : n < m) : 2 ^ n % 2 ^ m = 2 ^ n := by
  simp_scalar
