import Aeneas.CryptoSolver

namespace Aeneas.CryptoSolver.Tests

/-! ### Basic arithmetic bounds -/

-- Simple linear: omega should handle this
example (x : Nat) (h : x < 100) : x < 200 := by crypto_solver

-- Nat multiplication bounds: the core use case
example (x y : Nat) (hx : x < 2^32) (hy : y < 2^32) : x * y < 2^64 := by
  crypto_solver

/-! ### Asymmetric bounds (crypto limb sizes) -/

-- 52-bit × 62-bit → fits in 114 bits (Curve25519 limb multiply pattern)
example (a b : Nat) (ha : a < 2^52) (hb : b < 2^62) : a * b < 2^114 := by
  crypto_solver

/-! ### Three-way products -/

-- Three bounded values multiplied together
example (x y z : Nat) (hx : x < 2^16) (hy : y < 2^16) (hz : z < 2^16) :
    x * y * z < 2^48 := by
  crypto_solver

/-! ### Sum of products (schoolbook multiply column) -/

-- Sum of 5 products of 52-bit values: appears in Curve25519 schoolbook mul
example (a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 : Nat)
    (ha0 : a0 < 2^52) (hb0 : b0 < 2^52)
    (ha1 : a1 < 2^52) (hb1 : b1 < 2^52)
    (ha2 : a2 < 2^52) (hb2 : b2 < 2^52)
    (ha3 : a3 < 2^52) (hb3 : b3 < 2^52)
    (ha4 : a4 < 2^52) (hb4 : b4 < 2^52) :
    a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4 < 5 * 2^104 := by
  crypto_solver

/-! ### Widening multiplication -/

-- 32-bit × 32-bit → 64-bit
example (x y : Nat) (hx : x < 2^32) (hy : y < 2^32) : x * y < 2^64 := by
  crypto_solver

-- 64-bit × 64-bit → 128-bit
example (x y : Nat) (hx : x < 2^64) (hy : y < 2^64) : x * y < 2^128 := by
  crypto_solver

/-! ### Division and modular reduction -/

-- Division reduces bit width
example (x : Nat) (hx : x < 2^64) : x / 2^32 < 2^32 := by
  crypto_solver

-- Mod produces bounded result
example (x : Nat) (hx : x < 2^64) : x % 2^32 < 2^32 := by
  crypto_solver

/-! ### Int (signed) arithmetic -/

-- Signed multiplication bounds
-- With x ∈ [-2^31, 2^31) and y ∈ [-2^31, 2^31), max product is 2^62 (at x=y=-2^31)
example (x y : Int) (hx1 : -2^31 ≤ x) (hx2 : x < 2^31)
    (hy1 : -2^31 ≤ y) (hy2 : y < 2^31) :
    -(2^62) < x * y ∧ x * y ≤ 2^62 := by
  crypto_solver

/-! ### Conjunction splitting -/

-- Both bounds in one goal
example (x y : Nat) (hx : x < 2^32) (hy : y < 2^32) :
    x * y < 2^64 ∧ x + y < 2^33 := by
  crypto_solver

/-! ### Barrett reduction approximation -/

-- Core Barrett estimate: a % n < n when n > 0
example (a n : Nat) (hn : 0 < n) (ha : a < n * n) :
    a % n < n := by crypto_solver

-- Division bound: if a < 2^64 then a / 2^32 < 2^32
example (a : Nat) (ha : a < 2^64) : a / 2^32 < 2^32 := by
  crypto_solver

-- Multiply-high pattern: (a * b) / 2^64 where a, b < 2^64
-- This needs nlinarith to establish a*b < 2^128, then omega for division
example (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    a * b / 2^64 < 2^64 := by
  crypto_solver

/-! ### Carry propagation -/

-- After add with carry: if a, b < 2^64 then a + b < 2^65
example (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    a + b < 2^65 := by
  crypto_solver

-- Extract carry and remainder
example (x : Nat) (hx : x < 2^65) :
    x % 2^64 < 2^64 ∧ x / 2^64 < 2 := by
  crypto_solver

end Aeneas.CryptoSolver.Tests

/-! ## Advanced crypto patterns -/

namespace Aeneas.CryptoSolver.AdvancedTests

/-! ### Four-way product (schoolbook column accumulator) -/

example (a b c d : Nat) (ha : a < 2^16) (hb : b < 2^16) (hc : c < 2^16) (hd : d < 2^16) :
    a * b * c * d < 2^64 := by
  crypto_solver

/-! ### Curve25519-style 5-limb product column -/

-- Product of two 51-bit limbs plus product of two 51-bit limbs (two terms in a column)
example (a0 b4 a1 b3 : Nat)
    (ha0 : a0 < 2^51) (hb4 : b4 < 2^51)
    (ha1 : a1 < 2^51) (hb3 : b3 < 2^51) :
    a0 * b4 + a1 * b3 < 2^103 := by
  crypto_solver

/-! ### Montgomery reduction: quotient estimate bound -/

-- q = (lo * n_inv) % 2^64, so q < 2^64
-- then q * n < 2^64 * n for any n
example (q n : Nat) (hq : q < 2^64) (hn : n < 2^64) :
    q * n < 2^128 := by
  crypto_solver

/-! ### Barrett reduction: approximate quotient -/

-- Barrett quotient: q = a * m / 2^(2k) where m ≈ 2^(2k) / n
-- When a < n^2 and m < 2^(2k+1)/n, the quotient is close to a/n
example (a m k : Nat) (ha : a < 2^64) (hm : m < 2^64) :
    a * m / 2^64 < 2^64 := by
  crypto_solver

/-! ### NTT butterfly: addition/subtraction modular bounds -/

-- After NTT butterfly: if a, b < q then (a + b) % q < q
example (a b q : Nat) (ha : a < q) (hb : b < q) (hq : 0 < q) :
    (a + b) % q < q := by
  crypto_solver

-- Subtraction variant with wrap-around: (a + q - b) % q < q
example (a b q : Nat) (ha : a < q) (hb : b < q) (hq : 0 < q) :
    (a + q - b) % q < q := by
  crypto_solver

/-! ### ML-KEM/Kyber specific: coefficient in range -/

-- After Barrett reduction: result < 2q for q = 3329
example (x : Nat) (hx : x < 2 * 3329) :
    x % 3329 < 3329 := by
  crypto_solver

/-! ### Carry chain: multi-limb addition -/

-- Three-limb addition with carries
example (a0 a1 a2 b0 b1 b2 : Nat)
    (ha0 : a0 < 2^64) (ha1 : a1 < 2^64) (ha2 : a2 < 2^64)
    (hb0 : b0 < 2^64) (hb1 : b1 < 2^64) (hb2 : b2 < 2^64) :
    a0 + b0 < 2^65 ∧ a1 + b1 < 2^65 ∧ a2 + b2 < 2^65 := by
  crypto_solver

/-! ### Division with remainder -/

-- Standard division bound: Nat.div_mul_le_self
example (a d : Nat) (hd : 0 < d) (ha : a < 2^64) :
    a / d * d ≤ a := by
  crypto_solver

/-! ### Nested multiplication + division -/

-- (a * b / 2^32) * c / 2^32 < 2^32 when a, b, c < 2^32
-- This requires multi-level bound introduction
set_option maxHeartbeats 400000 in
example (a b c : Nat) (ha : a < 2^32) (hb : b < 2^32) (hc : c < 2^32) :
    (a * b / 2^32) * c / 2^32 < 2^32 := by
  crypto_solver

end Aeneas.CryptoSolver.AdvancedTests

/-! ## Bitwise operation tests -/

namespace Aeneas.CryptoSolver.BitwiseTests

/-! ### Masking (AND with power-of-2 minus 1) -/

-- Basic mask: x &&& 0xFF < 256
example (x : Nat) : x &&& 0xFF < 256 := by crypto_solver

-- 32-bit mask
example (x : Nat) : x &&& (2^32 - 1) < 2^32 := by crypto_solver

-- AND is bounded by right operand
example (x y : Nat) (hy : y < 2^16) : x &&& y < 2^16 := by crypto_solver

/-! ### Shift operations -/

-- Right shift reduces bit width
example (x : Nat) (hx : x < 2^64) : x >>> 32 < 2^32 := by crypto_solver

-- Right shift reduces value
example (x : Nat) (hx : x < 2^64) : x >>> 16 < 2^48 := by crypto_solver

-- Left shift preserves bound (expressed as multiplication)
example (x : Nat) (hx : x < 2^16) : x <<< 8 < 2^24 := by crypto_solver

/-! ### Limb extraction patterns -/

-- Extract low 52 bits (Curve25519 limb extraction)
example (x : Nat) : x &&& (2^52 - 1) < 2^52 := by crypto_solver

-- Extract carry from addition
example (x : Nat) (hx : x < 2^65) : x >>> 64 < 2 := by crypto_solver

/-! ### Combined bitwise + arithmetic -/

-- After extracting a 32-bit limb, its product with another 32-bit value fits in 64 bits
set_option maxHeartbeats 400000 in
example (x y : Nat) (hx : x < 2^64) (hy : y < 2^32) :
    (x &&& (2^32 - 1)) * y < 2^64 := by crypto_solver

-- Shift-and-mask extraction: (x >>> 32) &&& (2^32 - 1)
-- After shift, x >>> 32 < 2^32 (when x < 2^64), so the mask is identity
example (x : Nat) (hx : x < 2^64) : (x >>> 32) &&& (2^32 - 1) < 2^32 := by
  crypto_solver

/-! ### Carry chain with shifts -/

-- Sum fits in 65 bits, carry is 1 bit
example (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    (a + b) >>> 64 < 2 := by crypto_solver

end Aeneas.CryptoSolver.BitwiseTests

/-! ## Additional regression and crypto tests -/

namespace Aeneas.CryptoSolver.CryptoTests

/-! ### Single-level div bound -/

-- a * b / 2^32 < 2^32, the inner step of nested div
set_option maxHeartbeats 400000 in
example (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    a * b / 2^32 < 2^32 := by crypto_solver

/-! ### Three-limb chain -/

-- Three levels of mul+div representing a carry chain
set_option maxHeartbeats 800000 in
example (a b c d : Nat) (ha : a < 2^32) (hb : b < 2^32)
    (hc : c < 2^32) (hd : d < 2^32) :
    ((a * b / 2^32) * c / 2^32) * d / 2^32 < 2^32 := by crypto_solver

/-! ### Widening multiplication patterns -/

-- 32-bit × 32-bit fits in 64 bits
example (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    a * b < 2^64 := by crypto_solver

-- 52-bit × 52-bit fits in 104 bits (Curve25519 limb multiply)
example (a b : Nat) (ha : a < 2^52) (hb : b < 2^52) :
    a * b < 2^104 := by crypto_solver

-- 64-bit × 64-bit fits in 128 bits
example (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    a * b < 2^128 := by crypto_solver

/-! ### Accumulation patterns (sums of products) -/

-- Sum of two 64-bit products fits in 129 bits
example (a b c d : Nat) (ha : a < 2^64) (hb : b < 2^64)
    (hc : c < 2^64) (hd : d < 2^64) :
    a * b + c * d < 2^129 := by crypto_solver

/-! ### Modular arithmetic -/

-- Modulo produces smaller value
example (x n : Nat) (hn : 0 < n) : x % n < n := by crypto_solver

-- Modulo is bounded by the modulus minus 1
example (x : Nat) : x % 2^32 < 2^32 := by crypto_solver

end Aeneas.CryptoSolver.CryptoTests
