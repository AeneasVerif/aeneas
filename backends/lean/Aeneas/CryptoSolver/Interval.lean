import Aeneas.CryptoSolver.Init

/-!
# Interval arithmetic for CryptoSolver

Pure computational interval type used for meta-level bounds analysis.
All operations are conservative (sound over-approximations).
-/

namespace Aeneas.CryptoSolver

/-- A closed interval [lo, hi] over integers.
    Used at the meta level for bounds propagation. -/
structure Interval where
  lo : Int
  hi : Int
  deriving Repr, Inhabited, BEq

namespace Interval

/-- Maximally conservative interval (unknown bounds) -/
def top : Interval := ⟨Int.negSucc (2^63 - 1), (2^63 : Int)⟩

/-- Singleton interval -/
def singleton (n : Int) : Interval := ⟨n, n⟩

/-- Non-negative interval [0, hi] -/
def nonneg (hi : Int) : Interval := ⟨0, hi⟩

/-- Is the entire interval non-negative? -/
def isNonneg (i : Interval) : Bool := i.lo ≥ 0

/-- Is this the top (unknown) interval? -/
def isTop (i : Interval) : Bool := i.lo ≤ Int.negSucc (2^62) && i.hi ≥ (2^62 : Int)

/-- Is this interval well-formed (lo ≤ hi)? -/
def wf (i : Interval) : Bool := i.lo ≤ i.hi

/-- Interval addition -/
def add (a b : Interval) : Interval := ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- Interval subtraction -/
def sub (a b : Interval) : Interval := ⟨a.lo - b.hi, a.hi - b.lo⟩

/-- Interval negation -/
def neg (a : Interval) : Interval := ⟨-a.hi, -a.lo⟩

/-- Interval multiplication.
    For non-negative operands: [a.lo*b.lo, a.hi*b.hi].
    Otherwise: 4-corner analysis. -/
def mul (a b : Interval) : Interval :=
  if a.isNonneg && b.isNonneg then
    ⟨a.lo * b.lo, a.hi * b.hi⟩
  else if a.hi ≤ 0 && b.hi ≤ 0 then
    -- Both non-positive: lo*lo and hi*hi swap
    ⟨a.hi * b.hi, a.lo * b.lo⟩
  else
    -- General case: all four corners
    let c1 := a.lo * b.lo
    let c2 := a.lo * b.hi
    let c3 := a.hi * b.lo
    let c4 := a.hi * b.hi
    ⟨min (min c1 c2) (min c3 c4), max (max c1 c2) (max c3 c4)⟩

/-- Interval division (integer division, rounds toward zero).
    Conservative when divisor may contain zero. -/
def div (a b : Interval) : Interval :=
  if b.lo > 0 then
    -- Positive divisor
    if a.isNonneg then
      ⟨a.lo / b.hi, a.hi / b.lo⟩
    else if a.hi ≤ 0 then
      ⟨a.lo / b.lo, a.hi / b.hi⟩
    else
      ⟨a.lo / b.lo, a.hi / b.lo⟩
  else if b.hi < 0 then
    -- Negative divisor
    if a.isNonneg then
      ⟨a.hi / b.hi, a.lo / b.lo⟩
    else if a.hi ≤ 0 then
      ⟨a.hi / b.lo, a.lo / b.hi⟩
    else
      ⟨a.hi / b.hi, a.lo / b.hi⟩
  else
    top

/-- Interval modulo.
    For positive modulus m: result ∈ [0, m-1]. -/
def mod (a b : Interval) : Interval :=
  if b.lo > 0 then
    if a.isNonneg then
      ⟨0, min a.hi (b.hi - 1)⟩
    else
      ⟨max a.lo (1 - b.hi), min a.hi (b.hi - 1)⟩
  else
    top

/-- Interval exponentiation by literal exponent -/
def pow (a : Interval) (n : Nat) : Interval :=
  if n = 0 then singleton 1
  else if a.isNonneg then
    ⟨a.lo ^ n, a.hi ^ n⟩
  else if n % 2 = 0 then
    -- Even power: result is non-negative
    if a.hi ≤ 0 then
      ⟨a.hi ^ n, a.lo ^ n⟩
    else
      -- Mixed sign: 0 is in [lo, hi], minimum is 0
      ⟨0, max (a.lo ^ n) (a.hi ^ n)⟩
  else
    -- Odd power, mixed sign
    ⟨a.lo ^ n, a.hi ^ n⟩

/-- Interval left shift by constant -/
def shl (a : Interval) (n : Nat) : Interval :=
  let factor := (2 : Int) ^ n
  ⟨a.lo * factor, a.hi * factor⟩

/-- Interval right shift by constant (arithmetic shift for non-negative) -/
def shr (a : Interval) (n : Nat) : Interval :=
  let factor := (2 : Int) ^ n
  if a.isNonneg then
    ⟨a.lo / factor, a.hi / factor⟩
  else
    top

/-- Interval bitwise AND (conservative: result ∈ [0, min(a.hi, b.hi)]).
    Only meaningful for non-negative operands. -/
def band (a b : Interval) : Interval :=
  if a.isNonneg && b.isNonneg then
    ⟨0, min a.hi b.hi⟩
  else
    top

/-- Interval bitwise OR (conservative).
    Only meaningful for non-negative operands. -/
def bor (a b : Interval) : Interval :=
  if a.isNonneg && b.isNonneg then
    -- OR can only set bits, so result ≤ nextPow2(max) - 1
    -- Conservative: use a.hi + b.hi as upper bound
    ⟨max a.lo b.lo, a.hi + b.hi⟩
  else
    top

/-- Interval bitwise XOR (conservative).
    Only meaningful for non-negative operands. -/
def bxor (a b : Interval) : Interval :=
  if a.isNonneg && b.isNonneg then
    ⟨0, a.hi + b.hi⟩
  else
    top

/-- Intersect two intervals (tighten bounds) -/
def inter (a b : Interval) : Interval :=
  ⟨max a.lo b.lo, min a.hi b.hi⟩

/-- Does `other` fit entirely within `self`? -/
def contains (self other : Interval) : Bool :=
  self.lo ≤ other.lo && other.hi ≤ self.hi

end Interval

end Aeneas.CryptoSolver
