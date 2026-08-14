import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Algebra.Order.Floor.Div

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Ceiling division: Definitions

`n.div_ceil(m)` ≡ `⌈n / m⌉`, panicking on `m = 0`.

Rust computes this without overflow as (`library/core/src/num/uint_macros.rs`)
```
let d = self / rhs;
let r = self % rhs;
if r > 0 { d + 1 } else { d }
```
On `Nat` the ceiling `n ⌈/⌉ m` agrees with that result and never leaves the range
(`n ⌈/⌉ m ≤ n`), so we model the operation directly, mirroring the shape of `div`.
The only failure is division by zero, matching the panic of `self / rhs`.
-/

def UScalar.div_ceil {ty : UScalarTy} (n m : UScalar ty) : Result (UScalar ty) :=
  if h : m.val ≠ 0 then
    ok (UScalar.ofNatCore (n.val ⌈/⌉ m.val) (by
      have hle : n.val ⌈/⌉ m.val ≤ n.val := by
        rw [ceilDiv_le_iff_le_mul (by scalar_tac)]
        exact Nat.le_mul_of_pos_left n.val (by scalar_tac)
      have := n.hBounds
      scalar_tac))
  else fail divisionByZero

@[rust_fun "core::num::{u8}::div_ceil"]
def core.num.U8.div_ceil (n m : U8) : Result U8 := UScalar.div_ceil n m

@[rust_fun "core::num::{u16}::div_ceil"]
def core.num.U16.div_ceil (n m : U16) : Result U16 := UScalar.div_ceil n m

@[rust_fun "core::num::{u32}::div_ceil"]
def core.num.U32.div_ceil (n m : U32) : Result U32 := UScalar.div_ceil n m

@[rust_fun "core::num::{u64}::div_ceil"]
def core.num.U64.div_ceil (n m : U64) : Result U64 := UScalar.div_ceil n m

@[rust_fun "core::num::{u128}::div_ceil"]
def core.num.U128.div_ceil (n m : U128) : Result U128 := UScalar.div_ceil n m

@[rust_fun "core::num::{usize}::div_ceil"]
def core.num.Usize.div_ceil (n m : Usize) : Result Usize := UScalar.div_ceil n m

/-!
# Sanity Checks

Ground-truth checks that the model agrees with Rust's `u32::div_ceil` on concrete
inputs, including the exact-multiple, off-by-one, divisor-larger-than-dividend, and
`div_ceil(0, m) = 0` boundary cases.
-/

namespace Tests
  #assert (7 : Nat) ⌈/⌉ 3 = 3     -- 7.div_ceil(3) == 3
  #assert (9 : Nat) ⌈/⌉ 3 = 3     -- exact multiple
  #assert (1 : Nat) ⌈/⌉ 3 = 1     -- divisor larger than dividend
  #assert (0 : Nat) ⌈/⌉ 5 = 0     -- zero dividend
  #assert (256 : Nat) ⌈/⌉ 7 = 37  -- to_radix_2w_size_hint shape (w = 7)
end Tests

/-!
# Ceiling division: Theorems
-/

@[step]
theorem UScalar.div_ceil_spec {ty : UScalarTy} (n : UScalar ty) {m : UScalar ty}
    (hnz : m.val ≠ 0) :
    UScalar.div_ceil n m ⦃ (r : UScalar ty) => r.val = n.val ⌈/⌉ m.val ⦄ := by
  have hle : n.val ⌈/⌉ m.val ≤ n.val := by
    rw [ceilDiv_le_iff_le_mul (by scalar_tac)]
    exact Nat.le_mul_of_pos_left n.val (by scalar_tac)
  have := n.hBounds
  simp only [div_ceil, hnz, ne_eq, not_false_eq_true, ↓reduceDIte, spec_ok,
    UScalar.ofNatCore_val_eq]

uscalar @[step] theorem core.num.«%S».div_ceil_spec (n : «%S») {m : «%S»}
    (hnz : m.val ≠ 0) :
    core.num.«%S».div_ceil n m ⦃ (r : «%S») => r.val = n.val ⌈/⌉ m.val ⦄ :=
  UScalar.div_ceil_spec n hnz

/-- `div_ceil` fails (with `divisionByZero`) exactly when the divisor is zero,
matching the panic of the underlying Rust division. -/
theorem UScalar.div_ceil_divisionByZero {ty : UScalarTy} (n m : UScalar ty)
    (hz : m.val = 0) :
    UScalar.div_ceil n m = fail divisionByZero := by
  simp only [div_ceil, hz, ne_eq, not_true_eq_false, ↓reduceDIte]

end Aeneas.Std
