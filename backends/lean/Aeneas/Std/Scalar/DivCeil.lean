module
public import Aeneas.Std.Scalar.Core
public meta import Aeneas.Std.Scalar.Core -- for the `#guard`s
public import Aeneas.Std.Scalar.Elab
import Aeneas.Std.Scalar.Notations -- for the `#guard`s
public section

namespace Aeneas.Std

open Result Error ScalarElab

/-! ## `{u8,u16,...}::div_ceil`

Rust defines `div_ceil` on the unsigned integers only
(<https://doc.rust-lang.org/std/primitive.usize.html#method.div_ceil>). The implementation
(`library/core/src/num/uint_macros.rs`) is:
```rust
pub const fn div_ceil(self, rhs: Self) -> Self {
    let d = self / rhs;
    let r = self % rhs;
    if r > 0 { d + 1 } else { d }
}
```
It panics when `rhs == 0` (the division panics) and can't overflow: the result is at most
`self`. -/

/-- `(x + y - 1) / y` is at most `x` when `y ≠ 0`, so the result of `div_ceil` always fits in
    the type of its arguments. -/
theorem UScalar.div_ceil_le {x y : Nat} (hy : 0 < y) : (x + y - 1) / y ≤ x := by
  have h1 : x ≤ x * y := Nat.le_mul_of_pos_right x hy
  have : (x + y - 1) / y < x + 1 := by
    rw [Nat.div_lt_iff_lt_mul hy, Nat.add_mul]
    omega
  omega

@[expose] def UScalar.div_ceil {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if h : y.val = 0 then fail divisionByZero
  else ok (UScalar.ofNatCore ((x.val + y.val - 1) / y.val)
    (Nat.lt_of_le_of_lt (UScalar.div_ceil_le (by omega)) x.hBounds))

@[expose, rust_fun "core::num::{u8}::div_ceil"]
def core.num.U8.div_ceil (x y : U8) : Result U8 := UScalar.div_ceil x y

@[expose, rust_fun "core::num::{u16}::div_ceil"]
def core.num.U16.div_ceil (x y : U16) : Result U16 := UScalar.div_ceil x y

@[expose, rust_fun "core::num::{u32}::div_ceil"]
def core.num.U32.div_ceil (x y : U32) : Result U32 := UScalar.div_ceil x y

@[expose, rust_fun "core::num::{u64}::div_ceil"]
def core.num.U64.div_ceil (x y : U64) : Result U64 := UScalar.div_ceil x y

@[expose, rust_fun "core::num::{u128}::div_ceil"]
def core.num.U128.div_ceil (x y : U128) : Result U128 := UScalar.div_ceil x y

@[expose, rust_fun "core::num::{usize}::div_ceil"]
def core.num.Usize.div_ceil (x y : Usize) : Result Usize := UScalar.div_ceil x y

/- Sanity checks against Rust -/
#guard (core.num.U8.div_ceil 7#u8 2#u8).reducesTo 4#u8       -- assert_eq!(7u8.div_ceil(2), 4);
#guard (core.num.U8.div_ceil 8#u8 2#u8).reducesTo 4#u8       -- assert_eq!(8u8.div_ceil(2), 4);
#guard (core.num.U8.div_ceil 0#u8 5#u8).reducesTo 0#u8       -- assert_eq!(0u8.div_ceil(5), 0);
#guard (core.num.U8.div_ceil 255#u8 1#u8).reducesTo 255#u8   -- assert_eq!(255u8.div_ceil(1), 255);
#guard (core.num.U8.div_ceil 255#u8 2#u8).reducesTo 128#u8   -- assert_eq!(255u8.div_ceil(2), 128);
#guard (core.num.U8.div_ceil 255#u8 255#u8).reducesTo 1#u8   -- assert_eq!(255u8.div_ceil(255), 1);
-- 1u8.div_ceil(0) panics (`div_ceil_zero` shows the model fails with `divisionByZero`)
#guard !((core.num.U8.div_ceil 1#u8 0#u8).match matches .ok _)

/-- `div_ceil` fails when the divisor is zero, where Rust panics (`UScalar.div_ceil.spec` shows it
    succeeds otherwise). -/
theorem UScalar.div_ceil_zero {ty : UScalarTy} (x y : UScalar ty) (hy : y.val = 0) :
    UScalar.div_ceil x y = fail divisionByZero := by
  simp [UScalar.div_ceil, hy]

/-- The value computed by `div_ceil` is the ceiling of `x / y`, as documented for Rust's
    `div_ceil`: the unique `z` with `x ≤ z * y < x + y`. This ties the formula used in the
    model to Rust's definition. -/
theorem UScalar.div_ceil_is_ceil {x y : Nat} (hy : 0 < y) :
    x ≤ (x + y - 1) / y * y ∧ (x + y - 1) / y * y < x + y := by
  have hmod := Nat.mod_lt (x + y - 1) hy
  have hdiv := Nat.div_add_mod (x + y - 1) y
  rw [Nat.mul_comm] at hdiv
  constructor <;> omega

/-- **Spec theorem for `div_ceil`**, for every unsigned width: the result is `(x + y - 1) / y`,
    which is the ceiling of `x / y` (the unique `z` with `x ≤ z * y < x + y`, see
    `div_ceil_is_ceil`). -/
theorem UScalar.div_ceil.spec {ty : UScalarTy} (x y : UScalar ty) (hy : y.val ≠ 0) :
    UScalar.div_ceil x y ⦃ (z : UScalar ty) =>
      z.val = (x.val + y.val - 1) / y.val ∧
      x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ := by
  simp only [UScalar.div_ceil, hy, ↓reduceDIte, WP.spec_ok, UScalar.ofNatCore_val_eq, true_and]
  exact UScalar.div_ceil_is_ceil (by omega)

uscalar
/-- **Spec theorem for `core::num::{u8,…,usize}::div_ceil`**: the ceiling of `x / y`, for `y ≠ 0`
    (Rust panics when `y = 0`). -/
@[step]
theorem core.num.«%S».div_ceil.spec (x y : «%S») (hy : y.val ≠ 0) :
    core.num.«%S».div_ceil x y ⦃ (z : «%S») =>
      z.val = (x.val + y.val - 1) / y.val ∧
      x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ :=
  UScalar.div_ceil.spec x y hy

end Aeneas.Std
