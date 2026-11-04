module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public import Mathlib.Algebra.Order.Floor.Div
import Aeneas.Tactic.Solver.Grind.Init
public section

namespace Aeneas.Std

open Result Error ScalarElab

/-! ## `{u8,u16,...}::div_ceil`

Rust defines `div_ceil` on the unsigned integers only
(<https://doc.rust-lang.org/std/primitive.usize.html#method.div_ceil>).
It panics when `rhs == 0` and otherwise returns the ceiling of `self / rhs`, which can't overflow -/

/-- Model of `div_ceil`, for every unsigned width: Mathlib's ceiling division `x ⌈/⌉ y`. -/
@[expose] def UScalar.div_ceil {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if h : y.val = 0 then fail divisionByZero
  else ok (UScalar.ofNatCore (x.val ⌈/⌉ y.val)
    (Nat.lt_of_le_of_lt ((ceilDiv_le_iff_le_mul (Nat.pos_of_ne_zero h)).2
      (Nat.le_mul_of_pos_left x.val (Nat.pos_of_ne_zero h))) x.hBounds))

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

/-- `div_ceil` fails when the divisor is zero, where Rust panics (`UScalar.div_ceil.spec`
    shows it succeeds otherwise). -/
theorem UScalar.div_ceil_zero {ty : UScalarTy} (x y : UScalar ty) (hy : y.val = 0) :
    UScalar.div_ceil x y = fail divisionByZero := by
  simp [UScalar.div_ceil, hy]

/-- Spec theorem for `div_ceil`: the result is the ceiling of `x / y`. See
`UScalar.div_ceil.spec_bounds` for the characterization as the unique `z` such that
`x ≤ z * y < x + y`. -/
theorem UScalar.div_ceil.spec {ty : UScalarTy} (x y : UScalar ty) (hy : y.val ≠ 0) :
    UScalar.div_ceil x y ⦃ (z : UScalar ty) => z.val = x.val ⌈/⌉ y.val ⦄ := by
  simp only [UScalar.div_ceil, hy, ↓reduceDIte, WP.spec_ok, UScalar.ofNatCore_val_eq]

private theorem ceilDiv_bounds (x : ℕ) {y : ℕ} (hy : 0 < y) :
    x ≤ x ⌈/⌉ y * y ∧ x ⌈/⌉ y * y < x + y := by
  constructor
  · rw [Nat.mul_comm]
    exact le_smul_ceilDiv hy
  · have := Nat.div_mul_le_self (x + y - 1) y
    rw [Nat.ceilDiv_eq_add_pred_div]
    agrind

/-- Alternative specification of `div_ceil`: the result `z` satisfies `x ≤ z * y < x + y`, which
uniquely characterizes `x ⌈/⌉ y`. -/
theorem UScalar.div_ceil.spec_bounds {ty : UScalarTy} (x y : UScalar ty) (hy : y.val ≠ 0) :
    UScalar.div_ceil x y ⦃ (z : UScalar ty) =>
      x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ := by
  simp only [UScalar.div_ceil, hy, ↓reduceDIte, WP.spec_ok, UScalar.ofNatCore_val_eq]
  exact ceilDiv_bounds x.val (Nat.pos_of_ne_zero hy)

uscalar
/-- `core::num::{u8,…,usize}::div_ceil`: the ceiling of `x / y`, for `y ≠ 0`. -/
@[step]
theorem core.num.«%S».div_ceil.spec (x y : «%S») (hy : y.val ≠ 0) :
    core.num.«%S».div_ceil x y ⦃ (z : «%S») => z.val = x.val ⌈/⌉ y.val ⦄ :=
  UScalar.div_ceil.spec x y hy

uscalar
/-- `core::num::{u8,…,usize}::div_ceil`: the unique `z` with `x ≤ z * y < x + y`, for `y ≠ 0`. -/
theorem core.num.«%S».div_ceil.spec_bounds (x y : «%S») (hy : y.val ≠ 0) :
    core.num.«%S».div_ceil x y ⦃ (z : «%S») =>
      x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ :=
  UScalar.div_ceil.spec_bounds x y hy

end Aeneas.Std
