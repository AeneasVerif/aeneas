module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.Grind.Init
public section

namespace Aeneas.Std

open Result Error ScalarElab

/-! ## `{u8,u16,...}::div_ceil`

Rust defines `div_ceil` on the unsigned integers only
(<https://doc.rust-lang.org/std/primitive.usize.html#method.div_ceil>).
It panics when `rhs == 0` and `d + 1` can't overflow:
the result is at most `self` (`div_ceil_le`). -/

/-- The result of `div_ceil` is at most `x`, so it fits in the type of its arguments. -/
theorem UScalar.div_ceil_le {x y : Nat} (hy : 0 < y) :
    (if 0 < x % y then x / y + 1 else x / y) ≤ x := by
  have := Nat.div_add_mod x y
  have := Nat.le_mul_of_pos_left (x / y) hy
  split
  · agrind
  · agrind

/-- Model of `div_ceil`, for every unsigned width: Rust's `d + 1` if the remainder `r` is
    positive, `d` otherwise, with `d` and `r` the quotient and remainder of `x` by `y`. -/
@[expose] def UScalar.div_ceil {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if h : y.val = 0 then fail divisionByZero
  else ok (UScalar.ofNatCore (if 0 < x.val % y.val then x.val / y.val + 1 else x.val / y.val)
    (Nat.lt_of_le_of_lt (UScalar.div_ceil_le (Nat.pos_of_ne_zero h)) x.hBounds))

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

/-- Spec theorem for `div_ceil`: the result is the ceiling of `x / y`, i.e. the unique `z` with
`x ≤ z * y < x + y`. -/
theorem UScalar.div_ceil.spec {ty : UScalarTy} (x y : UScalar ty) (hy : y.val ≠ 0) :
    UScalar.div_ceil x y ⦃ (z : UScalar ty) =>
      x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ := by
  have := Nat.div_add_mod x.val y.val
  have := Nat.mod_lt x.val (Nat.pos_of_ne_zero hy)
  simp only [UScalar.div_ceil, hy, ↓reduceDIte, WP.spec_ok, UScalar.ofNatCore_val_eq]
  split
  · exact ⟨by agrind, by agrind⟩
  · exact ⟨by agrind, by agrind⟩

uscalar
/-- `core::num::{u8,…,usize}::div_ceil`: the ceiling of `x / y`, for `y ≠ 0`. -/
@[step]
theorem core.num.«%S».div_ceil.spec (x y : «%S») (hy : y.val ≠ 0) :
    core.num.«%S».div_ceil x y ⦃ (z : «%S») =>
      x.val ≤ z.val * y.val ∧ z.val * y.val < x.val + y.val ⦄ :=
  UScalar.div_ceil.spec x y hy

end Aeneas.Std
