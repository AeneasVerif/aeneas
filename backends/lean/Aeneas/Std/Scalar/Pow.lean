module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public section

namespace Aeneas.Std

open Result ScalarElab

/-! ## `{u8,u16,...}::is_power_of_two`

Rust defines `is_power_of_two` on the unsigned integers only. -/

def UScalar.is_power_of_two (x : UScalar ty) : Result Bool :=
  ok x.val.isPowerOfTwo

@[rust_fun "core::num::{u8}::is_power_of_two"]
def core.num.U8.is_power_of_two (x : U8) : Result Bool := UScalar.is_power_of_two x

@[rust_fun "core::num::{u16}::is_power_of_two"]
def core.num.U16.is_power_of_two (x : U16) : Result Bool := UScalar.is_power_of_two x

@[rust_fun "core::num::{u32}::is_power_of_two"]
def core.num.U32.is_power_of_two (x : U32) : Result Bool := UScalar.is_power_of_two x

@[rust_fun "core::num::{u64}::is_power_of_two"]
def core.num.U64.is_power_of_two (x : U64) : Result Bool := UScalar.is_power_of_two x

@[rust_fun "core::num::{u128}::is_power_of_two"]
def core.num.U128.is_power_of_two (x : U128) : Result Bool := UScalar.is_power_of_two x

@[rust_fun "core::num::{usize}::is_power_of_two"]
def core.num.Usize.is_power_of_two (x : Usize) : Result Bool := UScalar.is_power_of_two x

theorem UScalar.is_power_of_two.spec (x : UScalar ty) :
    UScalar.is_power_of_two x ⦃ (b : Bool) => b = x.val.isPowerOfTwo ⦄ := by
  simp only [UScalar.is_power_of_two, eq_iff_iff, WP.spec_ok, decide_eq_true_eq]

uscalar
@[step]
theorem core.num.«%S».is_power_of_two.spec (x : «%S») :
    core.num.«%S».is_power_of_two x ⦃ (b : Bool) => b = x.val.isPowerOfTwo ⦄ :=
  UScalar.is_power_of_two.spec x

end Aeneas.Std
