import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

open Result

@[rust_fun "core::num::{usize}::is_power_of_two"]
def core.num.Usize.is_power_of_two (x : Std.Usize) : Result Bool :=
  ok x.val.isPowerOfTwo

@[progress]
theorem core.num.Usize.is_power_of_two_spec (x : Std.Usize) :
  core.num.Usize.is_power_of_two x ⦃ b => b = x.val.isPowerOfTwo ⦄ := by
  simp only [is_power_of_two, eq_iff_iff, WP.spec_ok, decide_eq_true_eq]

end Aeneas.Std
