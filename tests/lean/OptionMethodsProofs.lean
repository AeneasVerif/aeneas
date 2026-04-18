-- Correctness proofs for docs-example tests in `OptionMethods.lean`.
--
-- Structural proofs via `step*` + library spec theorems.

import OptionMethods

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace option_methods

/-- `Some(97).as_ref()` returns `Some(&97)`. -/
theorem test_option_as_ref_some_correct :
    test_option_as_ref_some ⦃ _ => True ⦄ := by
  unfold test_option_as_ref_some
  step*

/-- `None.as_ref()` returns `None`. -/
theorem test_option_as_ref_none_correct :
    test_option_as_ref_none ⦃ _ => True ⦄ := by
  unfold test_option_as_ref_none make_none_u32
  step*

/-- `Some(42).ok_or(0)` returns `Ok(42)`. -/
theorem test_option_ok_or_some_correct :
    test_option_ok_or_some ⦃ _ => True ⦄ := by
  unfold test_option_ok_or_some
  step*
  all_goals simp_all

/-- `None.ok_or(7)` returns `Err(7)`. -/
theorem test_option_ok_or_none_correct :
    test_option_ok_or_none ⦃ _ => True ⦄ := by
  unfold test_option_ok_or_none make_none_u32
  step*
  all_goals simp_all

/-- `Option::default()` for `Option<T>` yields `None`. -/
theorem test_option_default_correct :
    test_option_default ⦃ _ => True ⦄ := by
  unfold test_option_default
    core.option.Option.Insts.CoreDefaultDefault.default
  step*
  all_goals simp_all

/-- `Some(2) == Some(2)` yields `true`. -/
theorem test_option_partial_eq_some_some_eq_correct :
    test_option_partial_eq_some_some_eq ⦃ _ => True ⦄ := by
  unfold test_option_partial_eq_some_some_eq
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
  step*

/-- `Some(2) == Some(3)` yields `false`. -/
theorem test_option_partial_eq_some_some_neq_correct :
    test_option_partial_eq_some_some_neq ⦃ _ => True ⦄ := by
  unfold test_option_partial_eq_some_some_neq
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
  step*

/-- `None == Some(2)` yields `false`. -/
theorem test_option_partial_eq_none_some_correct :
    test_option_partial_eq_none_some ⦃ _ => True ⦄ := by
  unfold test_option_partial_eq_none_some make_none_u32
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
  step*

/-- `Some(5).clone()` yields `Some(5)`. -/
theorem test_option_clone_some_correct :
    test_option_clone_some ⦃ _ => True ⦄ := by
  unfold test_option_clone_some
    core.option.Option.Insts.CoreCloneClone.clone
  step*

/-- `None.clone()` yields `None`. -/
theorem test_option_clone_none_correct :
    test_option_clone_none ⦃ _ => True ⦄ := by
  unfold test_option_clone_none make_none_u32
    core.option.Option.Insts.CoreCloneClone.clone
  simp

end option_methods
