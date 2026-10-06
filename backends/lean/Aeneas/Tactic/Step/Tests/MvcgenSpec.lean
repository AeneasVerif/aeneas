module
import Aeneas.Std.Scalar
import Aeneas.Std.Array
import Aeneas.Tactic.Step
import Aeneas.Do

open Aeneas Aeneas.Std Result Std.Do
open Aeneas.Std.WP (spec dspec spec_iff_mvcgen dspec_iff_mvcgen)
set_option mvcgen.warning false

/-!
# Tests: mvcgen spec generation from @[step]

For every @[step] theorem, the attribute handler also generates an `mvcgen` spec.
-/

example {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
    ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ ⇓ z => ⌜ z.val = x.val + y.val ⌝ ⦄ := by
  mvcgen; scalar_tac

example {x y : U8} :
    Triple
      (do
        if x < 10#u8
        then x * 2#u8
        else pure y)
      ⌜ True ⌝
      (⇓ z => ⌜ z.val ≠ y → z.val < 20 ⌝) := by
  mvcgen <;> scalar_tac

example (arr : Array U8 25#usize) (i : Usize) (a : U8) (hi : i < arr.length) :
    ⦃ ⌜ True ⌝ ⦄
      Array.update arr i a
    ⦃ ⇓ r => ⌜ r.get? i = some a ⌝ ⦄ := by
  mvcgen; grind

namespace Aeneas.MvcgenTests

def guardedIdentity (n : Nat) : Result Nat :=
  Result.guardedModify (fun _ => True) fun heap _ => (n, heap)

@[local step]
theorem guardedIdentity_spec (n : Nat) :
    spec (guardedIdentity n) (fun value => value = n) := by
  apply WP.ispec_guardedModify
  intro heap _ frame hCompatible
  exact ⟨True.intro, heap, hCompatible, rfl, rfl⟩

def twice (n : Nat) : Result Nat := do
  let value ← guardedIdentity n
  guardedIdentity (value + 1)

example (n : Nat) :
    ⦃ ⌜ True ⌝ ⦄ twice n ⦃ ⇓ value => ⌜ value = n + 1 ⌝ ⦄ := by
  mvcgen [twice]; grind

example (n : Nat) : spec (twice n) (fun value => value = n + 1) := by
  apply spec_iff_mvcgen.mpr
  mvcgen [twice]; grind

def countdown (n : Nat) : Result Nat :=
  if n = 0 then .ok 0 else countdown (n - 1)
partial_fixpoint

@[local step]
theorem countdown_spec (n : Nat) : dspec (countdown n) (fun value => value = 0) := by
  revert n
  dspec_induction countdown
  intro f ih n
  simp only
  split <;> simp_all

example (n : Nat) :
    ⦃ ⌜ True ⌝ ⦄ countdown n ⦃ ⇓? value => ⌜ value = 0 ⌝ ⦄ := by
  mvcgen; grind

example (n : Nat) : dspec (do let v ← countdown n; pure (v + 1)) (fun value => value = 1) := by
  apply dspec_iff_mvcgen.mpr
  mvcgen; grind

example (n : Nat) (hTerm : (countdown n).terminates) :
    ⦃ ⌜ True ⌝ ⦄ countdown n ⦃ ⇓ value => ⌜ value = 0 ⌝ ⦄ := by
  mvcgen
  all_goals simp_all

def delayedDiv : Result Nat :=
  Result.vis (.guardedModify Unit (fun _ => True) fun heap _ => ((), heap))
    (fun _ => Result.div)

example : delayedDiv ≠ Result.div := by
  simp [delayedDiv]

example : ¬ ⦃ ⌜ True ⌝ ⦄ delayedDiv ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  intro h
  have hSpec := spec_iff_mvcgen.mpr h
  rw [WP.spec, WP.ispec_iff] at hSpec
  have hEmp : ((SepLogic.emp : SepLogic.IPre) ∗ SepLogic.emp) (∅ : Heap) :=
    (SepLogic.sep_emp_r SepLogic.emp).mpr ∅ trivial
  exact Data.Coinductive.DWP.div_false (hSpec SepLogic.emp ∅ hEmp).vis_view.2

end Aeneas.MvcgenTests
