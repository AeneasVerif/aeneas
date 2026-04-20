import Aeneas.Std.Scalar
import Aeneas.Std.Array
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Std.Do
set_option mvcgen.warning false

/-!
# Tests: mvcgen spec generation from @[step]

For every @[step] theorem, the attribute handler also generates an `mvcgen` spec.
-/

example {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
    ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ ⇓ z => ⌜ z.val = x.val + y.val ⌝ ⦄ := by
  mvcgen; scalar_tac

example {x y : U8} :
    ⦃ ⌜ True ⌝ ⦄
      (do
        if x < 10#u8
        then x * 2#u8
        else pure y)
    ⦃ ⇓ z => ⌜ z.val ≠ y → z.val < 20 ⌝ ⦄ := by
  mvcgen <;> scalar_tac

example (arr : Array U8 25#usize) (i : Usize) (a : U8) (hi : i < arr.length) :
    ⦃ ⌜ True ⌝ ⦄
      Array.update arr i a
    ⦃ ⇓ r => ⌜ r.get? i = some a ⌝ ⦄ := by
  mvcgen; grind
