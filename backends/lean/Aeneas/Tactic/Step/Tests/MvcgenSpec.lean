module
import Aeneas.Std.Scalar
import Aeneas.Std.Array
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Std.Do
set_option mvcgen.warning false
/- TODO: `mvcgen` is deprecated in favor of `vcgen`, but `vcgen` cannot determine the program
   type of these goals yet (Lean v4.35.0). -/
set_option linter.deprecated.syntax false

/-!
# Tests: mvcgen spec generation from @[step]

For every @[step] theorem, the attribute handler also generates an `mvcgen` spec.
-/

example {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
    Triple (m := Result) (ps := .except (ULift Error) (.except PUnit (.except PUnit .pure)))
      (x + y) ⌜True⌝
      (fun z => ⌜z.val = x.val + y.val⌝, fun e => ⌜e.down = Error.oom⌝,
        fun _ => ⌜False⌝, fun _ => ⌜False⌝, .unit) := by
  mvcgen; scalar_tac

example {x y : U8} :
    Triple (m := Result) (ps := .except (ULift Error) (.except PUnit (.except PUnit .pure)))
      (do
        if x < 10#u8
        then x * 2#u8
        else pure y)
      ⌜True⌝
      (fun z => ⌜z.val ≠ y → z.val < 20⌝, fun e => ⌜e.down = Error.oom⌝,
        fun _ => ⌜False⌝, fun _ => ⌜False⌝, .unit) := by
  mvcgen <;> scalar_tac

example (arr : Array U8 25#usize) (i : Usize) (a : U8) (hi : i < arr.length) :
    Triple (m := Result) (ps := .except (ULift Error) (.except PUnit (.except PUnit .pure)))
      (Array.update arr i a) ⌜True⌝
      (fun r => ⌜r.get? i = some a⌝, fun e => ⌜e.down = Error.oom⌝,
        fun _ => ⌜False⌝, fun _ => ⌜False⌝, .unit) := by
  mvcgen; grind
