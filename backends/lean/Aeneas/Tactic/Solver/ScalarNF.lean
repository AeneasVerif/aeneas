import Aeneas.ScalarTac

namespace Aeneas

namespace ScalarTac

syntax "scalar_eq_nf" ("at" ("*" <|> ident))? : tactic
macro_rules
  | `(tactic| scalar_eq_nf) =>
    `(tactic|
      -- We put everything on the same side of the equation
      simp (config := {singlePass := true}) only [← Int.sub_eq_zero] <;>
      -- Then we call ring_nf
      ring_nf)
  | `(tactic| scalar_eq_nf at $h:ident) =>
    `(tactic|
      simp (config := {singlePass := true}) only [← Int.sub_eq_zero] at ($h) <;>
      ring_nf at ($h))
  | `(tactic| scalar_eq_nf at *) =>
    `(tactic|
      simp (config := {singlePass := true}) only [← Int.sub_eq_zero] at * <;>
      ring_nf at *)

open Lean.Parser.Tactic in
open Mathlib.Tactic.Ring in
macro "scalar_nf" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| ring_nf $cfg:optConfig $(loc)?)

end ScalarTac

end Aeneas
