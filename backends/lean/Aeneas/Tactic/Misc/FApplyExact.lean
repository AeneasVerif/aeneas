/-
  `fapply` and `fexact`: versions of `apply` and `exact` that use reducible
  transparency for the unification step, preventing WHNF explosion on complex
  function bodies.

  Analogous to `fcongr` (which is `congr` with reducible transparency).
-/
import Lean

open Lean Meta Parser Elab Tactic

namespace FApply

syntax (name := fapply) "fapply " term : tactic
syntax (name := fexact) "fexact " term : tactic

@[tactic fapply]
def evalFApply : Tactic
| `(tactic| fapply $e) => withMainContext do
    withTransparency .instances do
      evalTactic (← `(tactic| apply $e))
| _ => throwUnsupportedSyntax

@[tactic fexact]
def evalFExact : Tactic
| `(tactic| fexact $e) => withMainContext do
    withTransparency .instances do
      evalTactic (← `(tactic| exact $e))
| _ => throwUnsupportedSyntax

end FApply
