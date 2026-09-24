module
public import Aeneas.SepLogic.Basic
public import AeneasMeta.Simp
public section

/-!
# Setup for the separation-logic proof mode

The simp set the proof-mode tactics of `Aeneas.Tactic.SepLogic` normalize
assertions with, registered here so that every tactic module can reach it.
-/

namespace Aeneas.SepLogic

open Lean Lean.Meta

/-- The `iris_simps` simp attribute.  `iframe` and `iintro` use it to normalize
separation-logic assertions before extracting/cancelling them: it is where the
lemmas that unfold or fold representation predicates belong (`nodes_cons`,
`nodes_snoc`, …), making their rewriting declarative. -/
initialize irisSimpExt : SimpExtension ←
  registerSimpAttr `iris_simps "\
    The `iris_simps` attribute registers simp lemmas used by `iframe` and \
    `iintro` to normalize separation-logic assertions (typically, lemmas that \
    decompose a representation predicate into the cells it owns)."

namespace IFrame

theorem sep_ipure_eq (P Q : Prop) :
    (⌜P⌝ ∗ ⌜Q⌝) = ⌜P ∧ Q⌝ := by
  apply IProp.ext
  intro heap
  exact sep_pure_l P ⌜Q⌝ heap

end IFrame

end Aeneas.SepLogic
