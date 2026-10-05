module
public import Aeneas.SepLogic.Basic
public import AeneasMeta.Simp
public section

namespace Aeneas.SepLogic

open Lean Lean.Meta

/-- Lemmas (un)folding representation predicates, used by `iframe` and `iintro`. -/
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
