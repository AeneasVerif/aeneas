module
public import Lean
public section

namespace Aeneas.Step

open Lean Meta

/-- The `step_simps` simp attribute. -/
meta initialize stepSimpExt : SimpExtension ←
  registerSimpAttr `step_simps "\
    The `step_simps` attribute registers simp lemmas to be used by `step`
    to simplify the goal before looking up lemmas. If often happens that some
    monadic function calls, if given some specific parameters (in particuler,
    specific trait instances), can be simplified to far simpler functions: this
    is the main purpose of this attribute."

end Aeneas.Step
