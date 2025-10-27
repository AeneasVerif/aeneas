import Lean
open Lean Meta Meta.Simp

namespace Aeneas.Std

/-- The `global_simps` simp attribute. -/
initialize globalSimpExt : SimpExtension ←
  registerSimpAttr `global_simps "\
    The `global_simps` attribute registers simp lemmas to be used when proving
    that global/constant definitions successfully evaluate."

/-- The `global_simps_proc` simp attribute for the simp procs. -/
initialize globalSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `global_simps_proc "\
    The `global_simps_proc` attribute registers simp procedures to be used when proving
    that global/constant definitions successfully evaluate." none

end Aeneas.Std
