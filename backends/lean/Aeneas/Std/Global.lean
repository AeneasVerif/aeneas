import Lean
open Lean Meta Meta.Simp

namespace Aeneas.Std

/-- The `global_simps` simp attribute. -/
initialize globalSimpExt : SimpExtension ←
  registerSimpAttr `global_simps "\
    The `global_simps` attribute registers simp lemmas to be used when proving
    that global/constant definitions successfully evaluate."

initialize scalarTacSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `global_simps_proc` simp attribute for the simp rocs. -/
initialize globalSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `global_simps_proc "\
    The `global_simps_roc` attribute registers simp procedures to be used when proving
    that global/constant definitions successfully evaluate." (some scalarTacSimprocsRef)

end Aeneas.Std
