import Lean
open Lean Meta

namespace Aeneas.ZModify

/-- The `zmodify_simps` simp attribute. -/
initialize zmodifySimpExt : SimpExtension ←
  registerSimpAttr `zmodify_simps "\
    The `zmodify_simps` attribute registers simp lemmas to be used by `zmodify`."

initialize zmodifySimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `zmodify_simps_proc` simp attribute for the simp rocs. -/
initialize zmodifySimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `zmodify_simps_proc "\
    The `zmodify_simps_proc` attribute registers simp procedures to be used by `zmodify`
    during its preprocessing phase." (some zmodifySimprocsRef)

end Aeneas.ZModify
