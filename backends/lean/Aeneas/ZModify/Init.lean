import AeneasMeta.Extensions
open Lean Meta

namespace Aeneas.ZModify

/-!
# ZMod-ify
-/

/-- The `zmodify_simps` simp attribute. -/
initialize zmodifySimpExt : SimpExtension ←
  registerSimpAttr `zmodify_simps "\
    The `zmodify_simps` attribute registers simp lemmas to be used by `zmodify`."

/-- The `zmodify_simps_proc` simp attribute for the simp rocs. -/
initialize zmodifySimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `zmodify_simps_proc "\
    The `zmodify_simps_proc` attribute registers simp procedures to be used by `zmodify`
    during its preprocessing phase." none

/-- The `zmodify_hyps_simp` simp attribute. -/
initialize zmodifyHypsSimpExt : SimpExtension ←
  registerSimpAttr `zmodify_hyps_simps "\
    The `zmodify_hyps_simp` attribute registers simp lemmas to be used by `zmodify`."

initialize zmodifyHypsSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `zmodify_hyps_simp_proc` simp attribute for the simp rocs. -/
initialize zmodifyHypsSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `zmodify_hyps_simps_proc "\
    The `zmodify_hyps_simp_proc` attribute registers simp procedures to be used by `zmodify`
    during its preprocessing phase." (some zmodifyHypsSimprocsRef)

end Aeneas.ZModify
