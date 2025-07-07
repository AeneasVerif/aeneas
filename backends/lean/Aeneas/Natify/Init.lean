import AeneasMeta.Extensions
open Lean Meta

namespace Aeneas.Natify

/-- The `natify_simps` simp attribute. -/
initialize natifySimpExt : SimpExtension ←
  registerSimpAttr `natify_simps "\
    The `natify_simps` attribute registers simp lemmas to be used by `natify`."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
initialize natifySimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `natify_simps_proc` simp attribute for the simp rocs. -/
initialize natifySimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `natify_simps_proc "\
    The `natify_simps_proc` attribute registers simp procedures to be used by `natify`
    during its preprocessing phase." (some natifySimprocsRef)

end Aeneas.Natify
