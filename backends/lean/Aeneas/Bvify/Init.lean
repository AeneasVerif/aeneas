import AeneasMeta.Extensions
open Lean Meta

namespace Aeneas.Bvify

/-!
# Tracing
-/

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Bvify

/-!
# Bvify Simpsets
-/

/-- The `bvify_simps` simp attribute. -/
initialize bvifySimpExt : SimpExtension ←
  registerSimpAttr `bvify_simps "\
    The `bvify_simps` attribute registers simp lemmas to be used by `bvify`."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
--initialize bvifySimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `bvify_simps_proc` simp attribute for the simp rocs. -/
initialize bvifySimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `bvify_simps_proc "\
    The `bvify_simps_proc` attribute registers simp procedures to be used by `bvify`
    during its preprocessing phase." none --(some bvifySimprocsRef)

end Aeneas.Bvify
