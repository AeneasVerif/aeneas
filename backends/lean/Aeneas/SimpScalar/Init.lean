import AeneasMeta.Extensions
import AeneasMeta.Saturate
open Lean Meta

namespace Aeneas.SimpScalar

/-!
# Tracing
-/

-- We can't define and use trace classes in the same file
initialize registerTraceClass `SimpScalar

/-!
# Simp Scalar Simpsets
-/

/-- The `simp_scalar_simps` simp attribute. -/
initialize simpScalarSimpExt : SimpExtension ←
  registerSimpAttr `simp_scalar_simps "\
    The `simp_scalar_simps` attribute registers simp lemmas to be used by `simp_scalar`."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
--initialize simpScalarSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `simp_scalar_simps_proc` simp attribute for the simp rocs. -/
initialize simpScalarSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `simp_scalar_simps_proc "\
    The `simp_scalar_simps_proc` attribute registers simp procedures to be used by `simp_scalar`
    during its preprocessing phase." none --(some simpScalarSimprocsRef)

/-- The `simp_scalar_hyps_simp` simp attribute. -/
initialize simpScalarHypsSimpExt : SimpExtension ←
  registerSimpAttr `simp_scalar_hyps_simps "\
    The `simp_scalar_hyps_simp` attribute registers simp lemmas to be used by `simp_scalar`."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
--initialize simpScalarSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `simp_scalar_hyps_simp_proc` simp attribute for the simp rocs. -/
initialize simpScalarHypsSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `simp_scalar_hyps_simps_proc "\
    The `simp_scalar_hyps_simp_proc` attribute registers simp procedures to be used by `simp_scalar`
    during its preprocessing phase." none --(some simpScalarSimprocsRef)

end Aeneas.SimpScalar
