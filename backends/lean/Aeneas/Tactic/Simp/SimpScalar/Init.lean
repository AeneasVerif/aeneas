import AeneasMeta.Simp
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

/-- The `simp_scalar_simps` attribute registers simp lemmas to be used by `simp_scalar` -/
register_simp_attr' simpScalarSimpExt simpScalarSimprocExt simp_scalar_simps

/-- The `simp_scalar_hyps_simp` simp attribute -/
register_simp_attr' simpScalarHypsSimpExt simpScalarHypsSimprocExt simp_scalar_hyps_simps

end Aeneas.SimpScalar
