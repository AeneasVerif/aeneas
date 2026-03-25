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

/-- The `simp_scalar` attribute registers simp lemmas to be used by `simp_scalar`.
    Those are the "general" lemmas, used only when `safe` is `false` (the default).
    See also `simp_scalar_safe`. -/
register_simp_attr' simpScalarSimpExt simpScalarSimprocExt simp_scalar

/-- The `simp_scalar_safe` attribute registers "safe" simp lemmas for `simp_scalar`.
    These lemmas are always used, even with `simp_scalar +safe`. -/
register_simp_attr' simpScalarSafeSimpExt simpScalarSafeSimprocExt simp_scalar_safe

/-- The `simp_scalar_hyps_simp` simp attribute -/
register_simp_attr' simpScalarHypsSimpExt simpScalarHypsSimprocExt simp_scalar_hyps_simps

end Aeneas.SimpScalar
