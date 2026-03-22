import AeneasMeta.Simp
open Lean Meta

namespace Aeneas.SimpIfs

/-!
# Tracing
-/

-- We can't define and use trace classes in the same file
initialize registerTraceClass `SimpIfs

/-!
# Simp Ifs Simpsets
-/

/-- The `simp_ifs` attribute registers simp lemmas to be used by `simp_ifs`.
    Those are the "general" lemmas, used only when `safe` is `false` (the default).
    See also `simp_ifs_safe`. -/
register_simp_attr' simpIfsSimpExt simpIfsSimprocExt simp_ifs

/-- The `simp_ifs_safe` attribute registers "safe" simp lemmas for `simp_ifs`.
    These lemmas are always used, even with `simp_ifs +safe`. -/
register_simp_attr' simpIfsSafeSimpExt simpIfsSafeSimprocExt simp_ifs_safe

/-- The `simp_ifs_hyps_simps` attribute registers simp lemmas to be used by `simp_ifs` when
preprocessing assumptions -/
register_simp_attr' simpIfsHypsSimpExt simpIfsHypsSimprocExt simp_ifs_hyps_simps


end Aeneas.SimpIfs
