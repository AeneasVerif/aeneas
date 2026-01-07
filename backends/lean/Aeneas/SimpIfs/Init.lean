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

/-- The `simp_ifs_simps` attribute registers simp lemmas to be used by `simp_ifs` -/
register_simp_attr' simpIfsSimpExt simpIfsSimprocExt simp_ifs_simps

/-- The `simp_ifs_hyps_simps` attribute registers simp lemmas to be used by `simp_ifs` when
preprocessing assumptions -/
register_simp_attr' simpIfsHypsSimpExt simpIfsHypsSimprocExt simp_ifs_hyps_simps


end Aeneas.SimpIfs
