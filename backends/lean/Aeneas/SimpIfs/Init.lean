import AeneasMeta.Extensions
import AeneasMeta.Saturate
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

/-- The `simp_ifs_simps` simp attribute. -/
initialize simpIfsSimpExt : SimpExtension ←
  registerSimpAttr `simp_ifs_simps "\
    The `simp_ifs_simps` attribute registers simp lemmas to be used by `simp_ifs`."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
--initialize simpIfsSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `simp_ifs_simps_proc` simp attribute for the simp rocs. -/
initialize simpIfsSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `simp_ifs_simps_proc "\
    The `simp_ifs_simps_proc` attribute registers simp procedures to be used by `simp_ifs`
    during its preprocessing phase." none --(some simpIfsSimprocsRef)

/-- The `simp_ifs_hyps_simps` simp attribute. -/
initialize simpIfsHypsSimpExt : SimpExtension ←
  registerSimpAttr `simp_ifs_hyps_simps "\
    The `simp_ifs_hyps_simps` attribute registers simp lemmas to be used by `simp_ifs` when preprocessing hypotheses."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
--initialize simpIfsSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `simp_ifs_hyps_simps_proc` simp attribute for the simp rocs. -/
initialize simpIfsHypsSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `simp_ifs_hyps_simps_proc "\
    The `simp_ifs_hyps_simps_proc` attribute registers simp procedures to be used by `simp_ifs`
    during its preprocessing phase." none --(some simpIfsSimprocsRef)


end Aeneas.SimpIfs
