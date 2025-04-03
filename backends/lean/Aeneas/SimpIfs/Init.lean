import Aeneas.Extensions
import Aeneas.Saturate
open Lean Meta

namespace Aeneas.SimpIfs

/-!
# Tracing
-/

-- We can't define and use trace classes in the same file
initialize registerTraceClass `SimpIfs

/-!
# Simp Lists Simpsets
-/

/-- The `simp_ifs_simps` simp attribute. -/
initialize simpListsSimpExt : SimpExtension ←
  registerSimpAttr `simp_ifs_simps "\
    The `simp_ifs_simps` attribute registers simp lemmas to be used by `simp_ifs`."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
--initialize simpListsSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `simp_ifs_simps_proc` simp attribute for the simp rocs. -/
initialize simpListsSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `simp_ifs_simps_proc "\
    The `simp_ifs_simps_proc` attribute registers simp procedures to be used by `simp_ifs`
    during its preprocessing phase." none --(some simpListsSimprocsRef)

end Aeneas.SimpIfs
