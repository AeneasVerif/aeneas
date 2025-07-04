import AeneasMeta.Extensions
import AeneasMeta.Saturate
open Lean Meta

namespace Aeneas.SimpLists

/-!
# Tracing
-/

-- We can't define and use trace classes in the same file
initialize registerTraceClass `SimpLists

/-!
# Simp Lists Simpsets
-/

/-- The `simp_lists_simps` simp attribute. -/
initialize simpListsSimpExt : SimpExtension ←
  registerSimpAttr `simp_lists_simps "\
    The `simp_lists_simps` attribute registers simp lemmas to be used by `simp_lists`."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
--initialize simpListsSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `simp_lists_simps_proc` simp attribute for the simp rocs. -/
initialize simpListsSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `simp_lists_simps_proc "\
    The `simp_lists_simps_proc` attribute registers simp procedures to be used by `simp_lists`
    during its preprocessing phase." none --(some simpListsSimprocsRef)

/-- The `simp_lists_hyps_simp` simp attribute. -/
initialize simpListsHypsSimpExt : SimpExtension ←
  registerSimpAttr `simp_lists_hyps_simps "\
    The `simp_lists_hyps_simp` attribute registers simp lemmas to be used by `simp_lists`."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
--initialize simpListsSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `simp_lists_hyps_simp_proc` simp attribute for the simp rocs. -/
initialize simpListsHypsSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `simp_lists_hyps_simps_proc "\
    The `simp_lists_hyps_simp_proc` attribute registers simp procedures to be used by `simp_lists`
    during its preprocessing phase." none --(some simpListsSimprocsRef)

end Aeneas.SimpLists
