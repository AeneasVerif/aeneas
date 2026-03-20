import AeneasMeta.Simp
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

/-- The `simp_lists_simps` attribute registers simp lemmas to be used by `simp_lists` -/
register_simp_attr' simpListsSimpExt simpListsSimprocExt simp_lists_simps

/-- The `simp_lists_hyps_simp` simp attribute -/
register_simp_attr' simpListsHypsSimpExt simpListsHypsSimprocExt simp_lists_hyps_simps

end Aeneas.SimpLists
