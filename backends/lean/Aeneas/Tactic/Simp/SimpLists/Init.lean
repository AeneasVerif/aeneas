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

/-- The `simp_lists` attribute registers simp lemmas to be used by `simp_lists`.
    Those are the "general" lemmas, used only when `safe` is `false` (the default).
    See also `simp_lists_safe`. -/
register_simp_attr' simpListsSimpExt simpListsSimprocExt simp_lists

/-- The `simp_lists_safe` attribute registers "safe" simp lemmas for `simp_lists`.
    These lemmas are always used, even with `simp_lists +safe`. -/
register_simp_attr' simpListsSafeSimpExt simpListsSafeSimprocExt simp_lists_safe

/-- The `simp_lists_hyps_simp` simp attribute -/
register_simp_attr' simpListsHypsSimpExt simpListsHypsSimprocExt simp_lists_hyps_simps

end Aeneas.SimpLists
