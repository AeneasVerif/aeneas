import AeneasMeta.Simp
open Lean Meta

namespace Aeneas.SimpBoolProp

/-!
# Tracing
-/

-- We can't define and use trace classes in the same file
initialize registerTraceClass `SimpBoolProp

/-!
# Simp Bool/Prop Simpsets


Those lemmas and simp procedures specifically target boolean expressions and
propositions. They gather simp lemmas and procedures that are commonly used
by other specialized tactics (such as `scalar_tac`, `simp_lists`, etc.).
-/

/-- The `simp_bool_prop_simps` attribute registers simp lemmas to be used to simplify booleans and propositions.
    Those simp lemmas are used by several tactics such as `scalar_tac`, `simp_scalar`, `simp_ifs`, etc. -/
register_simp_attr' simpBoolPropSimpExt simpBoolPropSimprocExt simp_bool_prop_simps

/-- The `simp_bool_prop_hyps_simps` attribute registers simp lemmas to be used by tactics like `scalar_tac`,
`simp_scalar`, `simp_ifs`, etc. to simplify booleans and propositions in assumptions. -/
register_simp_attr' simpBoolPropHypsSimpExt simpBoolPropHypsSimprocExt simp_bool_prop_hyps_simps

end Aeneas.SimpBoolProp
