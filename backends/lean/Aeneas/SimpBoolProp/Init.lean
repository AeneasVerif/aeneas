import AeneasMeta.Extensions
import AeneasMeta.Saturate
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

/-- The `simp_bool_prop_simps` simp attribute. -/
initialize simpBoolPropSimpExt : SimpExtension ←
  registerSimpAttr `simp_bool_prop_simps "\
    The `simp_bool_prop_simps` attribute registers simp lemmas to be used to simplify booleans and propositions.
    Those simp lemmas are used by several tactics such as `scalar_tac`, `simp_scalar`, `simp_ifs`, etc."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
--initialize simpListsSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `simp_bool_prop_simps_proc` simp attribute for the simp rocs. -/
initialize simpBoolPropSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `simp_bool_prop_simps_proc "\
    The `simp_bool_prop_simps` attribute registers simp procedures to be used to simplify booleans and propositions.
    Those simp procedures are used by several tactics such as `scalar_tac`, `simp_scalar`, `simp_ifs`, etc."
    none --(some simpListsSimprocsRef)

/-- The `simp_bool_prop_hyps_simps` simp attribute. -/
initialize simpBoolPropHypsSimpExt : SimpExtension ←
  registerSimpAttr `simp_bool_prop_hyps_simps "\
    The `simp_bool_prop_hyps_simps` attribute registers simp lemmas to be used to simplify booleans and propositions.
    Those simp lemmas are used by several tactics such as `scalar_tac`, `simp_scalar`, `simp_ifs`, etc."

-- TODO: initialization fails with this, while the same works for `scalar_tac`??
--initialize simpListsSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- The `simp_bool_prop_hyps_simps_proc` simp attribute for the simp rocs. -/
initialize simpBoolPropHypsSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `simp_bool_prop_hyps_simps_proc "\
    The `simp_bool_prop_hyps_simps` attribute registers simp procedures to be used to simplify booleans and propositions.
    Those simp procedures are used by several tactics such as `scalar_tac`, `simp_scalar`, `simp_ifs`, etc."
    none --(some simpListsSimprocsRef)

end Aeneas.SimpBoolProp
