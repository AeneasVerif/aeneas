import AeneasMeta.Simp
open Lean Meta

namespace Aeneas.Bvify

/-!
# Tracing
-/

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Bvify

/-!
# Bvify Simpsets
-/

/-- The `bvify_simps` attribute registers simp lemmas to be used by `bvify` -/
register_simp_attr' bvifySimpExt bvifySimprocExt bvify_simps

/-- The `bvify_hyps_simps` attribute registers simp lemmas to be used by `bvify` to simplify
assumptions during its preprocessing phase -/
register_simp_attr' bvifyHypsSimpExt bvifyHypsSimprocExt bvify_hyps_simps

end Aeneas.Bvify
