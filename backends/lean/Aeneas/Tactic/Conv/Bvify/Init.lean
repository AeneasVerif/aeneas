module
public import AeneasMeta.Simp
public section
open Lean Meta

namespace Aeneas.Bvify

/-!
# Tracing
-/

-- We can't define and use trace classes in the same file
meta initialize registerTraceClass `Bvify

/-!
# Bvify Simpsets
-/

/-- The `bvify` attribute registers simp lemmas to be used by `bvify` -/
register_simp_attr' bvifySimpExt bvifySimprocExt bvify

/-- The `bvify_hyps_simps` attribute registers simp lemmas to be used by `bvify` to simplify
assumptions during its preprocessing phase -/
register_simp_attr' bvifyHypsSimpExt bvifyHypsSimprocExt bvify_hyps_simps

/-- The `bvify_assume` attribute registers the lifting lemmas whose preconditions `bvify ... by`
assumes rather than proves: the user then proves that the lifted proposition is equivalent to
the original one. -/
register_simp_attr' bvifyAssumeSimpExt bvifyAssumeSimprocExt bvify_assume

end Aeneas.Bvify
