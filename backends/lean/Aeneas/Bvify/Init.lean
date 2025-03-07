import Aeneas.Extensions
import Aeneas.Saturate
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

/-- The `bvify_simps` simp attribute. -/
initialize bvifySimpExt : SimpExtension ←
  registerSimpAttr `bvify_simps "\
    The `bvify_simps` attribute registers simp lemmas to be used by `bvify`."

/-- The `bvify_csimps` simp attribute, for conditional rewriting which need `scalar_tac` to discharge the preconditions. -/
initialize bvifyCSimpExt : SimpExtension ←
  registerSimpAttr `bvify_csimps "\
    The `bvify_csimps` attribute registers conditional simp lemmas to be used by `bvify`, and for which we use `scalar_tac`
    to discharge the preconditions."

/-!
# Bvify Forward Rules
-/
-- The sets of forward rules that `bvify` should use
open Extensions in
initialize bvifyRuleSet : ListDeclarationExtension Name ← do
  mkListDeclarationExtension `bvifyRuleSet

macro "bvify_forward" pat:term : attr =>
  `(attr|aeneas_saturate allow_loose (set := $(Lean.mkIdent `Aeneas.BvifyTac)) (pattern := $pat))

end Aeneas.Bvify
