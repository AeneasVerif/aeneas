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

end Aeneas.Bvify
