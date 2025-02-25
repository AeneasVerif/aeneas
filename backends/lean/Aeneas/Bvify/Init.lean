import Aeneas.Extensions
open Lean Meta

namespace Aeneas.Bvify

/-- The `bvify_simps` simp attribute. -/
initialize bvifySimpExt : SimpExtension ←
  registerSimpAttr `bvify_simps "\
    The `bvify_simps` attribute registers simp lemmas to be used by `bvify`."

end Aeneas.Bvify
