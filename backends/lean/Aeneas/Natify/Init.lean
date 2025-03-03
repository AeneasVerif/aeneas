import Aeneas.Extensions
open Lean Meta

namespace Aeneas.Natify

/-- The `natify_simps` simp attribute. -/
initialize natifySimpExt : SimpExtension ←
  registerSimpAttr `natify_simps "\
    The `natify_simps` attribute registers simp lemmas to be used by `natify`."

end Aeneas.Natify
