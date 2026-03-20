import AeneasMeta.Simp
open Lean Meta

namespace Aeneas.Natify

/-- The `natify_simps` attribute registers simp lemmas to be used by `natify` -/
register_simp_attr' natifySimpExt natifySimprocExt natify_simps

end Aeneas.Natify
