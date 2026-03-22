import AeneasMeta.Simp
open Lean Meta

namespace Aeneas.Natify

/-- The `natify` attribute registers simp lemmas to be used by the `natify` tactic -/
register_simp_attr' natifySimpExt natifySimprocExt natify

end Aeneas.Natify
