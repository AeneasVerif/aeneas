import AeneasMeta.Simp
open Lean Meta

namespace Aeneas.ZModify

/-!
# ZMod-ify
-/

/-- The `zmodify` attribute registers simp lemmas to be used by the `zmodify` tactic -/
register_simp_attr' zmodifySimpExt zmodifySimprocExt zmodify

/-- The `zmodify_hyps` attribute registers simp lemmas to be used by `zmodify` to simplify hypotheses -/
register_simp_attr' zmodifyHypsSimpExt zmodifyHypsSimprocExt zmodify_hyps

end Aeneas.ZModify
