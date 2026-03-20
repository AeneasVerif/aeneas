import AeneasMeta.Saturate.Attribute
import AeneasMeta.Simp
open Lean Meta Meta.Simp

namespace Aeneas.ScalarTac

/-!
# Tracing
-/

-- We can't define and use trace classes in the same file
initialize registerTraceClass `ScalarTac

/-!
# Simp Sets
-/

/-- The `scalar_tac_simps` attribute registers simp lemmas to be used by `scalar_tac`
during its preprocessing phase. -/
register_simp_attr' scalarTacSimpExt scalarTacSimprocExt scalar_tac_simps

/-!
# Saturation Rules Sets
-/

syntax (name := scalar_tac) "scalar_tac" (term)? : attr
syntax (name := scalar_tac_nonlin) "scalar_tac_nonlin" (term)? : attr

def elabAttribute (stx : Syntax) : MetaM (Option Syntax) :=
  withRef stx do
    match stx with
    | `(attr| scalar_tac $[$pat]?)
    | `(attr| scalar_tac_nonlin $[$pat]?) => pure pat
    | _ => Lean.Elab.throwUnsupportedSyntax

initialize scalarTacAttribute : Saturate.Attribute.SaturateAttribute ←
  Saturate.Attribute.makeAttribute `scalar_tac_map `scalar_tac elabAttribute

initialize scalarTacNonLinAttribute : Saturate.Attribute.SaturateAttribute ←
  Saturate.Attribute.makeAttribute `scalar_tac_nonlin_map `scalar_tac_nonlin elabAttribute

end Aeneas.ScalarTac
