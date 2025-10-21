import AeneasMeta.Saturate.Attribute
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

/-- The `scalar_tac_simps` simp attribute. -/
initialize scalarTacSimpExt : SimpExtension ←
  registerSimpAttr `scalar_tac_simps "\
    The `scalar_tac_simps` attribute registers simp lemmas to be used by `scalar_tac`
    during its preprocessing phase."

/-- The `scalar_tac_simps_proc` simp attribute for the simp rocs. -/
initialize scalarTacSimprocExt : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `scalar_tac_simps_proc "\
    The `scalar_tac_simps_proc` attribute registers simp procedures to be used by `scalar_tac`
    during its preprocessing phase." none

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
