import Lean
import AeneasMeta.Extensions
-- import Aeneas.Tactic.Step.Init
open Lean Elab Term Meta

namespace Aeneas
open Extensions

-- This file defines an extension for defining spec statements that
-- can be used with the step tactic.


structure LiftingInfo where
  from_statement : Name
  conversion_thm : Name
  conversion_thm_inferred_args : Nat

structure SpecInfo where
  name : Lean.Name
  arity : Nat
  program_index : Nat -- index into the arguments of the Result value
  post_index : Nat

  mk_spec_mono : Name
  mk_spec_mono_skip_args : Nat -- number of arguments to be inferred, before Result and Post arguments
  mk_spec_bind : Name
  mk_spec_bind_skip_args : Nat

  uncurry_elim_tactics : Array Lean.Name
  qimp_elim_tactics : Array Lean.Name

  liftings : Array LiftingInfo
  deriving Inhabited

structure SpecInfoExtensionState where
  specInfos : Std.HashMap Name SpecInfo
  deriving Inhabited

-- /- Initialize the state extension for adding spec theorems -/
initialize specAttr : SimpleScopedEnvExtension SpecInfo SpecInfoExtensionState  ← do
  let ext ← registerSimpleScopedEnvExtension {
    name        := `specStatementRegistrationExtension,
    initial     := {
      specInfos := Std.HashMap.emptyWithCapacity
    },
    addEntry    := fun state new =>
      {state with specInfos := state.specInfos.insert new.name new},
  }
  pure ext

syntax (name := register_spec_statement_cmd)
  "#register_spec_statement " term : command

@[command_elab register_spec_statement_cmd]
unsafe def register_spec_statement : Lean.Elab.Command.CommandElab := fun stx => do
  let info := stx[1]
  let expr ← Command.liftTermElabM do
    elabTerm info (some (mkConst ``SpecInfo))
  let value ← Lean.Elab.Command.liftTermElabM do
    Lean.Meta.evalExpr SpecInfo (mkConst ``SpecInfo) expr
  specAttr.add value

def specStatementLookup (n : Name) : MetaM (Option SpecInfo) := do
  let env ← getEnv
  let state := specAttr.getState env
  return state.specInfos.get? n

end Aeneas
