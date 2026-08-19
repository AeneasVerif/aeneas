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
  spec_name : Lean.Name
  arity : Nat
  program_index : Nat -- index into the arguments of the Result value
  post_index : Nat

  mk_spec_mono : Name
  mk_spec_mono_skip_args : Nat -- number of arguments to be inferred, before Result and Post arguments
  mk_spec_bind : Name
  mk_spec_bind_skip_args : Nat

  /-- Name of a zero-argument tactic applied on mono's and bind's preconditions in `step`
      and mono's final goal in `step*`, provided as its raw `Name`.
      Failure leaves the precondition/goal unchanged. -/
  discharge_tactic : Option Name := none

  uncurry_elim_tactics : Array Lean.Name := #[]
  /-- Tactic run on the goal.
  It may transform or solve the goal, but must not create multiple goals. -/
  intro_tactic : Option (TSyntax `tactic) := none
  qimp_elim_tactics : Array Lean.Name := #[]

  to_mvcgen: Option Name

  liftings : Array LiftingInfo
  deriving Inhabited

/-- Store tactic syntax in a `SpecInfo`, for example:
    ``intro_tactic := SpecInfo.tac `(tactic| my_tactic)``. -/
def SpecInfo.tac (tac : Unhygienic (TSyntax `tactic)) : Option (TSyntax `tactic) :=
  some (Unhygienic.run tac)

structure SpecInfoExtensionState where
  specInfos : Std.HashMap Name SpecInfo
  deriving Inhabited

/- Initialize the state extension for adding spec theorems -/
initialize specAttr : SimpleScopedEnvExtension SpecInfo SpecInfoExtensionState  ← do
  let ext ← registerSimpleScopedEnvExtension {
    name        := `specStatementRegistrationExtension,
    initial     := {
      specInfos := Std.HashMap.emptyWithCapacity
    },
    addEntry    := fun state new =>
      {state with specInfos := state.specInfos.insert new.spec_name new},
  }
  pure ext

syntax (name := register_spec_info_cmd)
  "#register_spec_info " term : command

@[command_elab register_spec_info_cmd]
unsafe def register_spec_info : Lean.Elab.Command.CommandElab := fun stx => do
  let info := stx[1]
  let expr ← Command.liftTermElabM do
    elabTerm info (some (mkConst ``SpecInfo))
  let value ← Lean.Elab.Command.liftTermElabM do
    Lean.Meta.evalExpr SpecInfo (mkConst ``SpecInfo) expr
  if let some tacticName := value.discharge_tactic then
    match Parser.runParserCategory (← getEnv) `tactic tacticName.toString with
    | .ok _ => pure ()
    | .error error => throwErrorAt info
        "Could not parse registered discharge tactic `{tacticName}`: {error}"
  specAttr.add value

def specInfoLookup (n : Name) : MetaM (Option SpecInfo) := do
  let env ← getEnv
  let state := specAttr.getState env
  return state.specInfos.get? n

end Aeneas
