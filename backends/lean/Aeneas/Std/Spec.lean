module
public import Lean
public import AeneasMeta.Extensions
public section
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

/-- Reshape the current entailment into an equivalent quantified target, without
introducing variables. Return the number of leading output binders; `step` introduces
these before the postconditions. Declare callbacks with this type alias. -/
abbrev PrepareIntroOutputs := Elab.Tactic.TacticM Nat

structure SpecInfo where
  spec_name : Lean.Name
  arity : Nat
  program_index : Nat -- index into the arguments of the Result value
  post_index : Nat

  mk_spec_mono : Name
  mk_spec_mono_skip_args : Nat -- number of arguments to be inferred, before Result and Post arguments
  mk_spec_bind : Name
  mk_spec_bind_skip_args : Nat

  /-- Name of a `PrepareIntroOutputs` callback. For example, given `qimp_spec P k Q`
  with call-site pattern `(a, b)`, `Aeneas.Step.prepareIntroOutputs` changes the goal
  to `∀ a b, imp (P (a, b)) (spec (k (a, b)) Q)` and returns `2`.
  It proves equivalence before changing the goal; `step` then introduces variables.
  Both `spec` and `dspec` register `prepare_intro_outputs := ``Aeneas.Step.prepareIntroOutputs`. -/
  prepare_intro_outputs : Name

  to_mvcgen: Option Name

  liftings : Array LiftingInfo
  deriving Inhabited

private meta unsafe def evalPrepareIntroOutputsUnsafe (name : Name) :
    Elab.Tactic.TacticM PrepareIntroOutputs :=
  Lean.evalConstCheck PrepareIntroOutputs ``PrepareIntroOutputs name

/-- Load a registered preparation callback, checking its type before evaluating it. -/
@[implemented_by evalPrepareIntroOutputsUnsafe]
meta opaque evalPrepareIntroOutputs (name : Name) : Elab.Tactic.TacticM PrepareIntroOutputs

meta structure SpecInfoExtensionState where
  specInfos : Std.HashMap Name SpecInfo
  deriving Inhabited

/- Initialize the state extension for adding spec theorems -/
meta initialize specAttr : SimpleScopedEnvExtension SpecInfo SpecInfoExtensionState  ← do
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
meta unsafe def register_spec_info : Lean.Elab.Command.CommandElab := fun stx => do
  let info := stx[1]
  let expr ← Command.liftTermElabM do
    elabTerm info (some (mkConst ``SpecInfo))
  let value ← Lean.Elab.Command.liftTermElabM do
    Lean.Meta.evalExpr SpecInfo (mkConst ``SpecInfo) expr
  let some callback := (← getEnv).find? value.prepare_intro_outputs
    | throwErrorAt info "Unknown output-preparation callback `{value.prepare_intro_outputs}`"
  unless callback.type == Lean.mkConst ``PrepareIntroOutputs do
    throwErrorAt info "Invalid output-preparation callback `{value.prepare_intro_outputs}`: \
      declare it with type `Aeneas.PrepareIntroOutputs`"
  specAttr.add value

meta def specInfoLookup (n : Name) : MetaM (Option SpecInfo) := do
  let env ← getEnv
  let state := specAttr.getState env
  return state.specInfos.get? n

end Aeneas
