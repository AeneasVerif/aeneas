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

/-- Type of a function that `step` uses to reshape the target before introducing
the outputs.

See `SpecInfo.prepare_intro_output` -/
abbrev PrepareIntroOutputs := Elab.Tactic.TacticM Nat

/-- Type of a tactic that `step` and `step*` use to discharge goals.

See `SpecInfo.discharge_tactic` -/
abbrev DischargeTactic := Elab.Tactic.TacticM Unit

structure SpecInfo where
  spec_name : Lean.Name
  arity : Nat
  program_index : Nat -- index into the arguments of the Result value
  post_index : Nat

  mk_spec_mono : Name
  mk_spec_mono_skip_args : Nat -- number of arguments to be inferred, before Result and Post arguments
  mk_spec_bind : Name
  mk_spec_bind_skip_args : Nat

  /-- Name of a `PrepareIntroOutputs` callback.

  The `step` tactic uses this callback to reshape the target before introducing the outputs,
  so that we have the proper number of properly named local variables.

  For instance, it should turn a goal of the shape:
  `forall x, ((a, b) c => P a b c) x → e ⦃ Q ⦄`, where `x` is the output and
  `((a, b) c => P a b c)` the post-condition of a let-binder we just processed,
  while `e ⦃ Q ⦄` is the goal we have to prove about the remaining continuation,
  into: `forall a b c, P a b c → e ⦃ Q ⦄`, so that `step` can then introduce the
  `a`, `b` and `c` into the context. -/
  prepare_intro_outputs : Name

  /-- Name of a tactic normalizing the goal after output destructuring. -/
  post_intro_tactic : Option Lean.Name := none

  /-- Name of a `DischargeTactic` callback (optional).

  This lets a specification come with a dedicated tactic for the goals it generates
  (e.g., with separation logic, applying `iframe` to each entailment).

  When `step` applies the mono or bind theorem, the theorem's preconditions become
  new goals, and its ghost variables become metavariables.
  `step` first tries this callback on each precondition, before `singleAssumptionTac` and
  the generic solvers (`simp`, `grind`, `scalar_tac`). Ghost variables are filled in when a
  precondition that mentions them is solved.
  `step*` also tries it on the final goal, which usually has the same shape as those
  preconditions (for instance, a magic wand application).

  If the tactic does not solve the goal, `step`/`step*` revert any modification it performed. -/
  discharge_tactic : Option Name := none

  to_mvcgen: Option Name

  liftings : Array LiftingInfo
  deriving Inhabited

private meta unsafe def evalPrepareIntroOutputsUnsafe (name : Name) :
    Elab.Tactic.TacticM PrepareIntroOutputs :=
  Lean.evalConstCheck PrepareIntroOutputs ``PrepareIntroOutputs name

/-- Load a registered preparation callback, checking its type before evaluating it. -/
@[implemented_by evalPrepareIntroOutputsUnsafe]
meta opaque evalPrepareIntroOutputs (name : Name) : Elab.Tactic.TacticM PrepareIntroOutputs

private meta unsafe def evalDischargeTacticUnsafe (name : Name) :
    Elab.Tactic.TacticM DischargeTactic :=
  Lean.evalConstCheck DischargeTactic ``DischargeTactic name

/-- Load a registered discharge tactic, checking its type before evaluating it. -/
@[implemented_by evalDischargeTacticUnsafe]
meta opaque evalDischargeTactic (name : Name) : Elab.Tactic.TacticM DischargeTactic

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

  -- checking if the discharge tactic is public so that step*? provides a proof script
  -- that can be applied
  if let some dischargeTactic := value.discharge_tactic then
    let some callback := (← getEnv).find? dischargeTactic
      | throwErrorAt info "Unknown discharge tactic `{dischargeTactic}`"
    if isPrivateName dischargeTactic then
      throwErrorAt info "Private discharge tactic `{privateToUserName dischargeTactic}`: \
        declare it with `public meta def`"
    unless callback.type == Lean.mkConst ``DischargeTactic do
      throwErrorAt info "Invalid discharge tactic `{dischargeTactic}`: \
        declare it with type `Aeneas.DischargeTactic`"
  specAttr.add value

meta def specInfoLookup (n : Name) : MetaM (Option SpecInfo) := do
  let env ← getEnv
  let state := specAttr.getState env
  return state.specInfos.get? n

end Aeneas
