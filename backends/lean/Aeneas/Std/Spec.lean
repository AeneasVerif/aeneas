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

/-- The type of an `intro_tactic`.

A function registered as an `intro_tactic` must be declared with this type, e.g.
`meta def myIntro : IntroFn := ...`. -/
abbrev IntroFn := Lean.Elab.Tactic.TacticM Nat

structure SpecInfo where
  spec_name : Lean.Name
  arity : Nat
  program_index : Nat -- index into the arguments of the Result value
  post_index : Nat

  mk_spec_mono : Name
  mk_spec_mono_skip_args : Nat -- number of arguments to be inferred, before Result and Post arguments
  mk_spec_bind : Name
  mk_spec_bind_skip_args : Nat

  /-- Name of a function of type `IntroFn` (i.e., `TacticM Nat`) run on the
  mono/bind premise left by the step theorem, to bring it to the `∀ x, P₀ → ... → Pₘ → k ⦃ Q ⦄`
  shape `step` introduces the outputs from.

  It is run on the premise as it stands: it may transform or solve it, but must not create
  multiple goals. What it introduces in the context is reverted, so it can be reintroduced
  later with the names provided by the user.

  It must return the index of the output among the binders of the resulting goal: usually 0. -/
  intro_tactic : Option Lean.Name := none

  /-- Name of a tactic normalizing the goal after output destructuring. -/
  post_intro_tactic : Option Lean.Name := none

  to_mvcgen: Option Name

  liftings : Array LiftingInfo
  deriving Inhabited

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
  if let some fn := value.intro_tactic then
    unless (← getConstInfo fn).type.isConstOf ``IntroFn do
      throwError "`intro_tactic` must be a function of type `Aeneas.IntroFn`, \
        but `{fn}` has type {(← getConstInfo fn).type}"
  specAttr.add value

meta def specInfoLookup (n : Name) : MetaM (Option SpecInfo) := do
  let env ← getEnv
  let state := specAttr.getState env
  return state.specInfos.get? n

end Aeneas
