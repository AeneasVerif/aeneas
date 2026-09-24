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

structure SpecInfo where
  spec_name : Lean.Name
  arity : Nat
  program_index : Nat -- index into the arguments of the Result value
  post_index : Nat

  mk_spec_mono : Name
  mk_spec_mono_skip_args : Nat -- number of arguments to be inferred, before Result and Post arguments
  mk_spec_bind : Name
  mk_spec_bind_skip_args : Nat

  /-- Name of a tactic run on the mono/bind premise left by the step theorem, to bring it
  to the `∀ x, P₀ → ... → Pₘ → k ⦃ Q ⦄` shape `step` introduces the outputs from.

  It is run on the premise as it stands: it may transform or solve it, but must not create
  multiple goals. What it introduces in the context is reverted, so it can introduce the
  binders of the premise and work on the facts among them — `Aeneas.Step.Intro.intro_split`
  does exactly that, and is all a statement whose premise already is `∀ x, P x → …` needs.

  A tactic which reorders binders must record the output with
  `Aeneas.Step.Intro.markOutputIndex`.

  Without one, `step` introduces the outputs of the premise as it stands. -/
  intro_tactic : Option Lean.Name := none

  /-- Optional normalization after output destructuring; it must not create multiple goals. -/
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
  specAttr.add value

meta def specInfoLookup (n : Name) : MetaM (Option SpecInfo) := do
  let env ← getEnv
  let state := specAttr.getState env
  return state.specInfos.get? n

end Aeneas
