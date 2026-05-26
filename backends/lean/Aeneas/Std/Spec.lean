import Lean
import AeneasMeta.Extensions
-- import Aeneas.Tactic.Step.Init
open Lean Elab Term Meta

namespace Aeneas
open Extensions

-- This file defines an extension for defining spec statements that
-- can be used with the step tactic.

-- structure SpecInfo where
--   name : Lean.Name
--   arity : Nat
--   mk_spec_mono : Array Lean.Expr → Lean.Expr → Lean.Expr
--   mk_spec_bind : Array Lean.Expr → Lean.Expr → Lean.Expr
--   -- discr_tree_key : Array Lean.Expr → Array Lean.Expr
--   program_index : Nat -- index into the arguments of the Result value

--   uncurry_elim_tactics : Array Lean.Name
--   qimp_elim_tactics : Array Lean.Name
--   deriving Inhabited -- why does the value type for an extension need to be Inhabited?

-- structure SpecInfoExtensionState where
--   specInfos : Std.HashMap Name SpecInfo

-- /- Initiliaze the `spec` attribute. -/
-- initialize specAttr : SimpleScopedEnvExtension SpecInfo SpecInfoExtensionState ← do
--   let ext ← registerSimpleScopedEnvExtension {
--     name        := `specStatementRegistrationExtension,
--     initial     := {
--       specInfos := Std.HashMap.emptyWithCapacity
--     },
--     addEntry    := fun state new =>
--       {state with specInfos := state.specInfos.insert new.name new},
--   }
--   pure ext

-- syntax (name := register_spec_statement_cmd)
--   "#register_spec_statement " term : command

-- @[command_elab register_spec_statement_cmd]
-- unsafe def register_spec_statement : Lean.Elab.Command.CommandElab := fun stx => do
--   let bla := stx[1]
--   let expr ← Command.liftTermElabM do
--     elabTerm bla (some (mkConst ``SpecInfo))
--   let value ← Lean.Elab.Command.liftTermElabM do
--     Lean.Meta.evalExpr SpecInfo (mkConst ``SpecInfo) expr
--   specAttr.add value

-- details that are specific to particular kinds of spec statements, like `spec` of `dspec`
-- unsafe def specStatementLookup : Name → SpecInfo
--   | ``Std.WP.spec => {
--     name := ``Std.WP.spec
--     arity := 3
--     mk_spec_mono := fun _args thm => thm
--     mk_spec_bind := fun _args thm => thm
--     uncurry_elim_tactics := #[]
--     qimp_elim_tactics := #[]
--     program_index := 1
--   }
--   | ``Std.WP.dspec => {
--     name := ``Std.WP.dspec
--     arity := 3
--     mk_spec_mono := fun _args thm => thm
--     mk_spec_bind := fun _args thm => thm
--     uncurry_elim_tactics := #[]
--     qimp_elim_tactics := #[]
--     program_index := 1
--   }
--   | _ => panic! "not a valid spec statement"


end Aeneas
