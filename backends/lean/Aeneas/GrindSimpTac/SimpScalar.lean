import Aeneas.GrindSimpTac.GrindSimpTac
import Aeneas.SimpScalar.Init
import Aeneas.SimpScalar.SimpScalar
import Aeneas.SimpBoolProp.SimpBoolProp
import Aeneas.ScalarTac.Init
import Aeneas.Grind.Init

/-!
# `gsimp_scalar`: like `simp_scalar` but using `grind` as a discharger

Built on top of `grindSimpTac`.
-/

namespace Aeneas.GrindSimpTac.SimpScalar

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Aeneas.GrindSimpTac (GrindSimpArgs grindSimpTac)

def gsimpScalarTac (args : ScalarTac.CondSimpPartialArgs) (loc : Utils.Location) : TacticM Unit := do
  let simpArgs : GrindSimpArgs := {
    simpThms := #[← SimpScalar.simpScalarSimpExt.getTheorems,
                   ← SimpBoolProp.simpBoolPropSimpExt.getTheorems],
    simprocs := #[← SimpScalar.simpScalarSimprocExt.getSimprocs,
                   ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs],
    declsToUnfold := args.declsToUnfold,
    addSimpThms := args.addSimpThms,
    hypsToUse := args.hypsToUse,
  }
  let grindConfig : Lean.Grind.Config := {
    splits := 4, ematch := 5, splitMatch := false, splitIte := false,
    splitIndPred := false, funext := false, gen := 2, instances := 1000,
    canonHeartbeats := 1000
  }
  let extensions := #[← Lean.Meta.Grind.getDefaultExtensionState, Grind.agrindExt.getState (← getEnv)]
  grindSimpTac grindConfig (withGroundSimprocs := true) extensions
    { maxDischargeDepth := 2, failIfUnchanged := false, contextual := true }
    simpArgs loc
    (preprocessSimpThms := #[← ScalarTac.scalarTacSimpExt.getTheorems,
                              ← SimpBoolProp.simpBoolPropSimpExt.getTheorems])
    (preprocessSimprocs := #[← ScalarTac.scalarTacSimprocExt.getSimprocs,
                              ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs])
    (preprocessHypsToUseSimpThms := #[← SimpScalar.simpScalarHypsSimpExt.getTheorems,
                                       ← SimpBoolProp.simpBoolPropSimpExt.getTheorems])
    (preprocessHypsToUseSimprocs := #[← SimpScalar.simpScalarHypsSimprocExt.getSimprocs,
                                       ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs])
    (genPreprocess := some 2)

syntax (name := gsimp_scalar) "gsimp_scalar" ("[" (term<|>"*"),* "]")? (location)? : tactic

elab stx:gsimp_scalar : tactic =>
  withMainContext do
  let (args, loc) ← do
    match stx with
    | `(tactic| gsimp_scalar $[[$args,*]]? $[$loc:location]?) => do
      let args := args.map (·.getElems) |>.getD #[]
      let args ← ScalarTac.condSimpParseArgs "gsimp_scalar" args
      let loc ← Utils.parseOptLocation loc
      pure (args, loc)
    | _ => Lean.Elab.throwUnsupportedSyntax
  gsimpScalarTac args loc

end Aeneas.GrindSimpTac.SimpScalar
