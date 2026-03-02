import Aeneas.GrindSimpTac.GrindSimpTac
import Aeneas.SimpLists.Init
import Aeneas.SimpLists.SimpLists
import Aeneas.SimpBoolProp.SimpBoolProp
import Aeneas.ScalarTac.Init
import Aeneas.Grind.Init

/-!
# `gsimp_lists`: like `simp_lists` but using `grind` as a discharger

Built on top of `grindSimpTac`.
-/

namespace Aeneas.GrindSimpTac.SimpLists

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Aeneas.GrindSimpTac (GrindSimpArgs grindSimpTac)

def gsimpListsTac (args : ScalarTac.CondSimpPartialArgs) (loc : Utils.Location) : TacticM Unit := do
  let simpArgs : GrindSimpArgs := {
    simpThms := #[← SimpLists.simpListsSimpExt.getTheorems,
                   ← SimpBoolProp.simpBoolPropSimpExt.getTheorems],
    simprocs := #[← SimpLists.simpListsSimprocExt.getSimprocs,
                   ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs],
    declsToUnfold := args.declsToUnfold,
    addSimpThms := args.addSimpThms,
    hypsToUse := args.hypsToUse,
  }
  let grindConfig : Lean.Grind.Config := {
    splits := 4, ematch := 1, splitMatch := false, splitIte := false,
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
    (preprocessHypsToUseSimpThms := #[← SimpLists.simpListsHypsSimpExt.getTheorems,
                                       ← SimpBoolProp.simpBoolPropSimpExt.getTheorems])
    (preprocessHypsToUseSimprocs := #[← SimpLists.simpListsHypsSimprocExt.getSimprocs,
                                       ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs])
    (baseSaturationRounds := 2)

syntax (name := gsimp_lists) "gsimp_lists" ("[" (term<|>"*"),* "]")? (location)? : tactic

elab stx:gsimp_lists : tactic =>
  withMainContext do
  let (args, loc) ← do
    match stx with
    | `(tactic| gsimp_lists $[[$args,*]]? $[$loc:location]?) => do
      let args := args.map (·.getElems) |>.getD #[]
      let args ← ScalarTac.condSimpParseArgs "gsimp_lists" args
      let loc ← Utils.parseOptLocation loc
      pure (args, loc)
    | _ => Lean.Elab.throwUnsupportedSyntax
  gsimpListsTac args loc

end Aeneas.GrindSimpTac.SimpLists
