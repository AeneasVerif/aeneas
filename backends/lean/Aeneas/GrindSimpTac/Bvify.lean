import Aeneas.GrindSimpTac.GrindSimpTac
import Aeneas.Bvify.Bvify
import Aeneas.SimpBoolProp.SimpBoolProp
import Aeneas.Grind.Init

/-!
# `gbvify`: like `bvify` but using `grind` as a discharger

Built on top of `grindSimpTac`.
-/

namespace Aeneas.GrindSimpTac.Bvify

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Aeneas.GrindSimpTac (GrindSimpArgs grindSimpTac)
open Aeneas.Bvify (bvifyAddSimpThms bvifySimpExt bvifySimprocExt
  bvifyHypsSimpExt bvifyHypsSimprocExt)

def gbvifyTac (n : Expr) (loc : Utils.Location) : TacticM Unit := do
  Elab.Tactic.focus do
  withMainContext do
  -- Add bvify-specific theorems instantiated with `n`
  let addedFVars ← bvifyAddSimpThms n
  let simpArgs : GrindSimpArgs := {
    simpThms := #[← bvifySimpExt.getTheorems,
                   ← SimpBoolProp.simpBoolPropSimpExt.getTheorems],
    simprocs := #[← bvifySimprocExt.getSimprocs,
                   ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs],
    hypsToUse := addedFVars,
  }
  let grindConfig : Lean.Grind.Config := {
    splits := 4, ematch := 5, splitMatch := false, splitIte := false,
    splitIndPred := false, funext := false, gen := 2, instances := 1000,
    canonHeartbeats := 1000
  }
  let extensions := #[Grind.agrindExt.getState (← getEnv)]
  grindSimpTac grindConfig (withGroundSimprocs := true) extensions
    { maxDischargeDepth := 2, failIfUnchanged := false, contextual := true }
    simpArgs loc
    (preprocessSimpThms := #[← ScalarTac.scalarTacSimpExt.getTheorems,
                              ← SimpBoolProp.simpBoolPropSimpExt.getTheorems])
    (preprocessSimprocs := #[← ScalarTac.scalarTacSimprocExt.getSimprocs,
                              ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs])
    (preprocessHypsToUseSimpThms := #[← bvifyHypsSimpExt.getTheorems,
                                       ← SimpBoolProp.simpBoolPropSimpExt.getTheorems])
    (preprocessHypsToUseSimprocs := #[← bvifyHypsSimprocExt.getSimprocs,
                                       ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs])
    (genPreprocess := some 2)
  -- Clear the added theorems from the remaining goal (if any)
  if (← getUnsolvedGoals).length > 0 then
    setGoals [← (← getMainGoal).tryClearMany addedFVars]

syntax (name := gbvify) "gbvify " colGt term (location)? : tactic

elab stx:gbvify : tactic => do
  let (n, loc) ← do
    match stx with
    | `(tactic| gbvify $n:term $[$loc:location]?) => do
      let n ← Elab.Term.elabTerm n (Expr.const ``Nat [])
      let loc ← Utils.parseOptLocation loc
      pure (n, loc)
    | _ => Lean.Elab.throwUnsupportedSyntax
  gbvifyTac n loc

end Aeneas.GrindSimpTac.Bvify
