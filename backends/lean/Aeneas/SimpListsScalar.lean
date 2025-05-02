import Aeneas.SimpLists
import Aeneas.SimpScalar

namespace Aeneas.SimpListsScalar

/-!
# `simp_lists_scalar` tactic

The `simp_lists_scalar` tactic is a combination of `simp_lists` and `simp_scalar`.
-/

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

def simpListsScalarTac (args : ScalarTac.CondSimpPartialArgs) (loc : Utils.Location) : TacticM Unit := do
  let addSimpThms : TacticM (Array FVarId) := pure #[]
  let args : ScalarTac.CondSimpArgs := {
      simpThms := #[
        ← SimpBoolProp.simpBoolPropSimpExt.getTheorems,
        ← SimpLists.simpListsSimpExt.getTheorems,
        ← SimpScalar.simpScalarSimpExt.getTheorems],
      simprocs := #[
        ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs,
        ← SimpLists.simpListsSimprocExt.getSimprocs,
        ← SimpScalar.simpScalarSimprocExt.getSimprocs
        ],
      declsToUnfold := args.declsToUnfold,
      addSimpThms := args.addSimpThms,
      hypsToUse := args.hypsToUse,
    }
  ScalarTac.condSimpTac "simp_lists_scalar" false {maxDischargeDepth := 2, failIfUnchanged := false, contextual := true} args addSimpThms false loc

syntax (name := simp_lists) "simp_lists_scalar" ("[" (term<|>"*"),* "]")? (location)? : tactic

def parseSimpListsScalar : TSyntax ``simp_lists -> TacticM (ScalarTac.CondSimpPartialArgs × Utils.Location)
| `(tactic| simp_lists_scalar $[[$args,*]]?) => do
  let args := args.map (·.getElems) |>.getD #[]
  let args ← ScalarTac.condSimpParseArgs "simp_lists_scalar" args
  pure (args, Utils.Location.targets #[] true)
| `(tactic| simp_lists_scalar $[[$args,*]]? $[$loc:location]?) => do
  let args := args.map (·.getElems) |>.getD #[]
  let args ← ScalarTac.condSimpParseArgs "simp_lists_scalar" args
  let loc ← Utils.parseOptLocation loc
  pure (args, loc)
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:simp_lists : tactic =>
  withMainContext do
  let (args, loc) ← parseSimpListsScalar stx
  simpListsScalarTac args loc

end Aeneas.SimpListsScalar
