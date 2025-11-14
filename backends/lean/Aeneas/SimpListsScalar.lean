import Aeneas.SimpLists
import Aeneas.SimpScalar

namespace Aeneas.SimpListsScalar

/-!
# `simp_lists_scalar` tactic

The `simp_lists_scalar` tactic is a combination of `simp_lists` and `simp_scalar`.
-/

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

def simpListsScalarTac (config : ScalarTac.CondSimpTacConfig)
  (args : ScalarTac.CondSimpPartialArgs) (loc : Utils.Location) : TacticM Unit := do
  let addSimpThms : TacticM (Array FVarId) := pure #[]
  let hypsArgs : ScalarTac.CondSimpArgs := {
      simpThms := #[
        ← SimpBoolProp.simpBoolPropHypsSimpExt.getTheorems,
        ← SimpLists.simpListsHypsSimpExt.getTheorems,
        ← SimpScalar.simpScalarHypsSimpExt.getTheorems],
      simprocs := #[
        ← SimpBoolProp.simpBoolPropHypsSimprocExt.getSimprocs,
        ← SimpLists.simpListsHypsSimprocExt.getSimprocs,
        ← SimpScalar.simpScalarHypsSimprocExt.getSimprocs
        ],
      declsToUnfold := #[],
      addSimpThms := #[],
      hypsToUse := #[],
    }
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
  ScalarTac.condSimpTac config {maxDischargeDepth := 2, failIfUnchanged := false, contextual := true} hypsArgs args addSimpThms false loc

/-- `simp_lists_scalar` simplifies expressions involving lists and scalars.

It is a combination of `simp_scalar` and `simp_lists` - see the documentation of `simp_scalar` for more details.

You can mark lemmas to be used by `simp_lists_scalar` by annotating them with the attribute `@[simp_lists_scalar]`,
or by passing them as arguments to the tactic, e.g., `simp_lists [my_lemma1, my_lemma2]`.
-/
syntax (name := simp_lists) "simp_lists_scalar" Parser.Tactic.optConfig ("[" (term<|>"*"),* "]")? (location)? : tactic

def parseSimpListsScalar :
TSyntax ``simp_lists -> TacticM (ScalarTac.CondSimpTacConfig × ScalarTac.CondSimpPartialArgs × Utils.Location)
| `(tactic| simp_lists_scalar $config $[[$args,*]]? $[$loc:location]?) => do
  let config ← ScalarTac.elabCondSimpTacConfig config
  let args := args.map (·.getElems) |>.getD #[]
  let args ← ScalarTac.condSimpParseArgs "simp_lists_scalar" args
  let loc ← Utils.parseOptLocation loc
  pure (config, args, loc)
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:simp_lists : tactic =>
  withMainContext do
  let (config, args, loc) ← parseSimpListsScalar stx
  simpListsScalarTac config args loc

end Aeneas.SimpListsScalar
