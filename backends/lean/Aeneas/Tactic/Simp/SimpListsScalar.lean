import Aeneas.Tactic.Simp.SimpLists
import Aeneas.Tactic.Simp.SimpScalar

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
  let mut simpThms : Array SimpTheorems := #[
    ← SimpBoolProp.simpBoolPropSimpExt.getTheorems,
    ← SimpLists.simpListsSafeSimpExt.getTheorems,
    ← SimpScalar.simpScalarSafeSimpExt.getTheorems]
  let mut simprocs : Simp.SimprocsArray := #[
    ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs,
    ← SimpLists.simpListsSafeSimprocExt.getSimprocs,
    ← SimpScalar.simpScalarSafeSimprocExt.getSimprocs]
  if !config.safe then
    simpThms := simpThms.push (← SimpLists.simpListsSimpExt.getTheorems)
      |>.push (← SimpScalar.simpScalarSimpExt.getTheorems)
    simprocs := simprocs.push (← SimpLists.simpListsSimprocExt.getSimprocs)
      |>.push (← SimpScalar.simpScalarSimprocExt.getSimprocs)
  let args : ScalarTac.CondSimpArgs := {
      simpThms,
      simprocs,
      declsToUnfold := args.declsToUnfold,
      addSimpThms := args.addSimpThms,
      hypsToUse := args.hypsToUse,
    }
  ScalarTac.condSimpTac config {maxDischargeDepth := 2, failIfUnchanged := false, contextual := true} hypsArgs args addSimpThms false loc

/-- `simp_lists_scalar` simplifies expressions involving lists and scalars.

It is a combination of `simp_scalar` and `simp_lists`, essentially equivalent to
`simp (discharger := scalar_tac) [simp_bool_prop, simp_lists_safe, simp_lists, simp_scalar_safe, simp_scalar]`
but implemented in a way which allows factoring out most of the preprocessing step of `scalar_tac`, resulting
in a significant gain in performance.

See the documentation of `simp_scalar` for more details.

You can mark lemmas to be used by `simp_lists_scalar` by annotating them with `@[simp_lists]`,
`@[simp_lists_safe]`, `@[simp_scalar]`, or `@[simp_scalar_safe]`,
or by passing them as arguments to the tactic, e.g., `simp_lists_scalar [my_lemma1, my_lemma2]`.

The `+safe` option restricts `simp_lists_scalar` to only the safe lemmas (`@[simp_lists_safe]`
and `@[simp_scalar_safe]`).
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
