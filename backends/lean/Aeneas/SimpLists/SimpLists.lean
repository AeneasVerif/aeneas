import Mathlib.Data.Nat.Bitwise
import Aeneas.SimpLists.Init
import Aeneas.ScalarTac.CondSimpTac
import Aeneas.SimpBoolProp.SimpBoolProp

/-!
# `simp_lists` tactic

The `simp_lists` tactic is used to simplify expressions using lists, such as nested
List `get` and `set`.
-/

namespace Aeneas.SimpLists

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

/- We need some basic arithmetic simplification theorems to simplify the
   indices we use to access the lists. We try to keep these to a minimum -
   for more aggressive arithmetic simplifications one should use `simp_scalar`.
-/
attribute [simp_lists_simps]
  add_tsub_cancel_right add_tsub_cancel_left
  zero_add add_zero

/- Adding theorems about `testBit`.

   We do this because `testBit` can be considered as a getter for the ith bit
   of a number, so it makes sense to use `simp_lists` to reason about it.
-/
attribute [simp_lists_simps]
  Nat.testBit_two_pow_add_gt Nat.testBit_eq_false_of_lt
  Nat.testBit_two_pow Nat.testBit_mod_two_pow
  Nat.testBit_shiftRight Nat.testBit_shiftLeft
  Nat.testBit_add_one
  Nat.testBit_two_pow_add_eq

attribute [simp_lists_simps] List.map_map List.map_id_fun List.map_id_fun' id_eq
attribute [simp_lists_simps] Fin.getElem!_fin

def simpListsTac (config : ScalarTac.CondSimpTacConfig)
  (args : ScalarTac.CondSimpPartialArgs) (loc : Utils.Location) : TacticM Unit := do
  let addSimpThms : TacticM (Array FVarId) := pure #[]
  let hypsArgs : ScalarTac.CondSimpArgs := {
      simpThms := #[← simpListsHypsSimpExt.getTheorems, ← SimpBoolProp.simpBoolPropHypsSimpExt.getTheorems],
      simprocs := #[← simpListsHypsSimprocExt.getSimprocs, ← SimpBoolProp.simpBoolPropHypsSimprocExt.getSimprocs],
      declsToUnfold := #[],
      addSimpThms := #[],
      hypsToUse := #[],
    }
  let args : ScalarTac.CondSimpArgs := {
      simpThms := #[← simpListsSimpExt.getTheorems, ← SimpBoolProp.simpBoolPropSimpExt.getTheorems],
      simprocs := #[← simpListsSimprocExt.getSimprocs, ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs],
      declsToUnfold := args.declsToUnfold,
      addSimpThms := args.addSimpThms,
      hypsToUse := args.hypsToUse,
    }
  ScalarTac.condSimpTac "simp_lists" config {maxDischargeDepth := 2, failIfUnchanged := false, contextual := true} hypsArgs args addSimpThms false loc

syntax (name := simp_lists) "simp_lists" Parser.Tactic.optConfig ("[" (term<|>"*"),* "]")? (location)? : tactic

def parseSimpLists :
TSyntax ``simp_lists -> TacticM (ScalarTac.CondSimpTacConfig × ScalarTac.CondSimpPartialArgs × Utils.Location)
| `(tactic| simp_lists $config $[[$args,*]]? $[$loc:location]?) => do
  let config ← ScalarTac.elabCondSimpTacConfig config
  let args := args.map (·.getElems) |>.getD #[]
  let args ← ScalarTac.condSimpParseArgs "simp_lists" args
  let loc ← Utils.parseOptLocation loc
  pure (config, args, loc)
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:simp_lists : tactic =>
  withMainContext do
  let (config, args, loc) ← parseSimpLists stx
  simpListsTac config args loc

end Aeneas.SimpLists
