import Mathlib.Data.Nat.Bitwise
import Aeneas.Tactic.Simp.SimpLists.Init
import Aeneas.Tactic.Solver.ScalarTac.CondSimpTac
import Aeneas.Tactic.Simp.SimpBoolProp.SimpBoolProp

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
attribute [simp_lists_safe]
  add_tsub_cancel_right add_tsub_cancel_left
  zero_add add_zero

/- Adding theorems about `testBit`.

   We do this because `testBit` can be considered as a getter for the ith bit
   of a number, so it makes sense to use `simp_lists` to reason about it.
-/
attribute [simp_lists_safe]
  Nat.testBit_two_pow_add_gt Nat.testBit_eq_false_of_lt
  Nat.testBit_two_pow Nat.testBit_mod_two_pow
  Nat.testBit_shiftRight Nat.testBit_shiftLeft
  Nat.testBit_add_one
  Nat.testBit_two_pow_add_eq

attribute [simp_lists_safe] List.map_map List.map_id_fun List.map_id_fun' id_eq
attribute [simp_lists_safe] Fin.getElem!_fin
attribute [simp_lists_safe] List.length_map List.length_flatMap
attribute [simp_lists_safe] List.length_cons List.length_nil

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
  let mut simpThms := #[← simpListsSafeSimpExt.getTheorems, ← SimpBoolProp.simpBoolPropSimpExt.getTheorems]
  let mut simprocs := #[← simpListsSafeSimprocExt.getSimprocs, ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs]
  if !config.safe then
    simpThms := simpThms.push (← simpListsSimpExt.getTheorems)
    simprocs := simprocs.push (← simpListsSimprocExt.getSimprocs)
  let args : ScalarTac.CondSimpArgs := {
      simpThms,
      simprocs,
      declsToUnfold := args.declsToUnfold,
      addSimpThms := args.addSimpThms,
      hypsToUse := args.hypsToUse,
    }
  ScalarTac.condSimpTac config {maxDischargeDepth := 2, failIfUnchanged := false, contextual := true} hypsArgs args addSimpThms false loc

/-- `simp_lists` simplifies expressions involving lists, in particular when they have getters and setters.

It works by following the same principle as `simp_scalar`, but focuses on lists instead of scalars - see the
documentation of `simp_scalar` for more details.

It can simplify an expression like `List.get (List.set (List.set l i v0) j v1) i` to `v1` when `i ≠ j`,
or `List.get (l0 ++ l1) i` to `List.get l1 (i - l0.length)` when `i ≥ l0.length`, etc.

You can mark lemmas to be used by `simp_lists` by annotating them with:
- `@[simp_lists_safe]` for safe lemmas (always used, even with `simp_lists +safe`)
- `@[simp_lists]` for general lemmas (only used when `safe` is `false`, which is the default)

The `+safe` option restricts `simp_lists` to only the safe lemmas.
-/
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
