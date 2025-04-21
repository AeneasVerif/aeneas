import Mathlib.Data.Nat.Bitwise
import Aeneas.SimpLists.Init
import Aeneas.ScalarTac.CondSimpTac

/-!
# `simp_lists` tactic

The `simp_lists` tactic is used to simplify expressions using lists, such as nested
List `get` and `set`.
-/

namespace Aeneas.SimpLists

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

/- Theorems to simplify booleans.

   This is useful because simplifying operations over lists often introduces
   those. As they are quite trivial we expect them to get simplified away
   independently of the simp tactic we're using.
-/
attribute [simp_lists_simps]
  implies_true
  Bool.and_true Bool.true_and
  Bool.false_or Bool.or_false
  Bool.true_or Bool.or_true
  true_or or_true
  true_and and_true
  false_or or_false
  false_and and_false
  decide_eq_false_iff_not ne_eq
  false_eq_decide_iff true_eq_decide_iff
  not_false_eq_true Bool.not_true Bool.not_false
  Bool.not_eq_eq_eq_not
  decide_true decide_false Bool.and_self

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

def simpListsTac (args : ScalarTac.CondSimpPartialArgs) (loc : Utils.Location) : TacticM Unit := do
  let addSimpThms : TacticM (Array FVarId) := pure #[]
  let args : ScalarTac.CondSimpArgs := {
      simpThms := #[← simpListsSimpExt.getTheorems],
      simprocs := #[← simpListsSimprocExt.getSimprocs],
      declsToUnfold := args.declsToUnfold,
      addSimpThms := args.addSimpThms,
      hypsToUse := args.hypsToUse,
    }
  ScalarTac.condSimpTac "simp_lists" false {maxDischargeDepth := 2, failIfUnchanged := false, contextual := true} args addSimpThms false loc

syntax (name := simp_lists) "simp_lists" ("[" (term<|>"*"),* "]")? (location)? : tactic

def parseSimpLists : TSyntax ``simp_lists -> TacticM (ScalarTac.CondSimpPartialArgs × Utils.Location)
| `(tactic| simp_lists $[[$args,*]]?) => do
  let args := args.map (·.getElems) |>.getD #[]
  let args ← ScalarTac.condSimpParseArgs "simp_lists" args
  pure (args, Utils.Location.targets #[] true)
| `(tactic| simp_lists $[[$args,*]]? $[$loc:location]?) => do
  let args := args.map (·.getElems) |>.getD #[]
  let args ← ScalarTac.condSimpParseArgs "simp_lists" args
  let loc ← Utils.parseOptLocation loc
  pure (args, loc)
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:simp_lists : tactic =>
  withMainContext do
  let (args, loc) ← parseSimpLists stx
  simpListsTac args loc

end Aeneas.SimpLists
