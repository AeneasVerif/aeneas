import Aeneas.SimpIfs.Init
import Aeneas.SimpBoolProp.SimpBoolProp
import Aeneas.ScalarTac.CondSimpTac

/-!
# `simp_ifs` tactic

The `simp_ifs` tactic is used to simplify expressions `if then else` expressions
-/

namespace Aeneas.SimpIfs

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

def simpIfsTac (config : ScalarTac.CondSimpTacConfig)
  (args : ScalarTac.CondSimpPartialArgs) (loc : Utils.Location) : TacticM Unit := do
  let addSimpThms : TacticM (Array FVarId) := pure #[]
  let hypsArgs : ScalarTac.CondSimpArgs := {
      simpThms := #[← simpIfsHypsSimpExt.getTheorems, ← SimpBoolProp.simpBoolPropHypsSimpExt.getTheorems],
      simprocs := #[← simpIfsHypsSimprocExt.getSimprocs, ← SimpBoolProp.simpBoolPropHypsSimprocExt.getSimprocs],
      declsToUnfold := #[],
      addSimpThms := #[],
      hypsToUse := #[],
    }
  let args : ScalarTac.CondSimpArgs := {
      simpThms := #[← simpIfsSimpExt.getTheorems, ← SimpBoolProp.simpBoolPropSimpExt.getTheorems],
      simprocs := #[← simpIfsSimprocExt.getSimprocs, ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs],
      declsToUnfold := args.declsToUnfold,
      addSimpThms := args.addSimpThms,
      hypsToUse := args.hypsToUse,
    }
  ScalarTac.condSimpTac config {maxDischargeDepth := 2, failIfUnchanged := false} hypsArgs args addSimpThms false loc

/-- `simp_ifs` simplifies `if then else` expressions exclusively.

This is particularly useful when one wants to simplify a function in the goal without having to resort
to a cumbersome gymnastic to simplify exactly the `if then else` expression.

It works by following the same principle as `simp_scalar` - see the documentation of `simp_scalar` for more details.
-/
syntax (name := simp_ifs) "simp_ifs" Parser.Tactic.optConfig ("[" term,* "]")? (location)? : tactic

@[simp_ifs_simps]
theorem if_true {α} (b : Prop) [Decidable b] (x y : α) (hb : b) : (if b then x else y) = x := by
  simp only [hb, ↓reduceIte]

@[simp_ifs_simps]
theorem if_false {α} (b : Prop) [Decidable b] (x y : α) (hb : ¬ b) : (if b then x else y) = y := by
  simp only [hb, ↓reduceIte]

@[simp_ifs_simps]
theorem dite_true {α} (c : Prop) [Decidable c] (h : c) (t : c → α) (e : ¬c → α) :
  dite c t e = t h := by simp [h]

@[simp_ifs_simps]
theorem dite_fase {α} (c : Prop) [Decidable c] (h : ¬ c) (t : c → α) (e : ¬c → α) :
  dite c t e = e h := by simp [h]

def parseSimpIfs :
TSyntax ``simp_ifs -> TacticM (ScalarTac.CondSimpTacConfig × ScalarTac.CondSimpPartialArgs × Utils.Location)
| `(tactic| simp_ifs $config $[[$args,*]]? $[$loc:location]?) => do
  let config ← ScalarTac.elabCondSimpTacConfig config
  let args := args.map (·.getElems) |>.getD #[]
  let args ← ScalarTac.condSimpParseArgs "simp_ifs" args
  let loc ← Utils.parseOptLocation loc
  pure (config, args, loc)
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:simp_ifs : tactic =>
  withMainContext do
  let (config, args, loc) ← parseSimpIfs stx
  simpIfsTac config args loc

example {α} [Inhabited α] (i j : Nat) (h :i ≥ j ∧ i < j + 1) : (if i = j then 0 else 1) = 0 := by
  simp_ifs

end Aeneas.SimpIfs
