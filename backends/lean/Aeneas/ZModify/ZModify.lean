import Mathlib.Tactic.Basic
import Mathlib.Tactic.Attr.Register
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Order.Basic
import Aeneas.ZModify.Init
import Aeneas.Arith.Lemmas
import Aeneas.Std.Scalar.Core
import Aeneas.ScalarTac.CondSimpTac
import Aeneas.SimpBoolProp.SimpBoolProp

/-!
# ZMod-ify tactic

The `zmodify` tactic is used to convert propositions about, e.g., `Nat`, to propositions about `ZMod`.
This tactic is adapted from `zify`.
-/

namespace Aeneas.ZModify

open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic
open Arith Std

structure Config where
  nonLin : Bool := true -- We use the non linear lemmas by default
  saturationPasses := 3

declare_config_elab elabConfig Config

attribute [zmodify_simps] ge_iff_le gt_iff_lt Nat.mod_lt_of_lt

theorem Nat.lt_imp_eq_iff_eq_ZMod (n a b : ℕ) (h : a < n ∧ b < n) : a = b ↔ (a : ZMod n) = (b : ZMod n) := by
  have ha := Nat.mod_eq_of_lt h.left
  have hb := Nat.mod_eq_of_lt h.right
  conv => lhs; rw [← ha, ← hb]
  simp [Nat.eq_mod_iff_eq_ZMod]

attribute [zmodify_simps] Nat.mod_lt

/-- `n` is the parameter of `ZMod`, in case it is not obvious from the context.
    In particular, if the user provides `n`, it activates the use of conditional rewritings by means of `scalar_tac`.
 -/
def zmodifyTac (config : Config)
  (n : Option Expr) (args : ScalarTac.CondSimpPartialArgs) (loc : Utils.Location) : TacticM Unit := do
  let addSimpThms : TacticM (Array FVarId) := do
    match n with
    | none => pure #[]
    | some n =>
      let addThm (thName : Name) : TacticM FVarId := do
        let thm ← mkAppM thName #[n]
        Utils.addDeclTac (← Utils.mkFreshAnonPropUserName) thm (← inferType thm) (asLet := false) fun thm => pure thm.fvarId!
      pure #[← addThm ``Nat.lt_imp_eq_iff_eq_ZMod]
  let hypsArgs : ScalarTac.CondSimpArgs := {
      simpThms := #[← zmodifyHypsSimpExt.getTheorems, ← SimpBoolProp.simpBoolPropHypsSimpExt.getTheorems],
      simprocs := #[← zmodifyHypsSimprocExt.getSimprocs, ← SimpBoolProp.simpBoolPropHypsSimprocExt.getSimprocs],
      declsToUnfold := #[],
      addSimpThms := #[],
      hypsToUse := #[],
    }
  let args : ScalarTac.CondSimpArgs := {
      -- Note that we also add the push_cast theorems
      simpThms := #[← zmodifySimpExt.getTheorems, ← SimpBoolProp.simpBoolPropSimpExt.getTheorems, ← Lean.Meta.NormCast.pushCastExt.getTheorems],
      simprocs := #[← zmodifySimprocExt.getSimprocs, ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs],
      declsToUnfold := args.declsToUnfold,
      addSimpThms := args.addSimpThms,
      hypsToUse := args.hypsToUse,
    }
  let config := { nonLin := config.nonLin, saturationPasses := config.saturationPasses }
  ScalarTac.condSimpTac config {maxDischargeDepth := 2, failIfUnchanged := false, contextual := true} hypsArgs args addSimpThms false loc

/--
The `zmodify` ("ZMod-ify") tactic is used to convert propositions about, e.g., `ℕ`, `ℤ`,
`BitVec`, etc., to propositions about `ZMod`.

This tactic is inspired by `zify`.

**Usage**: `zmodify [to <n>] [<simp_args>] [at <loc>]`, where `<n>` is the modulus to use for `ZMod`.
The parameter `<n>` is optional and can be omitted if the tactic can infer it from the context.
For instance, `zmodify` will successfully infer it should use `256` if the goal is `⊢ a % 256 = b % 256`.

One can give lemmas to `zmodify` by annotating them with the attribute `@[zmodify_simps]`,
or by passing them directly as arguments to the tactic, e.g., `zmodify [my_lemma1, my_lemma2]`.
-/
syntax (name := zmodify) "zmodify" Parser.Tactic.optConfig ("to" term)? ("[" (term<|>"*"),* "]")? (location)? : tactic

def parseZModify :
TSyntax ``zmodify -> TacticM (Config × Option Expr × ScalarTac.CondSimpPartialArgs × Utils.Location)
| `(tactic| zmodify $config $[to $n]? $[[$args,*]]? $[$loc:location]?) => do
  let config ← elabConfig config
  let n ← Utils.optElabTerm n
  let args := args.map (·.getElems) |>.getD #[]
  let args ← ScalarTac.condSimpParseArgs "zmodify" args
  let loc ← Utils.parseOptLocation loc
  pure (config, n, args, loc)
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:zmodify : tactic =>
  withMainContext do
  let (config, n, args, loc) ← parseZModify stx
  zmodifyTac config n args loc

attribute [zmodify_simps] Nat.eq_mod_iff_eq_ZMod Int.eq_mod_iff_eq_ZMod div_to_ZMod
attribute [zmodify_simps] Nat.reduceGcd

attribute [zmodify_simps] ZMod.natCast_val ZMod.natCast_mod ZMod.cast_id' ZMod.intCast_mod id_eq
attribute [zmodify_simps] Int.cast_add Int.cast_natCast Int.cast_mul
attribute [zmodify_simps] Int.reduceNeg

@[zmodify_simps]
theorem Nat.eq_mod_zero_iff_eq_ZMod (n : ℕ) (a : Nat) : a % n = 0 ↔ (a : ZMod n) = 0 := by
  have : 0 = 0 % n := by simp only [Nat.zero_mod]
  rw [this]
  simp only [Nat.eq_mod_iff_eq_ZMod, Nat.cast_zero]

@[zmodify_simps]
theorem Nat.eq_zero_mod_iff_eq_ZMod (n : ℕ) (a : Nat) : 0 = a % n ↔ 0 = (a : ZMod n) := by
  have : 0 = 0 % n := by simp only [Nat.zero_mod]
  rw [this]
  simp only [Nat.eq_mod_iff_eq_ZMod, Nat.cast_zero]

@[zmodify_simps]
theorem Int.eq_zero_mod_iff_eq_ZMod (n : ℕ) (a : ℤ) : 0 = a % n ↔ 0 = (a : ZMod n) := by
  have : (0 : Int) = 0 % n := by simp only [EuclideanDomain.zero_mod]
  rw [this]
  simp only [Int.eq_mod_iff_eq_ZMod, Int.cast_zero]

@[zmodify_simps]
theorem Int.eq_mod_zero_iff_eq_ZMod (n : ℕ) (a : ℤ) : a % n = 0 ↔ (a : ZMod n) = 0 := by
  have : (0 : Int) = 0 % n := by simp only [EuclideanDomain.zero_mod]
  rw [this]
  simp only [Int.eq_mod_iff_eq_ZMod, Int.cast_zero]

@[zmodify_simps]
theorem Nat.mod_eq_iff (n : ℕ) (a b : ℕ) : a % n = b ↔ ((b < n ∨ n = 0) ∧ (a : ZMod n) = (b : ZMod n)) := by
  by_cases h: b < n
  . have := Nat.mod_eq_of_lt h
    simp [*, ← Nat.eq_mod_iff_eq_ZMod]
  . simp [*]
    by_cases hn : n = 0
    . simp [*, ← Nat.eq_mod_iff_eq_ZMod]
    . simp [*, ← Nat.eq_mod_iff_eq_ZMod]
      have := @Nat.mod_lt a n  (by omega)
      omega

@[zmodify_simps]
theorem Nat.eq_mod_iff (n : ℕ) (a b : ℕ) : a = b % n ↔ ((a < n ∨ n = 0) ∧ (a : ZMod n) = (b : ZMod n)) := by
  have : a = b % n ↔ b % n = a := by tauto
  rw [this]
  simp only [mod_eq_iff, and_congr_right_iff]
  tauto

/- We introduce this lemma because of the case `n = 0` in the lemma above -/
@[zmodify_simps]
theorem Nat.ne_zero_imp_eq_zero_false (n : ℕ) (h : ¬ n = 0) : (n = 0) ↔ False := by simp [*]

@[zmodify_simps]
theorem Nat.lt_imp_lt (a b : ℕ) : a < b → a < b := by simp +contextual

/- This example comes from Verus:
   https://verus-lang.github.io/verus/guide/nonlinear.html#example-1-integer_ring-as-a-helper-lemma-to-provide-facts-on-modular-arithmetic -/
example (x y d : ℕ) (h0 : d > 0) (h1 : x <= y) (h2 : x % d <= y % d) (h3 : y - x < d) :
  y % d - x % d = y - x := by
  zmodify to d

/-- Checking that unfolding of local declarations works properly -/
example (x y : U32) (hx : x.val < 8) (hy : y.val < 8) :
  let z := x.val + y.val
  z < 16 := by
  intro z
  zmodify [z]

end Aeneas.ZModify
