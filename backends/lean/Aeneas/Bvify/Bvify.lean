import Aeneas.Bvify.Init
import Aeneas.Arith.Lemmas
import Aeneas.Std.Scalar
import Aeneas.Std.PrimitivesLemmas
import Aeneas.Std.Scalar.CoreConvertNum -- we need this for the tests
import Aeneas.ScalarTac.CondSimpTac
import Aeneas.SimpBoolProp.SimpBoolProp
import Aeneas.Grind.Init

/-!
# `bvify` tactic

The `bvify` tactic is used to shift propositions about, e.g., `Nat`, to `BitVec`.
This tactic is adapted from `zify`.
-/

namespace Aeneas.Bvify

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Arith Std

structure Config where
  nonLin : Bool := true -- We use the non linear lemmas by default
  saturationPasses := 3

declare_config_elab elabConfig Config

/- Simp procedures -/
attribute [bvify_simps]
  reduceIte
  Nat.reduceLeDiff Nat.reduceLT Nat.reduceGT Nat.reduceBEq Nat.reduceBNe
  Nat.reducePow Nat.reduceAdd Nat.reduceSub Nat.reduceMul Nat.reduceDiv Nat.reduceMod
  Int.reduceLT Int.reduceLE Int.reduceGT Int.reduceGE Int.reduceEq Int.reduceNe Int.reduceBEq Int.reduceBNe
  Int.reducePow Int.reduceAdd Int.reduceSub Int.reduceMul Int.reduceDiv Int.reduceMod
  Int.reduceNegSucc Int.reduceNeg Int.reduceToNat
  BitVec.reduceMul BitVec.reduceAdd BitVec.reduceSub BitVec.reduceMod BitVec.reduceDiv
  Nat.dvd_iff_mod_eq_zero
  BitVec.ofNat_or BitVec.ofNat_and

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem U8.UScalar_bv (x : U8) : UScalar.bv x = x.bv := by simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem U16.UScalar_bv (x : U16) : UScalar.bv x = x.bv := by simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem U32.UScalar_bv (x : U32) : UScalar.bv x = x.bv := by simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem U64.UScalar_bv (x : U64) : UScalar.bv x = x.bv := by simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem U128.UScalar_bv (x : U128) : UScalar.bv x = x.bv := by simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem Usize.UScalar_bv (x : Usize) : UScalar.bv x = x.bv := by simp

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem I8.IScalar_bv (x : I8) : IScalar.bv x = x.bv := by simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem I16.IScalar_bv (x : I16) : IScalar.bv x = x.bv := by simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem I32.IScalar_bv (x : I32) : IScalar.bv x = x.bv := by simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem I64.IScalar_bv (x : I64) : IScalar.bv x = x.bv := by simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem I128.IScalar_bv (x : I128) : IScalar.bv x = x.bv := by simp
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem Isize.IScalar_bv (x : Isize) : IScalar.bv x = x.bv := by simp

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem UScalar.bv_setWidth (x : UScalar ty) : x.bv.setWidth ty.numBits = x.bv := by simp only [BitVec.setWidth_eq]

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem U8.bv_setWidth (x : U8) : x.bv.setWidth 8 = x.bv := UScalar.bv_setWidth x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem U16.bv_setWidth (x : U16) : x.bv.setWidth 16 = x.bv := UScalar.bv_setWidth x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem U32.bv_setWidth (x : U32) : x.bv.setWidth 32 = x.bv := UScalar.bv_setWidth x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem U64.bv_setWidth (x : U64) : x.bv.setWidth 64 = x.bv := UScalar.bv_setWidth x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem U128.bv_setWidth (x : U128) : x.bv.setWidth 128 = x.bv := UScalar.bv_setWidth x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem Usize.bv_setWidth (x : Usize) : x.bv.setWidth System.Platform.numBits = x.bv := UScalar.bv_setWidth x

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem IScalar.bv_signExtend (x : IScalar ty) : x.bv.signExtend ty.numBits = x.bv := by
  simp only [BitVec.signExtend, IScalar.bv_toInt_eq, IScalar.BitVec_ofInt_val]

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem I8.bv_signExtend (x : I8) : x.bv.signExtend 8 = x.bv := IScalar.bv_signExtend x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem I16.bv_signExtend (x : I16) : x.bv.signExtend 16 = x.bv := IScalar.bv_signExtend x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem I32.bv_signExtend (x : I32) : x.bv.signExtend 32 = x.bv := IScalar.bv_signExtend x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem I64.bv_signExtend (x : I64) : x.bv.signExtend 64 = x.bv := IScalar.bv_signExtend x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem I128.bv_signExtend (x : I128) : x.bv.signExtend 128 = x.bv := IScalar.bv_signExtend x
@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem Isize.bv_signExtend (x : Isize) : x.bv.signExtend System.Platform.numBits = x.bv := IScalar.bv_signExtend x

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =]
theorem UScalar.cast_bv (x : UScalar ty) : (UScalar.cast tgt x).bv = x.bv.setWidth tgt.numBits := by
  simp

theorem BitVec.lt_pow_ofNat_le {n : Nat} (a b : Nat) (h0 : b < 2^n) (h1 : a ≤ b) :
  BitVec.ofNat n a ≤ BitVec.ofNat n b := by
  have : 0 < 2^n := by simp
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; omega
  have : b % 2^n = b := by apply Nat.mod_eq_of_lt; omega
  simp [*]

theorem BitVec.lt_pow_le_iff_ofNat_le (n a b : Nat) (h0 : a < 2^n) (h1 : b < 2^n) :
  a ≤ b ↔ BitVec.ofNat n a ≤ BitVec.ofNat n b := by
  constructor <;> intro h2
  . apply BitVec.lt_pow_ofNat_le <;> assumption
  . simp at h2
    have : a % 2^n = a := by apply Nat.mod_eq_of_lt; assumption
    have : b % 2^n = b := by apply Nat.mod_eq_of_lt; assumption
    omega

/- Grouping the preconditions into one: this is better when using `scalar_tac` to discharge the preconditions
   because it is only called once, leading to less preprocessing. -/
theorem BitVec.lt_pow_le_iff_ofNat_le' (n a b : Nat) (h : a < 2^n ∧ b < 2^n) :
  a ≤ b ↔ BitVec.ofNat n a ≤ BitVec.ofNat n b := by
  apply BitVec.lt_pow_le_iff_ofNat_le <;> simp [*]

theorem BitVec.lt_pow_ofNat_lt (n a b : Nat) (h0 : b < 2^n) (h0 : a < b) :
  BitVec.ofNat n a < BitVec.ofNat n b := by
  have : 0 < 2^n := by simp
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; omega
  have : b % 2^n = b := by apply Nat.mod_eq_of_lt; omega
  simp [*]

theorem BitVec.lt_pow_lt_iff_ofNat_lt {n : Nat} (a b : Nat) (h0 : a < 2^n) (h1 : b < 2^n) :
  a < b ↔ BitVec.ofNat n a < BitVec.ofNat n b := by
  constructor <;> intro h2
  . apply BitVec.lt_pow_ofNat_lt <;> assumption
  . simp at h2
    have : a % 2^n = a := by apply Nat.mod_eq_of_lt; assumption
    have : b % 2^n = b := by apply Nat.mod_eq_of_lt; assumption
    omega

/- TODO: we may want to use bvify_forward on this one?
   It is better to have it as bvify_forward for the assumptions (because then we don't need the condition a < 2^n)
   but we also an equivalence for the lemma to be usable on the goals. -/
theorem BitVec.lt_pow_lt_iff_ofNat_lt' (n a b : Nat) (h : a < 2^n ∧ b < 2^n) :
  a < b ↔ BitVec.ofNat n a < BitVec.ofNat n b := by
  apply BitVec.lt_pow_lt_iff_ofNat_lt <;> simp [*]

theorem BitVec.lt_pow_lt_ofNat_le (n a b : Nat) (h0 : a < b) (h1 : b - 1 < 2^n) :
  BitVec.ofNat n a ≤ BitVec.ofNat n (b - 1) := by
  simp
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; omega
  have : (b - 1) % 2^n = b - 1 := by apply Nat.mod_eq_of_lt; assumption
  omega

theorem BitVec.lt_pow_n_iff_ofNat_le (n a : Nat) (h : a < 2^n) :
  a < 2^n ↔ BitVec.ofNat n a ≤ BitVec.ofNat n (2^n - 1) := by
  constructor
  . intro h
    simp only [BitVec.ofNat_le_ofNat, Nat.self_sub_mod]
    have : a % 2^n = a := by apply Nat.mod_eq_of_lt; omega
    omega
  . simp [*]

@[bvify_simps]
theorem Nat.mod_le_imp_mod_le (a b c : Nat) (h : b ≠ 0 ∧ (a < c ∨ b ≤ c)) : a % b < c := by
  obtain ⟨ h0, h1 ⟩ := h
  cases h1
  . have := @Nat.mod_le a b
    omega
  . have := @Nat.mod_lt a b (by omega)
    omega

attribute [bvify_simps] ge_iff_le gt_iff_lt decide_eq_true_eq BitVec.ofNat_add

theorem BitVec.iff_ofNat_eq (n a b : Nat) (ha : a < 2^n) (hb : b < 2^n) :
  a = b ↔ BitVec.ofNat n a = BitVec.ofNat n b := by
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; assumption
  have : b % 2^n = b := by apply Nat.mod_eq_of_lt; assumption
  simp only [BitVec.toNat_eq, BitVec.toNat_ofNat, *]

theorem BitVec.iff_ofNat_eq' (n a b : Nat) (h : a < 2^n ∧ b < 2^n) :
  a = b ↔ BitVec.ofNat n a = BitVec.ofNat n b := by
  apply BitVec.iff_ofNat_eq <;> simp [*]

theorem BitVec.ofNat_mod (n : Nat) (a b : Nat) (ha : a < 2^n) (hb : b < 2^n) :
  BitVec.ofNat n (a % b) = BitVec.ofNat n a % BitVec.ofNat n b := by
  simp [BitVec.toNat_eq]
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; assumption
  have : b % 2^n = b := by apply Nat.mod_eq_of_lt; assumption
  dcases b = 0
  . simp_all only [Nat.ofNat_pos, pow_pos, Nat.zero_mod, Nat.mod_zero]
  . have := @Nat.mod_lt a b (by omega)
    have : (a % b) % 2^n  = a % b:= by apply Nat.mod_eq_of_lt; omega
    simp only [*]

@[bvify_simps]
theorem BitVec.ofNat_mod' (n a b : Nat) (h : a < 2^n ∧ b < 2^n) :
  BitVec.ofNat n (a % b) = BitVec.ofNat n a % BitVec.ofNat n b := by
  apply BitVec.ofNat_mod <;> simp [*]

@[bvify_simps]
theorem BitVec.ofNat_sub' (n a b : Nat) (h : b ≤ a) :
  BitVec.ofNat n (a - b) = BitVec.ofNat n a - BitVec.ofNat n b := by
  simp [BitVec.toNat_eq]
  zify
  have : (a - b : Nat) = (a : Int) - (b : Int) := by omega
  rw [this]; clear this
  have := @Nat.mod_lt b (2^n) (by simp)
  have : (2^n - b%2^n : Nat) = ((2^n : Nat) : Int) - (b % 2^n  : Nat):= by omega
  rw [this]; clear this
  simp
  have : (2 ^ n : Int) - (b : Int) % 2 ^ n + (a : Int) =
         (2 ^ n : Int) + ((a : Int) - (b : Int) % 2 ^ n) := by ring_nf
  rw [this]; clear this
  simp only [Int.add_emod_left]
  rw [Int.sub_emod]
  conv => rhs; rw [Int.sub_emod]
  simp only [dvd_refl, Int.emod_emod_of_dvd]

@[bvify_simps]
theorem BitVec.ofNat_mul (n a b : Nat) :
  BitVec.ofNat n (a * b) = BitVec.ofNat n a * BitVec.ofNat n b := by
  simp

@[bvify_simps]
theorem BitVec.ofNat_div (n a b : Nat)
  (h : a < 2^n ∧ b < 2^n) :
  BitVec.ofNat n (a / b) = BitVec.ofNat n a / BitVec.ofNat n b := by
  simp only [BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_udiv]
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; omega
  have : b % 2^n = b := by apply Nat.mod_eq_of_lt; omega
  have : a / b ≤ a := by apply Nat.div_le_self
  have : (a / b) % 2^n = a / b := by apply Nat.mod_eq_of_lt; omega
  simp only [*]

attribute [bvify_simps] ZMod.eq_iff_mod ZMod.val_add ZMod.val_sub ZMod.val_mul ZMod.val_sub' ZMod.val_natCast
attribute [bvify_simps] Nat.add_one_sub_one Nat.add_mod_mod Nat.mod_add_mod

@[simp, simp_scalar_simps, bvify_simps]
theorem BitVec.ofNat_shift_UScalar_val (x : UScalar ty) (n : Nat) :
  BitVec.ofNat ty.numBits (x.val >>> n) = x.bv >>> n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, UScalar.bv_toNat]
  have : x.val >>> n ≤ x.val := by
    simp [Nat.shiftRight_eq_div_pow]
    apply Nat.div_le_self
  have : (x.val >>> n) % 2^ty.numBits = x.val >>> n := by
    apply Nat.mod_eq_of_lt
    have := x.hBounds
    scalar_tac
  rw [this]

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem BitVec.ofNat_shift_U8_val (x : U8) (n : Nat) :
  BitVec.ofNat 8 (x.val >>> n) = x.bv >>> n := BitVec.ofNat_shift_UScalar_val x n

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem BitVec.ofNat_shift_U16_val (x : U16) (n : Nat) :
  BitVec.ofNat 16 (x.val >>> n) = x.bv >>> n := BitVec.ofNat_shift_UScalar_val x n

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem BitVec.ofNat_shift_U32_val (x : U32) (n : Nat) :
  BitVec.ofNat 32 (x.val >>> n) = x.bv >>> n := BitVec.ofNat_shift_UScalar_val x n

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem BitVec.ofNat_shift_U64_val (x : U64) (n : Nat) :
  BitVec.ofNat 64 (x.val >>> n) = x.bv >>> n := BitVec.ofNat_shift_UScalar_val x n

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem BitVec.ofNat_shift_U128_val (x : U128) (n : Nat) :
  BitVec.ofNat 128 (x.val >>> n) = x.bv >>> n := BitVec.ofNat_shift_UScalar_val x n

@[simp, simp_scalar_simps, bvify_simps, grind =, agrind =] theorem BitVec.ofNat_shift_Usize_val (x : Usize) (n : Nat) :
  BitVec.ofNat System.Platform.numBits (x.val >>> n) = x.bv >>> n := BitVec.ofNat_shift_UScalar_val x n

/-!
Simplification lemmas about `setWidth`
-/
attribute [bvify_simps] BitVec.setWidth_eq

@[simp, simp_scalar_simps, bvify_simps, simp_scalar_simps, grind =, agrind =]
theorem UScalar.BitVec_ofNat_setWidth (x : UScalar ty) : BitVec.ofNat n x.val = x.bv.setWidth n := by
  simp only [UScalar.val, BitVec.toNat_eq]; simp

syntax (name := bvify_saturate) "bvify_saturate" colGe term : tactic

/-!
Some theorems which automatically lift comparisons between machine scalars, without needing the number of bits to be provided by the user.
-/

attribute [bvify_simps] UScalar.eq_equiv_bv_eq IScalar.eq_equiv_bv_eq
                        gt_iff_lt ge_iff_le true_and and_true

@[bvify_simps]
theorem UScalar.lt_equiv_bv_lt {ty : UScalarTy} (x y : UScalar ty) : x < y ↔ x.bv < y.bv := by rfl

@[bvify_simps]
theorem UScalar.le_equiv_bv_le {ty : UScalarTy} (x y : UScalar ty) : x ≤ y ↔ x.bv ≤ y.bv := by rfl

def bvifyAddSimpThms (n : Expr) : TacticM (Array FVarId) := do
  let addThm (thName : Name) : TacticM FVarId := do
    let thm ← mkAppM thName #[n]
    Utils.addDeclTac (← Utils.mkFreshAnonPropUserName) thm (← inferType thm) (asLet := false) fun thm => pure thm.fvarId!
  let le_iff ← addThm ``BitVec.lt_pow_le_iff_ofNat_le'
  let lt_iff ← addThm ``BitVec.lt_pow_lt_iff_ofNat_lt'
  let lt_max_iff ← addThm ``BitVec.lt_pow_n_iff_ofNat_le
  let eq_iff ← addThm ``BitVec.iff_ofNat_eq'
  pure #[le_iff, lt_iff, lt_max_iff, eq_iff]

def bvifySimpConfig : Simp.Config := {maxDischargeDepth := 2, failIfUnchanged := false}

def bvifyTacSimp (loc : Utils.Location) : TacticM (Option (Array FVarId)) := do
  let args : ScalarTac.CondSimpArgs := {
      simpThms := #[← bvifySimpExt.getTheorems, ← SimpBoolProp.simpBoolPropSimpExt.getTheorems]
      simprocs := #[← bvifySimprocExt.getSimprocs, ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs]
    }
  ScalarTac.condSimpTacSimp bvifySimpConfig args loc #[] #[] none

def bvifyTac (config : Config) (n : Expr) (loc : Utils.Location) : TacticM Unit := do
  let hypsArgs : ScalarTac.CondSimpArgs := {
      simpThms := #[← bvifyHypsSimpExt.getTheorems]
      simprocs := #[← bvifyHypsSimprocExt.getSimprocs]
    }
  let args : ScalarTac.CondSimpArgs := {
      simpThms := #[← bvifySimpExt.getTheorems, ← SimpBoolProp.simpBoolPropSimpExt.getTheorems]
      simprocs := #[← bvifySimprocExt.getSimprocs, ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs]
    }
  let config := { nonLin := config.nonLin, saturationPasses := config.saturationPasses }
  ScalarTac.condSimpTac config bvifySimpConfig hypsArgs args (bvifyAddSimpThms n) true loc

/--
The `bvify` (to be read "bv-ify") tactic is used to lift propositions about, e.g., `Nat`, to `BitVec`.
This tactic is inspired from `zify` which converts propositions about `ℕ` to propositions about `ℤ`.

**Usage**: `bvify <n> [at <loc>]`, where `<n>` is the number of bits to use for the `BitVec`
representation.

**Example:**
```lean
example (x y : U8) (h : x.val < y.val) : x.bv < y.bv := by
  bvify 8 at h -- turns `h` into: `h : x.bv < y.bv`
  apply h
```

**Adding custom lemmas:**
One can give lemmas to `bvify` by annotating them with the attribute `@[bvify_simps]`,
or by passing them directly as arguments to the tactic, e.g., `bvify [my_lemma1, my_lemma2]`.

**Remark:**
This kind of conversions does not come for free and requires some proof obligations to be discharged.
For instance, one can convert `a < b` into `BitVec.ofNat n a < BitVec.ofNat n b` only when `b < 2^n`
(`n` is the number of bits used for the `BitVec`).

In case `bvify` fails to lift some inequality, a workaround consists in writing the expected assumption
with an `have` (e.g., `have h' : BitVec.ofNat n a < BitVec.ofNat n b := ...`), and proving it by using
`natify`, `simp_scalar` (to get rid of, e.g., the modulos introduced in the conversion) and `simp`.
-/
syntax (name := bvify) "bvify " colGt Parser.Tactic.optConfig term (location)? : tactic

def parseBvify : TSyntax ``bvify -> TacticM (Config × Expr × Utils.Location)
| `(tactic| bvify $config $n:term $[$loc:location]?) => do
  let config ← elabConfig config
  -- TODO: if we forget the number of bits the error messages are spurious
  trace[Bvify] "Number of bits: {n}"
  let n ← Elab.Term.elabTerm n (Expr.const ``Nat [])
  trace[Bvify] "Number of bits after elaboration: {n}"
  let loc ← Utils.parseOptLocation loc
  pure (config, n, loc)
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:bvify : tactic => do
  let (config, n, loc) ← parseBvify stx
  bvifyTac config n loc

example (x y : U8) (h : x.val < y.val) : x.bv < y.bv := by
  bvify 8 at h
  apply h

example (x y : U8) (h : x.val < y.val) : x.bv < y.bv := by
  bvify 8 at *
  bv_decide

example (x : U8) (h : x.val < 32) : x.bv < 32#8 := by
  bvify 8 at h
  apply h

example (x : U8) (h : x.val < 32) : x.bv < 32#8 := by
  bvify 8 at *
  apply h

example (a : U32) (h : a.val = 3329) : a.bv = 3329#32 := by
  bvify 32 at *
  apply h

/--
info: example
  (a : U32)
  (b : U32)
  (c : U32)
  (h0 : c.bv ≤ 3329#32)
  (h1 : a.bv + b.bv ≤ 3329#32 + c.bv) :
  a.bv + b.bv ≤ 3329#32 + c.bv
  := by sorry
-/
#guard_msgs in
set_option linter.unusedTactic false in
example (a b c : U32) (h0 : c.val ≤ 3329) (h1 : a.val + b.val ≤ 3329 + c.val) : a.bv + b.bv ≤ 3329#32 + c.bv := by
  bvify 32 at *
  extract_goal1
  assumption

example (n a : Nat) (h : a < 2^n) : BitVec.ofNat n a ≤ BitVec.ofNat n (2^n - 1) := by
  bvify n at *
  tauto

/--
info: example
  (a : U32)
  (b : U32)
  (c : U32)
  (h : a.bv + b.bv < 32#32)
  (hc : c.bv = a.bv + b.bv) :
  c.bv % 32#32 = (a.bv + b.bv) % 32#32
  := by sorry
-/
#guard_msgs in
set_option linter.unusedTactic false in
example
  (a b c : U32) (h : a.val + b.val < 32) (hc : c.val = a.val + b.val) :
  (c.val : ZMod 32) = (a.val : ZMod 32) + (b.val : ZMod 32) := by
  bvify 32 at *
  extract_goal1
  bv_decide

example
  (a : U32)
  (b : U32)
  (ha : (↑a : ℕ) < 3329)
  (hb : (↑b : ℕ) < 3329)
  (c1 : U32)
  (hc1 : (↑c1 : ℕ) = (↑a : ℕ) + (↑b : ℕ))
  (_ : c1.bv = a.bv + b.bv)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv - 3329#32)
  (c3 : U32)
  (hc3 : c3.bv = c2.bv >>> 16)
  (c4 : U32)
  (hc4 : (↑c4 : ℕ) = (↑(3329#u32 &&& c3) : ℕ))
  (_ : c4.bv = 3329#32 &&& c3.bv)
  (c5 : U32)
  (hc5 : c5.bv = c2.bv + c4.bv) :
  (c5.val : ZMod 3329) = (a.val : ZMod 3329) + (b.val : ZMod 3329) ∧ c5.val < 3329
  := by
  bvify 32 at *
  simp_all only
  bv_decide

example
  (a : U32)
  (b : U32)
  (_ : a.val ≤ 6658)
  (ha : a.val < b.val + 3329)
  (hb : b.val ≤ 3329)
  (c1 : U32)
  (hc1 : c1.bv = a.bv - b.bv)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16)
  (c3 : U32)
  (_ : c3.bv = 3329#32 &&& c2.bv)
  (c4 : U32)
  (hc3 : c4 = c1.bv + c3.bv) :
  (c4.val : ZMod 3329) = (a.val : ZMod 3329) - (b.val : ZMod 3329) ∧
  c4.val < 3329
  := by
  bvify 32 at *
  simp_all only
  bv_decide

example
  (x : U16) (_ : x.val < 3329)
  (y : U32) (_ : y = core.convert.num.FromU32U16.from x) :
  y.val = x.val
  := by
  bvify 32 at *
  bv_decide

example
  (x : U32) (_ : x.val < 3329)
  (y : U16) (_ : y = UScalar.cast UScalarTy.U16 x) :
  y.val = x.val
  := by
  bvify 16 at *
  bv_decide

example (x : U64) : x.val >>> 31 < 2^33 := by
  bvify 64
  bv_decide

/--
info: example
  (x : U32)
  (a : U32)
  (b : U32)
  (h : x.bv = a.bv + b.bv) :
  x.bv % 3329#32 = (a.bv + b.bv) % 3329#32
  := by sorry
-/
#guard_msgs in
set_option linter.unusedTactic false in
example (x a b : U32) (h : x.val = a.val + b.val) : (x.val : ZMod 3329) = (a.val : ZMod 3329) + (b.val : ZMod 3329) := by
  bvify 32 at *
  extract_goal1
  simp [h]

example (byte : U8) : 8 ∣ (byte &&& 16#u8).val := by
  bvify 8; bv_decide

end Aeneas.Bvify
