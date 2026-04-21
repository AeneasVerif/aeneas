import Aeneas.Tactic.Conv.Bvify.Init
import Aeneas.Tactic.Solver.Arith.Lemmas
import Aeneas.Std.Scalar
import Aeneas.Std.PrimitivesLemmas
import Aeneas.Std.Scalar.CoreConvertNum -- we need this for the tests
import Aeneas.Tactic.Solver.ScalarTac.CondSimpTac
import Aeneas.Tactic.Simp.SimpBoolProp.SimpBoolProp
import Aeneas.Tactic.Solver.Grind.Init

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
attribute [bvify]
  reduceIte
  Nat.reduceLeDiff Nat.reduceLT Nat.reduceGT Nat.reduceBEq Nat.reduceBNe
  Nat.reducePow Nat.reduceAdd Nat.reduceSub Nat.reduceMul Nat.reduceDiv Nat.reduceMod
  Int.reduceLT Int.reduceLE Int.reduceGT Int.reduceGE Int.reduceEq Int.reduceNe Int.reduceBEq Int.reduceBNe
  Int.reducePow Int.reduceAdd Int.reduceSub Int.reduceMul Int.reduceDiv Int.reduceMod
  Int.reduceNegSucc Int.reduceNeg Int.reduceToNat
  BitVec.reduceMul BitVec.reduceAdd BitVec.reduceSub BitVec.reduceMod BitVec.reduceDiv
  Nat.dvd_iff_mod_eq_zero
  BitVec.ofNat_or BitVec.ofNat_and

@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem U8.UScalar_toBitVec (x : U8) : UScalar.toBitVec x = x.toBitVec := by simp
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem U16.UScalar_toBitVec (x : U16) : UScalar.toBitVec x = x.toBitVec := by simp
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem U32.UScalar_toBitVec (x : U32) : UScalar.toBitVec x = x.toBitVec := by simp
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem U64.UScalar_toBitVec (x : U64) : UScalar.toBitVec x = x.toBitVec := by simp
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem U128.UScalar_toBitVec (x : U128) : UScalar.toBitVec x = x.toBitVec := by simp
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem Usize.UScalar_toBitVec (x : Usize) : UScalar.toBitVec x = x.toBitVec := by simp

@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem I8.IScalar_toBitVec (x : I8) : IScalar.toBitVec x = x.toBitVec := by simp
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem I16.IScalar_toBitVec (x : I16) : IScalar.toBitVec x = x.toBitVec := by simp
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem I32.IScalar_toBitVec (x : I32) : IScalar.toBitVec x = x.toBitVec := by simp
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem I64.IScalar_toBitVec (x : I64) : IScalar.toBitVec x = x.toBitVec := by simp
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem I128.IScalar_toBitVec (x : I128) : IScalar.toBitVec x = x.toBitVec := by simp
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem Isize.IScalar_toBitVec (x : Isize) : IScalar.toBitVec x = x.toBitVec := by simp

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem UScalar.toBitVec_setWidth (x : UScalar ty) : x.toBitVec.setWidth ty.numBits = x.toBitVec := by simp only [BitVec.setWidth_eq]

@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem U8.toBitVec_setWidth (x : U8) : x.toBitVec.setWidth 8 = x.toBitVec := UScalar.toBitVec_setWidth x
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem U16.toBitVec_setWidth (x : U16) : x.toBitVec.setWidth 16 = x.toBitVec := UScalar.toBitVec_setWidth x
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem U32.toBitVec_setWidth (x : U32) : x.toBitVec.setWidth 32 = x.toBitVec := UScalar.toBitVec_setWidth x
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem U64.toBitVec_setWidth (x : U64) : x.toBitVec.setWidth 64 = x.toBitVec := UScalar.toBitVec_setWidth x
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem U128.toBitVec_setWidth (x : U128) : x.toBitVec.setWidth 128 = x.toBitVec := UScalar.toBitVec_setWidth x
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem Usize.toBitVec_setWidth (x : Usize) : x.toBitVec.setWidth System.Platform.numBits = x.toBitVec := UScalar.toBitVec_setWidth x

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem IScalar.toBitVec_signExtend (x : IScalar ty) : x.toBitVec.signExtend ty.numBits = x.toBitVec := by
  simp only [BitVec.signExtend, IScalar.toBitVec_toInt_eq, IScalar.BitVec_ofInt_toInt]

@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem I8.toBitVec_signExtend (x : I8) : x.toBitVec.signExtend 8 = x.toBitVec := IScalar.toBitVec_signExtend x
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem I16.toBitVec_signExtend (x : I16) : x.toBitVec.signExtend 16 = x.toBitVec := IScalar.toBitVec_signExtend x
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem I32.toBitVec_signExtend (x : I32) : x.toBitVec.signExtend 32 = x.toBitVec := IScalar.toBitVec_signExtend x
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem I64.toBitVec_signExtend (x : I64) : x.toBitVec.signExtend 64 = x.toBitVec := IScalar.toBitVec_signExtend x
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem I128.toBitVec_signExtend (x : I128) : x.toBitVec.signExtend 128 = x.toBitVec := IScalar.toBitVec_signExtend x
@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem Isize.toBitVec_signExtend (x : Isize) : x.toBitVec.signExtend System.Platform.numBits = x.toBitVec := IScalar.toBitVec_signExtend x

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem UScalar.cast_toBitVec (x : UScalar ty) : (UScalar.cast tgt x).toBitVec = x.toBitVec.setWidth tgt.numBits := by
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

@[bvify]
theorem Nat.mod_le_imp_mod_le (a b c : Nat) (h : b ≠ 0 ∧ (a < c ∨ b ≤ c)) : a % b < c := by
  obtain ⟨ h0, h1 ⟩ := h
  cases h1
  . have := @Nat.mod_le a b
    omega
  . have := @Nat.mod_lt a b (by omega)
    omega

attribute [bvify] ge_iff_le gt_iff_lt decide_eq_true_eq BitVec.ofNat_add

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

@[bvify]
theorem BitVec.ofNat_mod' (n a b : Nat) (h : a < 2^n ∧ b < 2^n) :
  BitVec.ofNat n (a % b) = BitVec.ofNat n a % BitVec.ofNat n b := by
  apply BitVec.ofNat_mod <;> simp [*]

@[bvify]
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

@[bvify]
theorem BitVec.ofNat_mul (n a b : Nat) :
  BitVec.ofNat n (a * b) = BitVec.ofNat n a * BitVec.ofNat n b := by
  simp

@[bvify]
theorem BitVec.ofNat_div (n a b : Nat)
  (h : a < 2^n ∧ b < 2^n) :
  BitVec.ofNat n (a / b) = BitVec.ofNat n a / BitVec.ofNat n b := by
  simp only [BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_udiv]
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; omega
  have : b % 2^n = b := by apply Nat.mod_eq_of_lt; omega
  have : a / b ≤ a := by apply Nat.div_le_self
  have : (a / b) % 2^n = a / b := by apply Nat.mod_eq_of_lt; omega
  simp only [*]

attribute [bvify] ZMod.eq_iff_mod ZMod.val_add ZMod.val_sub ZMod.val_mul ZMod.val_sub' ZMod.val_natCast
attribute [bvify] Nat.add_one_sub_one Nat.add_mod_mod Nat.mod_add_mod

@[simp, simp_scalar_safe, bvify]
theorem BitVec.ofNat_shift_UScalar_val (x : UScalar ty) (n : Nat) :
  BitVec.ofNat ty.numBits (x.toNat >>> n) = x.toBitVec >>> n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, UScalar.toBitVec_toNat]
  have : x.toNat >>> n ≤ x.toNat := by
    simp [Nat.shiftRight_eq_div_pow]
    apply Nat.div_le_self
  have : (x.toNat >>> n) % 2^ty.numBits = x.toNat >>> n := by
    apply Nat.mod_eq_of_lt
    have := x.hBounds
    scalar_tac
  rw [this]

@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem BitVec.ofNat_shift_U8_val (x : U8) (n : Nat) :
  BitVec.ofNat 8 (x.toNat >>> n) = x.toBitVec >>> n := BitVec.ofNat_shift_UScalar_val x n

@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem BitVec.ofNat_shift_U16_val (x : U16) (n : Nat) :
  BitVec.ofNat 16 (x.toNat >>> n) = x.toBitVec >>> n := BitVec.ofNat_shift_UScalar_val x n

@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem BitVec.ofNat_shift_U32_val (x : U32) (n : Nat) :
  BitVec.ofNat 32 (x.toNat >>> n) = x.toBitVec >>> n := BitVec.ofNat_shift_UScalar_val x n

@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem BitVec.ofNat_shift_U64_val (x : U64) (n : Nat) :
  BitVec.ofNat 64 (x.toNat >>> n) = x.toBitVec >>> n := BitVec.ofNat_shift_UScalar_val x n

@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem BitVec.ofNat_shift_U128_val (x : U128) (n : Nat) :
  BitVec.ofNat 128 (x.toNat >>> n) = x.toBitVec >>> n := BitVec.ofNat_shift_UScalar_val x n

@[simp, simp_scalar_safe, bvify, grind =, agrind =] theorem BitVec.ofNat_shift_Usize_val (x : Usize) (n : Nat) :
  BitVec.ofNat System.Platform.numBits (x.toNat >>> n) = x.toBitVec >>> n := BitVec.ofNat_shift_UScalar_val x n

/-!
Simplification lemmas about `setWidth`
-/
attribute [bvify] BitVec.setWidth_eq

@[simp, simp_scalar_safe, bvify, grind =, agrind =]
theorem UScalar.BitVec_ofNat_setWidth (x : UScalar ty) : BitVec.ofNat n x.toNat = x.toBitVec.setWidth n := by
  simp only [UScalar.toNat, BitVec.toNat_eq]; simp

syntax (name := bvify_saturate) "bvify_saturate" colGe term : tactic

/-!
Some theorems which automatically lift comparisons between machine scalars, without needing the number of bits to be provided by the user.
-/

attribute [bvify] UScalar.eq_equiv_toBitVec_eq IScalar.eq_equiv_toBitVec_eq
                        gt_iff_lt ge_iff_le true_and and_true

@[bvify]
theorem UScalar.lt_equiv_toBitVec_lt {ty : UScalarTy} (x y : UScalar ty) : x < y ↔ x.toBitVec < y.toBitVec := by rfl

@[bvify]
theorem UScalar.le_equiv_toBitVec_le {ty : UScalarTy} (x y : UScalar ty) : x ≤ y ↔ x.toBitVec ≤ y.toBitVec := by rfl

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
      simpThms := #[← bvifyHypsSimpExt.getTheorems, ← SimpBoolProp.simpBoolPropHypsSimpExt.getTheorems]
      simprocs := #[← bvifyHypsSimprocExt.getSimprocs, ← SimpBoolProp.simpBoolPropHypsSimprocExt.getSimprocs]
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
example (x y : U8) (h : x.toNat < y.toNat) : x.toBitVec < y.toBitVec := by
  bvify 8 at h -- turns `h` into: `h : x.toBitVec < y.toBitVec`
  apply h
```

**Adding custom lemmas:**
One can give lemmas to `bvify` by annotating them with the attribute `@[bvify]`,
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

example (x y : U8) (h : x.toNat < y.toNat) : x.toBitVec < y.toBitVec := by
  bvify 8 at h
  apply h

example (x y : U8) (h : x.toNat < y.toNat) : x.toBitVec < y.toBitVec := by
  bvify 8 at *
  bv_decide

example (x : U8) (h : x.toNat < 32) : x.toBitVec < 32#8 := by
  bvify 8 at h
  apply h

example (x : U8) (h : x.toNat < 32) : x.toBitVec < 32#8 := by
  bvify 8 at *
  apply h

example (a : U32) (h : a.toNat = 3329) : a.toBitVec = 3329#32 := by
  bvify 32 at *
  apply h

/--
info: example
  (a : U32)
  (b : U32)
  (c : U32)
  (h0 : c.toBitVec ≤ 3329#32)
  (h1 : a.toBitVec + b.toBitVec ≤ 3329#32 + c.toBitVec) :
  a.toBitVec + b.toBitVec ≤ 3329#32 + c.toBitVec
  := by sorry
-/
#guard_msgs in
set_option linter.unusedTactic false in
example (a b c : U32) (h0 : c.toNat ≤ 3329) (h1 : a.toNat + b.toNat ≤ 3329 + c.toNat) : a.toBitVec + b.toBitVec ≤ 3329#32 + c.toBitVec := by
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
  (h : a.toBitVec + b.toBitVec < 32#32)
  (hc : c.toBitVec = a.toBitVec + b.toBitVec) :
  c.toBitVec % 32#32 = (a.toBitVec + b.toBitVec) % 32#32
  := by sorry
-/
#guard_msgs in
set_option linter.unusedTactic false in
example
  (a b c : U32) (h : a.toNat + b.toNat < 32) (hc : c.toNat = a.toNat + b.toNat) :
  (c.toNat : ZMod 32) = (a.toNat : ZMod 32) + (b.toNat : ZMod 32) := by
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
  (_ : c1.toBitVec = a.toBitVec + b.toBitVec)
  (c2 : U32)
  (hc2 : c2.toBitVec = c1.toBitVec - 3329#32)
  (c3 : U32)
  (hc3 : c3.toBitVec = c2.toBitVec >>> 16)
  (c4 : U32)
  (hc4 : (↑c4 : ℕ) = (↑(3329#u32 &&& c3) : ℕ))
  (_ : c4.toBitVec = 3329#32 &&& c3.toBitVec)
  (c5 : U32)
  (hc5 : c5.toBitVec = c2.toBitVec + c4.toBitVec) :
  (c5.toNat : ZMod 3329) = (a.toNat : ZMod 3329) + (b.toNat : ZMod 3329) ∧ c5.toNat < 3329
  := by
  bvify 32 at *
  simp_all only
  bv_decide

example
  (a : U32)
  (b : U32)
  (_ : a.toNat ≤ 6658)
  (ha : a.toNat < b.toNat + 3329)
  (hb : b.toNat ≤ 3329)
  (c1 : U32)
  (hc1 : c1.toBitVec = a.toBitVec - b.toBitVec)
  (c2 : U32)
  (hc2 : c2.toBitVec = c1.toBitVec >>> 16)
  (c3 : U32)
  (_ : c3.toBitVec = 3329#32 &&& c2.toBitVec)
  (c4 : U32)
  (hc3 : c4 = c1.toBitVec + c3.toBitVec) :
  (c4.toNat : ZMod 3329) = (a.toNat : ZMod 3329) - (b.toNat : ZMod 3329) ∧
  c4.toNat < 3329
  := by
  bvify 32 at *
  simp_all only
  bv_decide

example
  (x : U16) (_ : x.toNat < 3329)
  (y : U32) (_ : y = core.convert.num.FromU32U16.from x) :
  y.toNat = x.toNat
  := by
  bvify 32 at *
  bv_decide

example
  (x : U32) (_ : x.toNat < 3329)
  (y : U16) (_ : y = UScalar.cast UScalarTy.U16 x) :
  y.toNat = x.toNat
  := by
  bvify 16 at *
  bv_decide

example (x : U64) : x.toNat >>> 31 < 2^33 := by
  bvify 64
  bv_decide

/--
info: example
  (x : U32)
  (a : U32)
  (b : U32)
  (h : x.toBitVec = a.toBitVec + b.toBitVec) :
  x.toBitVec % 3329#32 = (a.toBitVec + b.toBitVec) % 3329#32
  := by sorry
-/
#guard_msgs in
set_option linter.unusedTactic false in
example (x a b : U32) (h : x.toNat = a.toNat + b.toNat) : (x.toNat : ZMod 3329) = (a.toNat : ZMod 3329) + (b.toNat : ZMod 3329) := by
  bvify 32 at *
  extract_goal1
  simp [h]

example (byte : U8) : 8 ∣ (byte &&& 16#u8).toNat := by
  bvify 8; bv_decide

end Aeneas.Bvify
