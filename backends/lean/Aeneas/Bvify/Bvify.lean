import Mathlib.Tactic.Basic
import Mathlib.Tactic.Attr.Register
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Order.Basic
import Aeneas.Bvify.Init
import Aeneas.Arith.Lemmas
import Aeneas.Std.Scalar
import Aeneas.Std.PrimitivesLemmas

/-!
# `bvify` tactic

The `bvify` tactic is used to shift propositions about, e.g., `Nat`, to `BitVec`.
This tactic is adapted from `zify`.

TODO: we can probably drop the `bvify_csimps` attribute if we're being careful so that `scalar_tac` doesn't get called too many times.
-/

namespace Aeneas.Bvify

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Arith Std

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
  dcases h1
  . have := @Nat.mod_le a b
    omega
  . have := @Nat.mod_lt a b (by omega)
    omega

attribute [bvify_simps] ge_iff_le gt_iff_lt decide_eq_true_eq BitVec.ofNat_add or_self or_true
attribute [bvify_csimps] BitVec.ofNat_add

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

@[bvify_csimps]
theorem BitVec.ofNat_mod' (n a b : Nat) (h : a < 2^n ∧ b < 2^n) :
  BitVec.ofNat n (a % b) = BitVec.ofNat n a % BitVec.ofNat n b := by
  apply BitVec.ofNat_mod <;> simp [*]

@[bvify_csimps]
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
  simp only [Int.add_emod_self_left]
  rw [Int.sub_emod]
  conv => rhs; rw [Int.sub_emod]
  simp only [dvd_refl, Int.emod_emod_of_dvd]

@[simp, bvify_simps, bvify_csimps]
theorem UScalar.BitVec_ofNat_val (x : UScalar ty) : BitVec.ofNat ty.numBits x.val = x.bv := by
  cases x; simp only [UScalar.val, BitVec.ofNat_toNat, BitVec.setWidth_eq]

@[simp, bvify_simps, bvify_csimps] theorem U8.BitVec_ofNat_val (x : U8) : BitVec.ofNat 8 x.val = x.bv := UScalar.BitVec_ofNat_val x
@[simp, bvify_simps, bvify_csimps] theorem U16.BitVec_ofNat_val (x : U16) : BitVec.ofNat 16 x.val = x.bv := UScalar.BitVec_ofNat_val x
@[simp, bvify_simps, bvify_csimps] theorem U32.BitVec_ofNat_val (x : U32) : BitVec.ofNat 32 x.val = x.bv := UScalar.BitVec_ofNat_val x
@[simp, bvify_simps, bvify_csimps] theorem U64.BitVec_ofNat_val (x : U64) : BitVec.ofNat 64 x.val = x.bv := UScalar.BitVec_ofNat_val x
@[simp, bvify_simps, bvify_csimps] theorem U128.BitVec_ofNat_val (x : U128) : BitVec.ofNat 128 x.val = x.bv := UScalar.BitVec_ofNat_val x
@[simp, bvify_simps, bvify_csimps] theorem Usize.BitVec_ofNat_val (x : Usize) : BitVec.ofNat System.Platform.numBits x.val = x.bv := UScalar.BitVec_ofNat_val x

@[simp, bvify_simps, bvify_csimps]
theorem IScalar.BitVec_ofInt_val (x : IScalar ty) : BitVec.ofInt ty.numBits x.val = x.bv := by
  cases x; simp only [IScalar.val, BitVec.ofInt_toInt, BitVec.setWidth_eq]

@[simp, bvify_simps, bvify_csimps] theorem I8.BitVec_ofInt_val (x : I8) : BitVec.ofInt 8 x.val = x.bv := IScalar.BitVec_ofInt_val x
@[simp, bvify_simps, bvify_csimps] theorem I16.BitVec_ofInt_val (x : I16) : BitVec.ofInt 16 x.val = x.bv := IScalar.BitVec_ofInt_val x
@[simp, bvify_simps, bvify_csimps] theorem I32.BitVec_ofInt_val (x : I32) : BitVec.ofInt 32 x.val = x.bv := IScalar.BitVec_ofInt_val x
@[simp, bvify_simps, bvify_csimps] theorem I64.BitVec_ofInt_val (x : I64) : BitVec.ofInt 64 x.val = x.bv := IScalar.BitVec_ofInt_val x
@[simp, bvify_simps, bvify_csimps] theorem I128.BitVec_ofInt_val (x : I128) : BitVec.ofInt 128 x.val = x.bv := IScalar.BitVec_ofInt_val x
@[simp, bvify_simps, bvify_csimps] theorem Isize.BitVec_ofInt_val (x : Isize) : BitVec.ofInt System.Platform.numBits x.val = x.bv := IScalar.BitVec_ofInt_val x

@[simp, bvify_simps, bvify_csimps]
theorem UScalar.Nat_cast_BitVec_val (x : UScalar ty) : Nat.cast x.val = x.bv := by
  simp only [BitVec.natCast_eq_ofNat, UScalar.BitVec_ofNat_val_eq]

@[simp, bvify_simps, bvify_csimps] theorem U8.Nat_cast_BitVec_val (x : U8) : Nat.cast x.val = x.bv := UScalar.Nat_cast_BitVec_val x
@[simp, bvify_simps, bvify_csimps] theorem U16.Nat_cast_BitVec_val (x : U16) : Nat.cast x.val = x.bv := UScalar.Nat_cast_BitVec_val x
@[simp, bvify_simps, bvify_csimps] theorem U32.Nat_cast_BitVec_val (x : U32) : Nat.cast x.val = x.bv := UScalar.Nat_cast_BitVec_val x
@[simp, bvify_simps, bvify_csimps] theorem U64.Nat_cast_BitVec_val (x : U64) : Nat.cast x.val = x.bv := UScalar.Nat_cast_BitVec_val x
@[simp, bvify_simps, bvify_csimps] theorem U128.Nat_cast_BitVec_val (x : U128) : Nat.cast x.val = x.bv := UScalar.Nat_cast_BitVec_val x
@[simp, bvify_simps, bvify_csimps] theorem Usize.Nat_cast_BitVec_val (x : Usize) : Nat.cast x.val = x.bv := UScalar.Nat_cast_BitVec_val x

@[simp, bvify_simps, bvify_csimps]
theorem IScalar.Nat_cast_BitVec_val (x : IScalar ty) : Int.cast x.val = x.bv := by
  simp only [Int.cast, IntCast.intCast, BitVec_ofInt_val]

@[simp, bvify_simps, bvify_csimps] theorem I8.Nat_cast_BitVec_val (x : I8) : Int.cast x.val = x.bv := IScalar.Nat_cast_BitVec_val x
@[simp, bvify_simps, bvify_csimps] theorem I16.Nat_cast_BitVec_val (x : I16) : Int.cast x.val = x.bv := IScalar.Nat_cast_BitVec_val x
@[simp, bvify_simps, bvify_csimps] theorem I32.Nat_cast_BitVec_val (x : I32) : Int.cast x.val = x.bv := IScalar.Nat_cast_BitVec_val x
@[simp, bvify_simps, bvify_csimps] theorem I64.Nat_cast_BitVec_val (x : I64) : Int.cast x.val = x.bv := IScalar.Nat_cast_BitVec_val x
@[simp, bvify_simps, bvify_csimps] theorem I128.Nat_cast_BitVec_val (x : I128) : Int.cast x.val = x.bv := IScalar.Nat_cast_BitVec_val x
@[simp, bvify_simps, bvify_csimps] theorem Isize.Nat_cast_BitVec_val (x : Isize) : Int.cast x.val = x.bv := IScalar.Nat_cast_BitVec_val x

attribute [bvify_simps] ZMod.eq_iff_mod ZMod.val_add ZMod.val_sub ZMod.val_mul ZMod.val_sub' ZMod.val_natCast
attribute [bvify_simps] Nat.add_one_sub_one Nat.add_mod_mod Nat.mod_add_mod

syntax (name := bvify_saturate) "bvify_saturate" term : tactic

/-!
Some theorems which automatically lift comparisons between machine scalars, without needing the number of bits to be provided by the user.
-/

attribute [bvify_simps] UScalar.eq_equiv_bv_eq IScalar.eq_equiv_bv_eq
                        gt_iff_lt ge_iff_le true_and and_true

@[bvify_simps]
theorem UScalar.lt_equiv_bv_lt {ty : UScalarTy} (x y : UScalar ty) : x < y ↔ x.bv < y.bv := by rfl

@[bvify_simps]
theorem UScalar.le_equiv_bv_le {ty : UScalarTy} (x y : UScalar ty) : x ≤ y ↔ x.bv ≤ y.bv := by rfl

syntax (name := bvify) "bvify" num (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| bvify $n $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic|
    (simp -decide (maxDischargeDepth := 1) only [
       Int.reduceToNat, Nat.reducePow, Nat.reduceLT,
       Nat.lt_iff_BitVec_ofNat_lt $n, Nat.le_iff_BitVec_ofNat_le $n,
       bvify_simps, push_cast, $args,*] $[at $location]?))

def bvifyTacSimp (loc : Utils.Location) (additionalAsms : List FVarId := []): TacticM Unit := do
  withMainContext do
  let simpTheorems ← bvifySimpExt.getTheorems
  let simprocs := [``Nat.reducePow, ``Nat.reduceLT, ``Nat.reduceLeDiff]
  Utils.simpAt true {maxDischargeDepth := 2, failIfUnchanged := false} simprocs [simpTheorems] [] [] additionalAsms loc

def bvifyTacCSimp (loc : Utils.Location) (additionalAsms : List FVarId := []): TacticM Unit := do
  withMainContext do
  -- TODO: saturate before-hand, then scalar_tac (saturate := false)
  let (ref, d) ← tacticToDischarge (← `(tactic|scalar_tac))
    let dischargeWrapper := Lean.Elab.Tactic.Simp.DischargeWrapper.custom ref d
    let _ ← dischargeWrapper.with fun discharge? => do
      -- Initialize the simp context
      let simprocs := [``Nat.reducePow, ``Nat.reduceLT, ``Nat.reduceLeDiff] -- TODO: update the list of simprocs?
      let simpThms ← bvifyCSimpExt.getTheorems
      let (ctx, simprocs) ← Utils.mkSimpCtx true {maxDischargeDepth := 2, failIfUnchanged := false} .simp
        simprocs [simpThms] [] [] additionalAsms
      -- Apply the simplifier
      let _ ← Utils.customSimpLocation ctx simprocs discharge? loc

def bvifyTac (n : Expr) (loc : Utils.Location) : TacticM Unit := do
  Elab.Tactic.focus do
  withMainContext do
  trace[Bvify] "Initial goal: {← getMainGoal}"
  /- -/
  let toDuplicate ← do
    match loc with
    | .wildcard => pure none
    | .wildcard_dep => throwError "bvifyTac does not support using location `Utils.Location.wildcard_dep`"
    | .targets hyps type =>
      if type then throwError "bvifyTac does not support using location `Utils.Location.target` with `type = true`"
      pure (some hyps)
  /- Small helper.

     We use it to refresh the fvar ids after simplifying some assumptions.
     Whenever we apply a simplification to some assumptions, the only way to retrieve their new ids is
     to go through the context and filter the ids which we know do not come from the duplicated
     assumptions. -/
  let refreshFVarIds (keep ignore : Std.HashSet FVarId) : TacticM (Array FVarId) := do
    withMainContext do
    let decls := (← (← getLCtx).getDecls).toArray
    decls.filterMapM fun d => do
      if (← inferType d.type).isProp ∧ (d.fvarId ∈ keep ∨ d.fvarId ∉ ignore)
      then pure (some d.fvarId) else pure none
  let getOtherAsms (ignore : Std.HashSet FVarId) : TacticM (Array FVarId) :=
    refreshFVarIds Std.HashSet.empty ignore
  /- First duplicate the propositions in the context: we will need the original ones (which mention
     integers rather than bit-vectors) for `scalar_tac` to succeed when doing the conditional rewritings. -/
  let (oldAsms, newAsms) ← Utils.duplicateAssumptions toDuplicate
  let oldAsmsSet := Std.HashSet.ofArray oldAsms
  trace[Bvify] "Goal after duplicating the assumptions: {← getMainGoal}"
  /- Introduce additional simp assumptions -/
  let addThm (thName : Name) : TacticM FVarId := do
    let thm ← mkAppM thName #[n]
    let thm ← Utils.addDeclTac (← Utils.mkFreshAnonPropUserName) thm (← inferType thm) (asLet := false)
    pure thm.fvarId!
  withMainContext do
  let le_iff ← addThm ``BitVec.lt_pow_le_iff_ofNat_le'
  let lt_iff ← addThm ``BitVec.lt_pow_lt_iff_ofNat_lt'
  let lt_max_iff ← addThm ``BitVec.lt_pow_n_iff_ofNat_le
  --let lt_iff_csimp ← addThm ``BitVec.lt_pow_lt_iff_ofNat_le
  let eq_iff ← addThm ``BitVec.iff_ofNat_eq'
  trace[Bvify] "Goal after adding the additional simp assumptions: {← getMainGoal}"
  let additionalThms := [le_iff, lt_iff, lt_max_iff, eq_iff]
  let additionalSimpThms := [le_iff, lt_iff, lt_max_iff, eq_iff]
  let additionalCSimpThms := [le_iff, lt_max_iff, lt_iff, eq_iff]
  /- Simplify the targets (note that we preserve the new assumptions for `scalar_tac`) -/
  let (loc, notLocAsms) ← do
    match loc with
    | .wildcard => pure (Utils.Location.targets oldAsms true, ← getOtherAsms oldAsmsSet)
    | .wildcard_dep => throwError "Unreachable"
    | .targets hyps type => pure (Utils.Location.targets hyps type, ← getOtherAsms (Std.HashSet.ofArray hyps))
  bvifyTacSimp loc additionalSimpThms
  if (← getUnsolvedGoals) == [] then return
  trace[Bvify] "Goal after simplifying: {← getMainGoal}"
  /- Simplify the targets by using `scalar_tac` as a discharger -/
  let notLocAsmsSet := Std.HashSet.ofArray notLocAsms
  let nloc ← do
    match loc with
    | .wildcard => pure (Utils.Location.targets (← refreshFVarIds oldAsmsSet notLocAsmsSet) true) --, ← refreshFVarIds oldAsmsSet notLocAsmsSet)
    | .wildcard_dep => throwError "Unreachable"
    | .targets hyps type => pure (Utils.Location.targets (← refreshFVarIds (Std.HashSet.ofArray hyps) notLocAsmsSet) type) --, ← refreshFVarIds oldAsmsSet notLocAsmsSet)
  bvifyTacCSimp nloc additionalCSimpThms
  /- Clear the additional assumptions -/
  Utils.clearFVarIds newAsms
  trace[Bvify] "Goal after clearing the duplicated assumptions: {← getMainGoal}"
  Utils.clearFVarIds additionalThms.toArray
  trace[Bvify] "Goal after clearing the additional theorems: {← getMainGoal}"

elab "bvify'" n:term : tactic => do
  let n ← Elab.Term.elabTerm n (Expr.const ``Nat [])
  bvifyTac n Utils.Location.wildcard

/-- The `Simp.Context` generated by `bvify`. -/
def mkBvifyContext (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ",")) :
    TacticM MkSimpContextResult := do
  let args := simpArgs.map (·.getElems) |>.getD #[]
  mkSimpContext
    (← `(tactic| simp -decide (maxDischargeDepth := 1) only [bvify_simps, push_cast, $args,*])) false

/-- A variant of `applySimpResultToProp` that cannot close the goal, but does not need a meta
variable and returns a tuple of a proof and the corresponding simplified proposition. -/
def applySimpResultToProp' (proof : Expr) (prop : Expr) (r : Simp.Result) : MetaM (Expr × Expr) :=
  do
  match r.proof? with
  | some eqProof => return (← mkExpectedTypeHint (← mkEqMP eqProof proof) r.expr, r.expr)
  | none =>
    if r.expr != prop then
      return (← mkExpectedTypeHint proof r.expr, r.expr)
    else
      return (proof, r.expr)

/-- Translate a proof and the proposition into a natified form. -/
def bvifyProof (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ","))
    (proof : Expr) (prop : Expr) : TacticM (Expr × Expr) := do
  let ctx_result ← mkBvifyContext simpArgs
  let (r, _) ← simp prop ctx_result.ctx
  applySimpResultToProp' proof prop r

example (x y : U8) (h : x.val < y.val) : x.bv < y.bv := by
  bvify 8 at h
  apply h

example (x y : U8) (h : x.val < y.val) : x.bv < y.bv := by
  bvify' 8
  bv_decide

example (x : U8) (h : x.val < 32) : x.bv < 32#8 := by
  bvify 8 at h
  apply h

example (x : U8) (h : x.val < 32) : x.bv < 32#8 := by
  bvify' 8
  apply h

example (a : U32) (h : a.val = 3329) : a.bv = 3329#32 := by
  bvify' 32
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
  bvify' 32
  extract_goal1
  assumption

example (n a : Nat) (h : a < 2^n) : BitVec.ofNat n a ≤ BitVec.ofNat n (2^n - 1) := by
  bvify' n
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
  bvify' 32
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
  bvify' 32
  simp_all only
  bv_decide

set_option profiler true in
set_option profiler.threshold 10 in
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
  bvify' 32
  simp_all only
  bv_decide

end Aeneas.Bvify
