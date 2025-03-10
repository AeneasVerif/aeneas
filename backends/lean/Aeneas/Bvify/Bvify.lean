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
-/

namespace Aeneas.Bvify

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Arith Std

def guarded (p q : Prop) := p → q

@[bvify_simps] theorem guarded_true : guarded True q ↔ q := by simp [guarded]
@[bvify_simps] theorem guarded_same (p : Prop) : guarded p p ↔ True := by simp [guarded, *]

theorem BitVec.lt_pow_ofNat_le {n : Nat} (a b : Nat) (h0 : b < 2^n) (h1 : a ≤ b) :
  BitVec.ofNat n a ≤ BitVec.ofNat n b := by
  have : 0 < 2^n := by simp
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; omega
  have : b % 2^n = b := by apply Nat.mod_eq_of_lt; omega
  simp [*]

theorem BitVec.lt_pow_le_iff_ofNat_le {n : Nat} (a b : Nat) (h0 : a < 2^n) (h1 : b < 2^n) :
  a ≤ b ↔ BitVec.ofNat n a ≤ BitVec.ofNat n b := by
  constructor <;> intro h2
  . apply BitVec.lt_pow_ofNat_le <;> assumption
  . simp at h2
    have : a % 2^n = a := by apply Nat.mod_eq_of_lt; assumption
    have : b % 2^n = b := by apply Nat.mod_eq_of_lt; assumption
    omega

@[bvify_forward a ≤ b]
theorem BitVec.lt_pow_le_guarded_ofNat_le {n : Nat} (a b : Nat) :
  guarded (b < 2^n ∧ a ≤ b) (BitVec.ofNat n a ≤ BitVec.ofNat n b) := by
  simp only [guarded, and_imp]
  apply BitVec.lt_pow_ofNat_le

theorem BitVec.lt_pow_ofNat_lt {n : Nat} (a b : Nat) (h0 : b < 2^n) (h0 : a < b) :
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

-- We're not using this theorem but rather the one below
theorem BitVec.lt_pow_lt_guarded_ofNat_lt {n : Nat} (a b : Nat) :
  guarded (b < 2^n ∧ a < b) (BitVec.ofNat n a < BitVec.ofNat n b) := by
  simp only [guarded, and_imp]
  apply BitVec.lt_pow_ofNat_lt

theorem BitVec.lt_pow_lt_iff_ofNat_le {n : Nat} (a b : Nat) (h0 : a < b) (h1 : b - 1 < 2^n) :
  BitVec.ofNat n a ≤ BitVec.ofNat n (b - 1) := by
  simp
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; omega
  have : (b - 1) % 2^n = b - 1 := by apply Nat.mod_eq_of_lt; assumption
  omega

@[bvify_forward a < b]
theorem BitVec.lt_pow_lt_guarded_ofNat_le {n : Nat} (a b : Nat) :
  guarded (a < b ∧ b - 1 < 2^n) (BitVec.ofNat n a ≤ BitVec.ofNat n (b - 1)) := by
  simp only [guarded, and_imp]
  apply BitVec.lt_pow_lt_iff_ofNat_le

@[bvify_csimps]
theorem guarded_imp (p q : Prop) (h : p) : guarded p q ↔ q := by simp [guarded, *]

@[bvify_simps]
theorem Nat.mod_le_imp_mod_le (a b c : Nat) (h : b ≠ 0 ∧ (a < c ∨ b ≤ c)) : a % b < c := by
  obtain ⟨ h0, h1 ⟩ := h
  dcases h1
  . have := @Nat.mod_le a b
    omega
  . have := @Nat.mod_lt a b (by omega)
    omega

attribute [bvify_simps] ge_iff_le gt_iff_lt decide_eq_true_eq BitVec.ofNat_add or_self or_true

syntax (name := bvify_saturate) "bvify_saturate" term : tactic

/-!
Some theorems which automatically lift comparisons between machine scalars, without needing the bitwise to be provided by the user.
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

structure Config where
  /- The maximum number of forward saturation steps.

     Saturation visits the context to instantiate and introduce lemmas in the context.
     We then recursively explore those lemmas, etc.
   -/
  maxSaturateSteps : Nat := 3
  fastSaturate : Bool := true

declare_config_elab elabConfig Config

def bvifyTacSimp (loc : Utils.Location) (additionalAsms : List FVarId := []): TacticM Unit := do
  withMainContext do
  let simpTheorems ← bvifySimpExt.getTheorems
  let simprocs := [``Nat.reducePow, ``Nat.reduceLT, ``Nat.reduceLeDiff]
  Utils.simpAt true {maxDischargeDepth := 2, failIfUnchanged := false} simprocs [simpTheorems] [] [] additionalAsms loc

def propConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``Iff, ``And, ``Or
]

def arithComparisonConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge
]

def arithBinops : Std.HashSet Name := Std.HashSet.ofList [
  ``HMod.hMod, ``HDiv.hDiv, ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul
]

def exploreSubterms (f : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  if ¬ f.isConst then return #[]
  let constName := f.constName!
  if constName == ``Eq ∧ args.size == 3 then
    trace[Saturate] "Found `=`"
    pure #[args[1]!, args[2]!]
  else if constName ∈ propConsts ∧ args.size == 2 then
    trace[Saturate] "Found prop const: {f}"
    pure #[args[0]!, args[1]!]
  else if constName ∈ arithComparisonConsts ∧ args.size == 4 then
    trace[Saturate] "Found arith comparison: {f}"
    pure #[args[2]!, args[3]!]
  else if constName ∈ arithBinops ∧ args.size == 6 then
    trace[Saturate] "Found arith binop: {f}"
    pure #[args[4]!, args[5]!]
  else if constName == ``BitVec.ofNat ∧ args.size == 2 then
     pure #[args[1]!]
  else
    pure #[]

def bvifyTac (config : Config) (n : Expr) (loc : Utils.Location) : TacticM Unit := do
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
  /- First duplicate the propositions in the context: we will need the original ones (which mention
     integers rather than bit-vectors) for `scalar_tac` to succeed when doing the conditional rewritings. -/
  let (oldAsms, newAsms) ← Utils.duplicateAssumptions toDuplicate
  trace[Bvify] "Goal after duplicating the assumptions: {← getMainGoal}"
  /- Simplify the old assumptions - we keep the new ones for `scalar_tac` -/
  let loc ← do
    match loc with
    | .wildcard => pure (Utils.Location.targets oldAsms true)
    | .wildcard_dep => throwError "Unreachable"
    | .targets hyps type => pure (Utils.Location.targets hyps type)
  let addThm (thName : Name) : TacticM FVarId := do
    let thm ← mkAppM thName #[n]
    let thm ← Utils.addDeclTac (← Utils.mkFreshAnonPropUserName) thm (← inferType thm) (asLet := false)
    pure thm.fvarId!
  let lt_iff ← addThm ``Nat.lt_iff_BitVec_ofNat_lt
  let le_iff ← addThm ``Nat.le_iff_BitVec_ofNat_le
  let eq_iff ← addThm ``Nat.eq_iff_BitVec_ofNat_eq
  bvifyTacSimp loc [lt_iff, le_iff, eq_iff]
  if (← getUnsolvedGoals) == [] then return
  Utils.clearFVarIds #[lt_iff, le_iff, eq_iff]
  trace[Bvify] "Goal after simplifying: {← getMainGoal}"
  /- Small helper to retrieve the old assumptions: when we simplify some assumptions, a new fvar id is
     introduced for it. Whenever we apply a simplification to the old assumptions, the only way to retrieve
     their new ids is to go through the context and filter the ids which we know do not come from the duplicated
     assumptions -/
  let refreshFVarIds (ignore : Std.HashSet FVarId) : TacticM (Array FVarId) := do
    withMainContext do
    let decls := (← (← getLCtx).getDecls).toArray
    decls.filterMapM fun d => do if (← inferType d.type).isProp ∧ d.fvarId ∉ ignore then pure (some d.fvarId) else pure none
  /- Saturate the context, by looking only at the new assumptions - we have simplified the old ones.

     In the preprocessing step, we instantiate the value `n` in the theorem.
     We repeteadly explore the introduced assumptions.
  -/
  let preprocessThm (mvars : Array Expr) (_ : Expr) : MetaM Unit :=
    assert! (mvars.size > 0)
    mvars[0]!.mvarId!.assign n
  let newAsmsSet := Std.HashSet.ofArray newAsms
  let oldAsms ← refreshFVarIds newAsmsSet
  let oldAsmsSet := Std.HashSet.ofArray oldAsms
  trace[Bvify] "About to saturate the context"
  let rec saturate (steps : Nat) (oldAsmsSet : Std.HashSet FVarId) (tgts : Array FVarId) (exploreGoal : Bool) : TacticM Unit := do
    if steps = 0 then pure ()
    else
      /- Call saturate once -/
      trace[Bvify] "About to saturate by using the assumptions: {oldAsms.map Expr.fvar}"
      let satAsms ← Saturate.evalSaturate [`Aeneas.BvifyTac] exploreSubterms preprocessThm (some tgts) exploreGoal
      trace[Bvify] "Goal after saturation (added {satAsms.size} assumptions): {← getMainGoal}"
      /- Simplify the propositions introduced by by using `saturate` -/
      let (ref, d) ← tacticToDischarge (← `(tactic|scalar_tac))
      let dischargeWrapper := Lean.Elab.Tactic.Simp.DischargeWrapper.custom ref d
      let _ ← dischargeWrapper.with fun discharge? => do
        -- Initialize the simp context
        let simpThms ← bvifyCSimpExt.getTheorems
        let (ctx, simprocs) ← Utils.mkSimpCtx true {maxDischargeDepth := 2, failIfUnchanged := false} .simp
          [] [simpThms] [] [] []
        -- Apply the simplifier
        let _ ← Utils.customSimpLocation ctx simprocs discharge? (.targets satAsms false)
      trace[Bvify] "Goal after simplifying the saturated assumptions (with scalar_tac as a discharger): {← getMainGoal}"
      -- Compute the set of modifies assumptions
      let satAsms ← refreshFVarIds oldAsmsSet
      let oldAsms := oldAsmsSet.union (Std.HashSet.ofArray satAsms)
      saturate (steps - 1) oldAsms satAsms false
  let oldNewAsmsSet := oldAsmsSet.union newAsmsSet
  saturate config.maxSaturateSteps newAsmsSet oldAsms true
  trace[Bvify] "Saturation is done: {← getMainGoal}"
  /- Clear the duplicated assumptions -/
  Utils.clearFVarIds newAsms
  trace[Bvify] "Goal after clearing the duplicated assumptions: {← getMainGoal}"
  /- Simplify again the saturated assumptions, this time by using the `bvify_simps` simpset -/
  let satAsms ← refreshFVarIds oldNewAsmsSet
  bvifyTacSimp (.targets satAsms false) []
  if (← getUnsolvedGoals) == [] then return
  trace[Bvify] "Goal after simplifying the saturated assumptions: {← getMainGoal}"

elab "bvify'" config:Parser.Tactic.optConfig n:term : tactic => do
  let config ← elabConfig config
  let n ← Elab.Term.elabTerm n (Expr.const ``Nat [])
  bvifyTac config n Utils.Location.wildcard

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
  apply h

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
info: theorem Aeneas.Bvify.extracted_1 (a b c : U32) (h1 : ↑a + ↑b ≤ 3329 + ↑c) (h0 : c.bv ≤ 3329#32)
  (_ : a.bv + b.bv ≤ 3329#32 + c.bv) : a.bv + b.bv ≤ 3329#32 + c.bv := sorry
-/
#guard_msgs in
example (a b c : U32) (h0 : c.val ≤ 3329) (h1 : a.val + b.val ≤ 3329 + c.val) : a.bv + b.bv ≤ 3329#32 + c.bv := by
  bvify' 32
  extract_goal
  assumption

example (n a : Nat) (h : a < 2^n) : BitVec.ofNat n a ≤ BitVec.ofNat n (2^n - 1) := by
  bvify' n
  assumption

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

@[bvify_forward a % b]
theorem BitVec.ofNat_mod' (n : Nat) (a b : Nat) :
  guarded (a < 2^n ∧ b < 2^n) (BitVec.ofNat n (a % b) = BitVec.ofNat n a % BitVec.ofNat n b) := by
  simp only [guarded, and_imp]
  apply BitVec.ofNat_mod

theorem BitVec.iff_ofNat_eq (n : Nat) (a b : Nat) (ha : a < 2^n) (hb : b < 2^n) :
  a = b ↔ BitVec.ofNat n a = BitVec.ofNat n b := by
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; assumption
  have : b % 2^n = b := by apply Nat.mod_eq_of_lt; assumption
  simp only [BitVec.toNat_eq, BitVec.toNat_ofNat, *]

@[bvify_forward a = b]
theorem BitVec.guarded_ofNat_eq (n : Nat) (a b : Nat) :
  guarded (a < 2^n ∧ b < 2^n) (a = b ↔ BitVec.ofNat n a = BitVec.ofNat n b) := by
  simp only [guarded, and_imp]
  apply BitVec.iff_ofNat_eq

@[bvify_forward a - b]
theorem BitVec.ofNat_sub_guarded (n a b : Nat) :
  guarded (b ≤ a) (BitVec.ofNat n (a - b) = BitVec.ofNat n a - BitVec.ofNat n b) := by
  sorry

attribute [bvify_simps] ZMod.eq_iff_mod ZMod.val_add ZMod.val_sub ZMod.val_mul ZMod.val_sub' ZMod.val_natCast
attribute [bvify_simps] Nat.add_one_sub_one Nat.add_mod_mod Nat.mod_add_mod

example
  (a b c : U32) (h : a.val + b.val < 32) (hc : c.val = a.val + b.val) :
  (c.val : ZMod 32) = (a.val : ZMod 32) + (b.val : ZMod 32) := by
  bvify' 32
  have : c.val % 32 = (↑a + ↑b) % 32 ↔ BitVec.ofNat 32 (↑c % 32) = BitVec.ofNat 32 ((↑a + ↑b) % 32) := by assumption
  simp only [hc]

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
  (↑(↑c5 : ℕ) : ZMod 3329) = (↑(↑a : ℕ) : ZMod 3329) + (↑(↑b : ℕ) : ZMod 3329) ∧ (↑c5 : ℕ) < 3329
  := by
  bvify' 32
  simp_all only
  bv_decide

/-example
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
  (hc3 : c4 = c1.bv - c3.bv) :
  (c4.val : ZMod 3329) = (a.val : ZMod 3329) - (b.val : ZMod 3329)
  := by
  bvify' (maxSaturateSteps := 1) 32
  sorry

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
  (hc3 : c4 = c1.bv - c3.bv) :
  (c4.val : ZMod 3329) = (a.val : ZMod 3329) - (b.val : ZMod 3329)
  := by
  bvify' (maxSaturateSteps := 2) 32
  sorry-/

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
  (hc3 : c4 = c1.bv - c3.bv) :
  (c4.val : ZMod 3329) = (a.val : ZMod 3329) - (b.val : ZMod 3329)
  := by
  set_option trace.Bvify true in
  bvify' (maxSaturateSteps := 2) 32
  simp_all only
  extract_goal1
  simp_all only
  simp at *
  --bv_decide

example
  (a : U32)
  (b : U32)
  (ha : (↑a : ℕ) < (↑b : ℕ) + 3329)
  (c1 : U32)
  (hc1 : c1.bv = a.bv - b.bv)
  (c2 : U32)
  (c3 : U32)
  (c4 : U32)
  (hc2 : c2.bv = (a.bv - b.bv) >>> 16)
  (x : c3.bv = 3329#32 &&& (a.bv - b.bv) >>> 16)
  (hc3 : (↑(↑c4 : ℕ) : BitVec 32) = a.bv - b.bv - (3329#32 &&& (a.bv - b.bv) >>> 16))
  (_ : a.bv ≤ 6658#32)
  (hb : b.bv ≤ 3329#32)
  (__6 : (↑c4 : ℕ) % 3329 = ((↑a : ℕ) + (3329 - (↑b : ℕ) % 3329)) % 3329 ↔
  c4.bv % 3329#32 = (a.bv + (3329#32 - b.bv % 3329#32)) % 3329#32)
  (__5 : BitVec.ofNat 32 (3329 - (↑b : ℕ) % 3329) = 3329#32 - b.bv % 3329#32)
  (__4 : a.bv ≤ b.bv + 3329#32 - 1#32)
  (__3 : b.bv + 3328#32 = b.bv + 3329#32 - 1#32)
  (__2 : BitVec.ofNat 32 (((↑a : ℕ) + (3329 - (↑b : ℕ) % 3329)) % 3329) = (a.bv + (3329#32 - b.bv % 3329#32)) % 3329#32)
  (__1 : BitVec.ofNat 32 ((↑b : ℕ) % 3329) = b.bv % 3329#32)
  (_ : BitVec.ofNat 32 ((↑c4 : ℕ) % 3329) = c4.bv % 3329#32) :
  c4.bv % 3329#32 = (a.bv + (3329#32 - b.bv % 3329#32)) % 3329#32
  := by

  bv_decide


end Aeneas.Bvify
