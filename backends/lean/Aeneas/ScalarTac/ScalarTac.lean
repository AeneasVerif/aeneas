import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Ring.RingNF
import Aeneas.Utils
import Aeneas.ScalarTac.Core
import Aeneas.ScalarTac.Init
import Aeneas.Saturate

namespace Aeneas

theorem Nat.le_mul_le (a0 a1 b0 b1 : Nat) (h0 : a0 ≤ a1) (h2 : b0 ≤ b1) : a0 * b0 ≤ a1 * b1 := by
  have := @Nat.mul_le_mul_left b0 b1 a0 (by assumption)
  have := @Nat.mul_le_mul_right a0 a1 b1 (by assumption)
  omega

theorem Nat.lt_mul_lt (a0 a1 b0 b1 : Nat) (h0 : a0 < a1) (h2 : b0 < b1) : a0 * b0 < a1 * b1 := by
  apply Nat.mul_lt_mul_of_lt_of_lt <;> assumption

theorem Nat.le_mul_lt (a0 a1 b0 b1 : Nat) (h0 : a0 ≤ a1) (h1 : 0 < a1) (h2 : b0 < b1) : a0 * b0 < a1 * b1 := by
  have := @Nat.mul_le_mul_right a0 a1 b0 (by assumption)
  have := @Nat.mul_lt_mul_left a1 b0 b1 (by assumption)
  omega

theorem Nat.lt_mul_le (a0 a1 b0 b1 : Nat) (h0 : a0 < a1) (h1 : b0 ≤ b1) (h2 : 0 < b1) : a0 * b0 < a1 * b1 := by
  have := @Nat.mul_lt_mul_right b1 a0 a1 (by assumption)
  have := @Nat.mul_le_mul_left b0 b1 a0 (by assumption)
  omega

theorem Nat.zero_lt_mul (a0 a1 : Nat) (h0 : 0 < a0) (h1 : 0 < a1) : 0 < a0 * a1 := by simp [*]
theorem Nat.mul_le_zero (a0 a1 : Nat) (h0 : a0 = 0) (h1 : a1 = 0) : a0 * a1 ≤ 0 := by simp [*]

namespace ScalarTac

open Utils
open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

/-
-- DEPRECATED: `scalar_tac` used to rely on `aesop`. As there are performance issues
-- with the saturation tactic for now we use our own tactic. We will revert once the performance
-- is improved.

/- Defining a custom attribute for Aesop - we use the Aesop tactic in the arithmetic tactics -/
attribute [aesop (rule_sets := [Aeneas.ScalarTac]) unfold norm] Function.comp

/-- The `scalar_tac` attribute used to tag forward theorems for the `scalar_tac` tactic. -/
macro "scalar_tac" pat:term : attr =>
  `(attr|aesop safe forward (rule_sets := [$(Lean.mkIdent `Aeneas.ScalarTac):ident]) (pattern := $pat))

/-- The `nonlin_scalar_tac` attribute used to tag forward theorems for the `scalar_tac` tactics. -/
macro "nonlin_scalar_tac" pat:term : attr =>
  `(attr|aesop safe forward (rule_sets := [$(Lean.mkIdent `Aeneas.ScalarTacNonLin):ident]) (pattern := $pat))
-/

/-- The `scalar_tac` attribute used to tag forward theorems for the `scalar_tac` tactics. -/
macro "scalar_tac" pat:term : attr =>
  `(attr|aeneas_saturate (set := $(Lean.mkIdent `Aeneas.ScalarTac)) (pattern := $pat))

/-- The `nonlin_scalar_tac` attribute used to tag forward theorems for the `scalar_tac` tactics. -/
macro "nonlin_scalar_tac" pat:term : attr =>
  `(attr|aeneas_saturate (set := $(Lean.mkIdent `Aeneas.ScalarTacNonLin)) (pattern := $pat))

-- This is useful especially in the termination proofs
attribute [scalar_tac a.toNat] Int.toNat_eq_max

/- Check if a proposition is a linear integer proposition.
   We notably use this to check the goals: this is useful to filter goals that
   are unlikely to be solvable with arithmetic tactics. -/
class IsLinearIntProp (x : Prop) where

instance (x y : Int) : IsLinearIntProp (x < y) where
instance (x y : Int) : IsLinearIntProp (x > y) where
instance (x y : Int) : IsLinearIntProp (x ≤ y) where
instance (x y : Int) : IsLinearIntProp (x ≥ y) where
instance (x y : Int) : IsLinearIntProp (x ≥ y) where
instance (x y : Int) : IsLinearIntProp (x = y) where

instance (x y : Nat) : IsLinearIntProp (x < y) where
instance (x y : Nat) : IsLinearIntProp (x > y) where
instance (x y : Nat) : IsLinearIntProp (x ≤ y) where
instance (x y : Nat) : IsLinearIntProp (x ≥ y) where
instance (x y : Nat) : IsLinearIntProp (x ≥ y) where
instance (x y : Nat) : IsLinearIntProp (x = y) where

instance : IsLinearIntProp False where
instance (p : Prop) [IsLinearIntProp p] : IsLinearIntProp (¬ p) where
instance (p q : Prop) [IsLinearIntProp p] [IsLinearIntProp q] : IsLinearIntProp (p ∨ q) where
instance (p q : Prop) [IsLinearIntProp p] [IsLinearIntProp q] : IsLinearIntProp (p ∧ q) where
-- We use the one below for goals
instance (p q : Prop) [IsLinearIntProp p] [IsLinearIntProp q] : IsLinearIntProp (p → q) where

-- Check if the goal is a linear arithmetic goal
def goalIsLinearInt : Tactic.TacticM Bool := do
  Tactic.withMainContext do
  let gty ← Tactic.getMainTarget
  match ← trySynthInstance (← mkAppM ``IsLinearIntProp #[gty]) with
  | .some _ => pure true
  | _ => pure false

example (x y : Int) (h0 : x ≤ y) (h1 : x ≠ y) : x < y := by
  omega

attribute [scalar_tac_simps]
  reduceIte
  Nat.reduceLeDiff Nat.reduceLT Nat.reduceGT Nat.reduceBEq Nat.reduceBNe
  Nat.reducePow Nat.reduceAdd Nat.reduceSub Nat.reduceMul Nat.reduceDiv Nat.reduceMod
  Int.reduceLT Int.reduceLE Int.reduceGT Int.reduceGE Int.reduceEq Int.reduceNe Int.reduceBEq Int.reduceBNe
  Int.reducePow Int.reduceAdd Int.reduceSub Int.reduceMul Int.reduceDiv Int.reduceMod
  Int.reduceNegSucc Int.reduceNeg Int.reduceToNat
  not_lt not_le

/- Small trick to prevent `simp_all` from simplifying an assumption `h1 : P v` when we have
  `h0 : ∀ x, P x` in the context: we replace the forall quantifiers with our own definition
  of `forall`. -/
def forall' {α : Type u} (p : α → Prop) : Prop := ∀ (x: α), p x

theorem forall_eq_forall' {α : Type u} (p : α → Prop) : (∀ (x: α), p x) = forall' p := by
  simp [forall']

@[app_unexpander forall']
def unexpForall' : Lean.PrettyPrinter.Unexpander | `($_ $_) => `(∀ _, __) | _ => throw ()

structure Config where
  /- Should we use non-linear arithmetic reasoning? -/
  nonLin : Bool := false
  /- If `true`, split all the matches/if then else in the context (note that `omega`
     splits the *disjunctions*) -/
  split: Bool := false
  /- Maximum number of steps to take with `simpAll` during the preprocessing phase.
     If equal to 0, we do not call `simpAll` at all.
   -/
  simpAllMaxSteps : Nat := 100000
  /- Should we saturate the context with theorems marked with the attribute `scalar_tac`? -/
  saturate : Bool := true
  fastSaturate : Bool := false

declare_config_elab elabConfig Config

/-- Apply the scalar_tac forward rules -/
def scalarTacSaturateForward (fast : Bool) (nonLin : Bool): Tactic.TacticM (Array FVarId) := do
  /-
  let options : Aesop.Options := {}
  -- Use a forward max depth of 0 to prevent recursively applying forward rules on the assumptions
  -- introduced by the forward rules themselves.
  let options ← options.toOptions' (some 0)-/
  -- We always use the rule set `Aeneas.ScalarTac`, but also need to add other rule sets locally
  -- activated by the user. The `Aeneas.ScalarTacNonLin` rule set has a special treatment as
  -- it is activated through an option.
  let ruleSets :=
    let ruleSets := `Aeneas.ScalarTac :: (← scalarTacRuleSets.get)
    if nonLin then `Aeneas.ScalarTacNonLin :: ruleSets
    else ruleSets
  -- TODO
  -- evalAesopSaturate options ruleSets.toArray
  Saturate.evalSaturate ruleSets (if fast then Saturate.exploreArithSubterms else none) none

-- For debugging
elab "scalar_tac_saturate" config:Parser.Tactic.optConfig : tactic => do
  let config ← elabConfig config
  let _ ← scalarTacSaturateForward config.fastSaturate config.nonLin

/- Propositional logic simp lemmas -/
attribute [scalar_tac_simps]
  and_self false_implies true_implies Prod.mk.injEq
  not_false_eq_true not_true_eq_false
  true_and and_true false_and and_false
  true_or or_true false_or or_false
  Bool.true_eq_false Bool.false_eq_true
  decide_eq_true_eq decide_eq_false_iff_not Bool.or_eq_true Bool.and_eq_true

/-  Boosting a bit the `omega` tac.

    - `extraPrePreprocess`: extra-preprocessing to be done *before* this preprocessing
    - `extraPreprocess`: extra-preprocessing to be done *after* this preprocessing
 -/
def scalarTacPreprocess (config : Config) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  -- Pre-preprocessing
  /- First get rid of [ofInt] (if there are dependent arguments, we may not
     manage to simplify the context). We only use a small set of lemmas
     because otherwise we may simplify too much, leading to issues when
     saturating. -/
  trace[ScalarTac] "Original goal before preprocessing: {← getMainGoal}"
  let beforeSatSimpArgs : SimpArgs ← do
    let simprocs ← scalarTacBeforeSatSimprocExt.getSimprocs
    let simpLemmas ← scalarTacBeforeSatSimpExt.getTheorems
    pure {simprocs := #[simprocs], simpThms := #[simpLemmas]}
  tryTac do
    Utils.simpAt true {dsimp := false, failIfUnchanged := false, maxDischargeDepth := 0}
              beforeSatSimpArgs .wildcard
  trace[ScalarTac] "Goal after first simplification: {← getMainGoal}"
  -- Apply the forward rules
  if config.saturate then
    allGoalsNoRecover (do let _ ← scalarTacSaturateForward config.fastSaturate config.nonLin)
  trace[ScalarTac] "Goal after saturation: {← getMainGoal}"
  let simprocs ← scalarTacSimprocExt.getSimprocs
  let simpLemmas ← scalarTacSimpExt.getTheorems
  let simpArgs : SimpArgs := {simprocs := #[simprocs], simpThms := #[simpLemmas]}
  -- Apply `simpAll`
  if config.simpAllMaxSteps ≠ 0 then
    allGoalsNoRecover
      (tryTac do
        Utils.simpAll
          {failIfUnchanged := false, maxSteps := config.simpAllMaxSteps, maxDischargeDepth := 0} true
          simpArgs)
  trace[ScalarTac] "Goal after simpAll: {← getMainGoal}"
  -- Reduce all the terms in the goal - note that the extra preprocessing step
  -- might have proven the goal, hence the `allGoals`
  let dsimp :=
    allGoalsNoRecover do
      tryTac do
      -- We set `simpOnly` at false on purpose.
      -- Also, we need `zetaDelta` to inline the let-bindings (otherwise, omega doesn't always manages
      -- to deal with them)
      dsimpAt false {zetaDelta := true, failIfUnchanged := false, maxDischargeDepth := 0} {simprocs := #[simprocs]}
        Tactic.Location.wildcard
  dsimp
  trace[ScalarTac] "Goal after first dsimp: {← getMainGoal}"
  -- More preprocessing: apply norm_cast to the whole context
  allGoalsNoRecover (Utils.tryTac (Utils.normCastAtAll))
  trace[ScalarTac] "Goal after first normCast: {← getMainGoal}"
  -- norm_cast does weird things with negative numbers so we reapply simp
  dsimp
  trace[ScalarTac] "Goal after 2nd dsimp: {← getMainGoal}"
  allGoalsNoRecover do
    tryTac do
    Utils.simpAt true {failIfUnchanged := false, maxDischargeDepth := 1}
      {simpThms := #[simpLemmas],
       addSimpThms :=
        #[-- Int.subNatNat is very annoying - TODO: there is probably something more general thing to do
          ``Int.subNatNat_eq_coe,
          -- We also need this, in case the goal is: ¬ False
          ``not_false_eq_true,
          -- Remove the forall quantifiers to prepare for the call of `simp_all` (we
          -- don't want `simp_all` to use assumptions of the shape `∀ x, P x`))
          ``forall_eq_forall']}
        .wildcard
  trace[ScalarTac] "Goal after simpAt following dsimp: {← getMainGoal}"

elab "scalar_tac_preprocess" config:Parser.Tactic.optConfig : tactic => do
  let config ← elabConfig config
  scalarTacPreprocess config

def scalarTacCore (config : Config) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  Tactic.focus do
  let simprocs ← scalarTacSimprocExt.getSimprocs
  let simpLemmas ← scalarTacSimpExt.getTheorems
  let simpArgs : SimpArgs := {simprocs := #[simprocs], simpThms := #[simpLemmas]}
  let g ← Tactic.getMainGoal
  trace[ScalarTac] "Original goal: {g}"
  -- Introduce all the universally quantified variables (includes the assumptions)
  let (_, g) ← g.intros
  Tactic.setGoals [g]
  -- Preprocess - wondering if we should do this before or after splitting
  -- the goal. I think before leads to a smaller proof term?
  allGoalsNoRecover (scalarTacPreprocess config)
  allGoalsNoRecover do
    if config.split then do
      trace[ScalarTac] "Splitting the goal"
      /- If we split the `if then else` call `simp_all` again -/
      splitAll do
        allGoalsNoRecover
          (tryTac do
            Utils.simpAll {failIfUnchanged := false, maxSteps := config.simpAllMaxSteps, maxDischargeDepth := 0}
              true simpArgs)
        trace[ScalarTac] "Calling omega"
        allGoalsNoRecover (Tactic.Omega.omegaTactic {})
    else
      trace[ScalarTac] "Calling omega"
      Tactic.Omega.omegaTactic {}

/-- Tactic to solve arithmetic goals.

    The `scalar_tac` tactic is designed to solve linear arithmetic problems (it calls `omega` under the hood),
    but it can also solve a range of non-linear arithmetic problems when using the option `nonLin` (`scalar_tac +nonLin`).
    In particular, if given a goal of the shape:
    `a * b ≤ c * d`

    where `a`, `b`, `c`, `d` are natural numbers, it will attempt to prove:
    `a ≤ c ∧ b ≤ d`

    This works also with strict inequalities.
-/
def scalarTac (config : Config) : TacticM Unit := do
  Tactic.withMainContext do
  let error : TacticM Unit := do
    let g ← Tactic.getMainGoal
    throwError "scalar_tac failed to prove the goal below.\n\nNote that scalar_tac is almost equivalent to:\n  scalar_tac_preprocess; simp_all (maxDischargeDepth := 1) only; omega\n\nGoal: \n{g}"
  try
    scalarTacCore config
  catch _ =>
    trace[ScalarTac] "The first call to `scalarTacCore` failed"
    /- If the option `nonLin` is activated, attempt to decompose the goal -/
    if config.nonLin then
      trace[ScalarTac] "The `nonLin` option is `true`: attempting to decompose the goal"
      -- Retry
      try
        let g ← getMainGoal
        let trySolve (x : Name) : TacticM Unit := do
          let goals ← g.apply (.const x [])
          setGoals goals
          allGoals (scalarTacCore config)
        let tacs := List.map trySolve [``Nat.le_mul_le, ``Nat.lt_mul_lt, ``Nat.le_mul_lt, ``Nat.lt_mul_le]
        firstTac tacs
      catch _ => error
    else
      error

elab "scalar_tac" config:Parser.Tactic.optConfig : tactic => do
  let config ← elabConfig config
  scalarTac config

-- For termination proofs
syntax "int_decr_tac" : tactic
macro_rules
  | `(tactic| int_decr_tac) =>
    `(tactic|
      simp_wf;
      -- TODO: don't use a macro (namespace problems)
      (first | apply ScalarTac.to_int_to_nat_lt
             | apply ScalarTac.to_int_sub_to_nat_lt) <;>
      simp_all <;> scalar_tac)

-- Checking that things happen correctly when there are several conjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y := by
  scalar_tac

-- Checking that things happen correctly when there are several conjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y ∧ x + y ≥ 2 := by
  scalar_tac

-- Checking that we can prove exfalso
example (a : Prop) (x : Int) (h0: 0 < x) (h1: x < 0) : a := by
  scalar_tac

-- Intermediate cast through natural numbers
example (a : Prop) (x : Int) (h0: (0 : Nat) < x) (h1: x < 0) : a := by
  scalar_tac

example (x : Int) (h : x ≤ -3) : x ≤ -2 := by
  scalar_tac

example (x y : Int) (h : x + y = 3) :
  let z := x + y
  z = 3 := by
  intro z
  omega

example (P : Nat → Prop) (z : Nat) (h : ∀ x, P x → x ≤ z) (y : Nat) (hy : P y) :
  y + 2 ≤ z + 2 := by
  have := h y hy
  scalar_tac

-- Checking that we manage to split the cases/if then else
example (x : Int) (b : Bool) (h : if b then x ≤ 0 else x ≤ 0) : x ≤ 0 := by
  scalar_tac +split

/-!
Checking some non-linear problems
-/

example (x y : Nat) (h0 : x ≤ 4) (h1 : y ≤ 5): x * y ≤ 4 * 5 := by
  scalar_tac +nonLin

example (x y : Nat) (h0 : x ≤ 4) (h1 : y < 5): x * y < 4 * 5 := by
  scalar_tac +nonLin

example (x y : Nat) (h0 : x < 4) (h1 : y < 5): x * y < 4 * 5 := by
  scalar_tac +nonLin

example (x y : Nat) (h0 : x < 4) (h1 : y ≤ 5): x * y < 4 * 5 := by
  scalar_tac +nonLin

end ScalarTac

end Aeneas
