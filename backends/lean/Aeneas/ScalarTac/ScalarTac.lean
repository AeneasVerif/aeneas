import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Ring.RingNF
import Aeneas.Utils
import Aeneas.ScalarTac.Core
import Aeneas.ScalarTac.Init
import Aeneas.Saturate
import Aeneas.SimpScalar.Init
import Aeneas.SimpBoolProp.SimpBoolProp

namespace Aeneas

@[simp_scalar_simps]
theorem Nat.le_mul_le (a0 a1 b0 b1 : Nat) (h : a0 ≤ a1 ∧ b0 ≤ b1) : a0 * b0 ≤ a1 * b1 := by
  have := @Nat.mul_le_mul_left b0 b1 a0 h.right
  have := @Nat.mul_le_mul_right a0 a1 b1 h.left
  omega

@[simp_scalar_simps]
theorem Nat.lt_mul_lt (a0 a1 b0 b1 : Nat) (h : a0 < a1 ∧ b0 < b1) : a0 * b0 < a1 * b1 := by
  apply Nat.mul_lt_mul_of_lt_of_lt <;> tauto

@[simp_scalar_simps]
theorem Nat.le_mul_lt (a0 a1 b0 b1 : Nat) (h0 : a0 ≤ a1 ∧ 0 < a1 ∧b0 < b1) : a0 * b0 < a1 * b1 := by
  have := @Nat.mul_le_mul_right a0 a1 b0 (by tauto)
  have := @Nat.mul_lt_mul_left a1 b0 b1 (by tauto)
  omega

@[simp_scalar_simps]
theorem Nat.lt_mul_le (a0 a1 b0 b1 : Nat) (h0 : a0 < a1 ∧ b0 ≤ b1 ∧ 0 < b1) : a0 * b0 < a1 * b1 := by
  have := @Nat.mul_lt_mul_right b1 a0 a1 (by tauto)
  have := @Nat.mul_le_mul_left b0 b1 a0 (by tauto)
  omega

@[simp_scalar_simps]
theorem Nat.zero_lt_mul (a0 a1 : Nat) (h : 0 < a0 ∧ 0 < a1) : 0 < a0 * a1 := by simp [*]
theorem Nat.mul_le_zero (a0 a1 : Nat) (h : a0 = 0 ∨ a1 = 0) : a0 * a1 ≤ 0 := by simp [*]

@[simp_scalar_simps]
theorem Int.emod_eq_of_lt' {a b : ℤ} (h : 0 ≤ a ∧ a < b) : a % b = a := by
  apply Int.emod_eq_of_lt <;> omega

@[simp_scalar_simps]
theorem Nat.le_pow (a i : ℕ) (h : 0 < a ∧ 0 < i) : a ≤ a ^ i := by
  have : a ^ 1 ≤ a ^ i := by apply Nat.pow_le_pow_right <;> omega
  simp_all

@[simp_scalar_simps]
theorem Nat.lt_pow (a i : ℕ) (h : 1 < a ∧ 1 < i) : a < a ^ i := by
  have : a ^ 1 < a ^ i := by apply Nat.pow_lt_pow_right <;> omega
  simp_all

namespace ScalarTac

open Utils
open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

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
  lt_inf_iff le_inf_iff
  Fin.is_le'

/- Small trick to prevent `simp_all` from simplifying an assumption `h1 : P v` when we have
  `h0 : ∀ x, P x` in the context: we replace the forall quantifiers with our own definition
  of `forall`. -/
def forall' {α : Type u} (p : α → Prop) : Prop := ∀ (x: α), p x

theorem forall_eq_forall' {α : Type u} (p : α → Prop) : (∀ (x: α), p x) = forall' p := by
  simp [forall']

@[app_unexpander forall']
def unexpForall' : Lean.PrettyPrinter.Unexpander | `($_ $_) => `(∀ _, __) | _ => throw ()

structure SaturateConfig where
  /- Should we use non-linear arithmetic reasoning? -/
  nonLin : Bool := false
  /- Should we explore the assumptions when saturating?. -/
  saturateAssumptions : Bool := true
  /- Should we explore the target when saturating?. -/
  saturateTarget : Bool := true
  /- Should we dive into binders? -/
  saturateVisitBoundExpressions := false

structure Config extends SaturateConfig where
  /- If `true`, split all the matches/if then else in the context (note that `omega`
     splits the *disjunctions*) -/
  split: Bool := false
  /- Maximum number of steps to take with `simpAll` during the preprocessing phase.
     If equal to 0, we do not call `simpAll` at all.
   -/
  simpAllMaxSteps : Nat := 100000
  /- Should we saturate the context with theorems marked with the attribute `scalar_tac`? -/
  saturate : Bool := true
  satConfig : SaturateConfig := {}

declare_config_elab elabConfig Config

/-- Apply the scalar_tac forward rules -/
def scalarTacSaturateForward {α} (config : SaturateConfig) (f : Array FVarId → TacticM α)  : TacticM α := do
  /-
  let options : Aesop.Options := {}
  -- Use a forward max depth of 0 to prevent recursively applying forward rules on the assumptions
  -- introduced by the forward rules themselves.
  let options ← options.toOptions' (some 0)-/
  -- We always use the rule set `Aeneas.ScalarTac`, but also need to add other rule sets locally
  -- activated by the user. The `Aeneas.ScalarTacNonLin` rule set has a special treatment as
  -- it is activated through an option.
  let rules :=
    if config.nonLin then #[scalarTacAttribute, scalarTacNonLinAttribute]
    else #[scalarTacAttribute]
  Saturate.evalSaturate
    { visitProofTerms := false, visitBoundExpressions := config.saturateVisitBoundExpressions }
    rules none none
    (declsToExplore := none)
    (exploreAssumptions := config.saturateAssumptions)
    (exploreTarget := config.saturateTarget) f


-- For debugging
elab "scalar_tac_saturate" config:Parser.Tactic.optConfig : tactic => do
  let config ← elabConfig config
  let _ ← scalarTacSaturateForward config.toSaturateConfig (fun _ => pure ())

def getSimpArgs : CoreM SimpArgs := do
  pure {
    simprocs := #[
        ← SimpBoolProp.simpBoolPropSimprocExt.getSimprocs,
        ← scalarTacSimprocExt.getSimprocs
    ],
    simpThms := #[
      ← SimpBoolProp.simpBoolPropSimpExt.getTheorems,
      ← scalarTacSimpExt.getTheorems
    ]}

def getSimpThmNames : CoreM (Array Name) := do
  let args ← getSimpArgs
  let names := args.simpThms.map fun x =>
    (x.lemmaNames.toList.filterMap fun x =>
      match x with
      | .decl declName _ _ => some declName
      | _ => none).toArray
  pure names.flatten

/- Sometimes `simp at *` doesn't work in the presence of dependent types. However, simplifying
   the assumptions *does* work, hence this peculiar way of simplifying the context. -/
def simpAsmsTarget (simpOnly : Bool) (config : Simp.Config) (args : SimpArgs) : TacticM Unit :=
  withMainContext do
  let lctx ← getLCtx
  let decls ← lctx.getDecls
  let props ← decls.filterM (fun d => do pure (← inferType d.type).isProp)
  let props := (props.map fun d => d.fvarId).toArray
  Aeneas.Utils.simpAt simpOnly config args (.targets props true)

/-  Boosting a bit the `omega` tac. -/
def scalarTacPreprocess (config : Config) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  -- Pre-preprocessing
  /- We simplify a first time before saturating the context.
     This is useful because simplifying often introduces expressions which are useful
     for the saturation phase, and it also often allows to get rid of some dependently
     typed expressions such as `UScalar.ofNat`.
  -/
  trace[ScalarTac] "Original goal before preprocessing: {← getMainGoal}"
  let simpArgs : SimpArgs ← getSimpArgs
  simpAsmsTarget true {dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1}
    -- Remove the forall quantifiers to prepare for the call of `simp_all` (we
    -- don't want `simp_all` to use assumptions of the shape `∀ x, P x`))
    {simpArgs with addSimpThms := #[``forall_eq_forall']}
  -- We might have proven the goal
  if (← getGoals).isEmpty then
    trace[ScalarTac] "Goal proven by preprocessing!"
    return
  trace[ScalarTac] "Goal after first simplification: {← getMainGoal}"
  -- Apply the forward rules
  if config.saturate then
    allGoalsNoRecover (scalarTacSaturateForward config.toSaturateConfig (fun _ => pure ()))
  trace[ScalarTac] "Goal after saturation: {← getMainGoal}"
  let simpArgs : SimpArgs ← getSimpArgs
  -- Apply `simpAll`
  if config.simpAllMaxSteps ≠ 0 then
    tryTac do
      /- By setting the maxDischargeDepth at 0, we make sure that assumptions of the shape `∀ x, P x → ...`
          will not have any effect. This is important because it often happens that the user instantiates
          one such assumptions with specific arguments, meaning that if we call `simpAll` naively, those
          instantiations will get simplified to `True` and thus eliminated. -/
      Utils.simpAll
        {failIfUnchanged := false, maxSteps := config.simpAllMaxSteps, maxDischargeDepth := 0} true
        simpArgs
  -- We might have proven the goal
  if (← getGoals).isEmpty then
    trace[ScalarTac] "Goal proven by preprocessing!"
    return
  trace[ScalarTac] "Goal after simpAll: {← getMainGoal}"
  -- Call `simp` again, this time to inline the let-bindings (otherwise, omega doesn't always manage to deal with them)
  Utils.simpAt true {zetaDelta := true, failIfUnchanged := false, maxDischargeDepth := 1} simpArgs .wildcard
  -- We might have proven the goal
  if (← getGoals).isEmpty then
    trace[ScalarTac] "Goal proven by preprocessing!"
    return
  trace[ScalarTac] "Goal after 2nd simp (with zetaDelta): {← getMainGoal}"
  -- Apply normCast
  Utils.normCastAtAll
  -- We might have proven the goal
  if (← getGoals).isEmpty then
    trace[ScalarTac] "Goal proven by preprocessing!"
    return
  trace[ScalarTac] "Goal after normCast: {← getMainGoal}"
  -- Call `simp` again because `normCast` sometimes does weird things
  Utils.simpAt true {failIfUnchanged := false, maxDischargeDepth := 1} simpArgs .wildcard
  -- We might have proven the goal
  if (← getGoals).isEmpty then
    trace[ScalarTac] "Goal proven by preprocessing!"
    return
  trace[ScalarTac] "Goal after 2nd call to simpAt: {← getMainGoal}"

elab "scalar_tac_preprocess" config:Parser.Tactic.optConfig : tactic => do
  let config ← elabConfig config
  scalarTacPreprocess config

def scalarTacCore (config : Config) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  Tactic.focus do
  let simpArgs : SimpArgs ← getSimpArgs
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
        trace[ScalarTac] "Goal proved!"
    else
      trace[ScalarTac] "Calling omega"
      Tactic.Omega.omegaTactic {}
      trace[ScalarTac] "Goal proved!"

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
    throwError "scalar_tac failed to prove the goal below.\n\nNote that scalar_tac is almost equivalent to:\n  scalar_tac_preprocess; omega\n\nGoal: \n{g}"
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
        let tacs := List.map trySolve [
            -- TODO: make this more general
            ``Nat.le_mul_le, ``Nat.lt_mul_lt, ``Nat.le_mul_lt, ``Nat.lt_mul_le,
            ``Nat.mod_eq_of_lt, ``Int.emod_eq_of_lt', ``Nat.pow_le_pow_right, ``Nat.pow_le_pow_left,
            ``Nat.pow_lt_pow_right, ``Nat.le_pow, ``Nat.lt_pow,
            ``Nat.div_le_div_right, ``Nat.mul_div_le, ``Nat.div_mul_le_self]
        firstTacSolve tacs
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
