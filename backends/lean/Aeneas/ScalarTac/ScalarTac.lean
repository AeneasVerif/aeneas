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
import Aeneas.Simp

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
  /- -/
  saturationPasses := 3

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
def scalarTacSaturateForward {α}
  (config : SaturateConfig)
  (satState : Option Saturate.State)
  (declsToExplore : Option (Array FVarId))
  (f : Saturate.State → Array FVarId → TacticM α) : TacticM α := do
  withTraceNode `ScalarTac (fun _ => pure m!"scalarTacSaturateForward") do
  withMainContext do
  /- We always use the rule set `Aeneas.ScalarTac`, but also need to add other rule sets locally
     activated by the user. The `Aeneas.ScalarTacNonLin` rule set has a special treatment as
     it is activated through an option. -/
  let rules :=
    if config.nonLin then #[scalarTacAttribute, scalarTacNonLinAttribute]
    else #[scalarTacAttribute]
  let declsToExplore ← do
    match declsToExplore with
    | none =>
      if config.saturateAssumptions
      then pure ((← (← getLCtx).getDecls).map fun d => d.fvarId).toArray
      else pure #[]
    | some decls => pure decls
  let state ← do
    match satState with
    | none =>
      let env ← getEnv
      let rules := rules.map fun s => s.ext.getState env
      pure (Saturate.State.new rules)
    | some state => pure state
  let (state, fvarIds) ←
    Saturate.evalSaturateCore
      { visitProofTerms := false,
        visitBoundExpressions := config.saturateVisitBoundExpressions,
        saturationPasses := config.saturationPasses }
      state none none
      declsToExplore
      (exploreTarget := config.saturateTarget)
  withMainContext do f state fvarIds

-- For debugging
elab "scalar_tac_saturate" config:Parser.Tactic.optConfig : tactic => do
  let config ← elabConfig config
  let _ ← scalarTacSaturateForward config.toSaturateConfig none none (fun _ _ => pure ())

def getSimpArgs : CoreM Simp.SimpArgs := do
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
def simpAsmsTarget (simpOnly : Bool) (config : Simp.Config) (args : Simp.SimpArgs) : TacticM (Option (Array FVarId)) :=
  withMainContext do
  let props ← (← getLCtx).getAssumptions
  let props := (props.map fun d => d.fvarId).toArray
  Aeneas.Simp.simpAt simpOnly config args (.targets props true)

/-  Boosting a bit the `omega` tac. -/
def preprocess (config : Config) : Tactic.TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure m!"scalarTacPreprocess") do
  Tactic.withMainContext do
  -- Pre-preprocessing
  /- We simplify a first time before saturating the context.
     This is useful because simplifying often introduces expressions which are useful
     for the saturation phase, and it also often allows to get rid of some dependently
     typed expressions such as `UScalar.ofNat`.
  -/
  traceGoalWithNode `ScalarTac "Original goal"
  let simpArgs : Simp.SimpArgs ← getSimpArgs
  let r ← simpAsmsTarget true {dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1}
    -- Remove the forall quantifiers to prepare for the call of `simp_all` (we
    -- don't want `simp_all` to use assumptions of the shape `∀ x, P x`))
    {simpArgs with addSimpThms := #[``forall_eq_forall']}
  -- We might have proven the goal
  if r.isNone then
    trace[ScalarTac] "Goal proven by preprocessing!"
    return
  traceGoalWithNode `ScalarTac "Goal after first simplification"
  -- Apply the forward rules
  if config.saturate then
    scalarTacSaturateForward config.toSaturateConfig none none (fun _ _ => pure ())
  traceGoalWithNode `ScalarTac "Goal after saturation"
  -- Apply `simpAll`
  if config.simpAllMaxSteps ≠ 0 then
    tryTac do
      /- By setting the maxDischargeDepth at 0, we make sure that assumptions of the shape `∀ x, P x → ...`
          will not have any effect. This is important because it often happens that the user instantiates
          one such assumptions with specific arguments, meaning that if we call `simpAll` naively, those
          instantiations will get simplified to `True` and thus eliminated. -/
      Simp.simpAll
        {failIfUnchanged := false, maxSteps := config.simpAllMaxSteps, maxDischargeDepth := 0} true
        simpArgs
  -- We might have proven the goal
  if (← getGoals).isEmpty then
    trace[ScalarTac] "Goal proven by preprocessing!"
    return
  traceGoalWithNode `ScalarTac "Goal after simpAll"
  -- Call `simp` again, this time to inline the let-bindings (otherwise, omega doesn't always manage to deal with them)
  let _ ← Simp.simpAt true {zetaDelta := true, failIfUnchanged := false, maxDischargeDepth := 1} simpArgs .wildcard
  -- We might have proven the goal
  if (← getGoals).isEmpty then
    trace[ScalarTac] "Goal proven by preprocessing!"
    return
  traceGoalWithNode `ScalarTac "Goal after 2nd simp (with zetaDelta)"
  -- Apply normCast
  let _ ← Utils.normCastAt .wildcard
  -- We might have proven the goal
  if (← getGoals).isEmpty then
    trace[ScalarTac] "Goal proven by preprocessing!"
    return
  traceGoalWithNode `ScalarTac "Goal after normCast"
  -- Call `simp` again because `normCast` sometimes introduces strange terms
  let _ ← Simp.simpAt true {failIfUnchanged := false, maxDischargeDepth := 1} simpArgs .wildcard
  -- We might have proven the goal
  if (← getGoals).isEmpty then
    trace[ScalarTac] "Goal proven by preprocessing!"
    return
  traceGoalWithNode `ScalarTac "Goal after 2nd call to simpAt"

structure State where
  saturateState : Saturate.State

def State.new (config : Config) : MetaM State := do
  let env ← getEnv
  let rules :=
    if config.nonLin then #[scalarTacAttribute, scalarTacNonLinAttribute]
    else #[scalarTacAttribute]
  let rules := rules.map fun s => s.ext.getState env
  let saturateState := Saturate.State.new rules
  pure { saturateState }

def partialPreprocess (config : Config) (simpArgs : Simp.SimpArgs) (state : State)
  (zetaDelta : Bool) (simpAllAssumptions : Bool)
  (hypsToUseForSimp assumptionsToPreprocess : Array FVarId) (simpTarget : Bool) :
  Tactic.TacticM (Option (State × Array FVarId)) := do
  withTraceNode `ScalarTac (fun _ => pure m!"scalarTacPartialPreprocess") do
  Tactic.focus do
  Tactic.withMainContext do
  -- Pre-preprocessing
  /- We simplify a first time before saturating the context.
     This is useful because simplifying often introduces expressions which are useful
     for the saturation phase, and it also often allows to get rid of some dependently
     typed expressions such as `UScalar.ofNat`.
  -/
  traceGoalWithNode `ScalarTac "Original goal before preprocessing"
  let some assumptions ←
    withTraceNode `ScalarTac (fun _ => pure m!"simpAt assumptionsToPreprocess simpTarget") do
    Simp.simpAt true {dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1}
      /- Remove the forall quantifiers to prepare for the call of `simp_all` (we
        don't want `simp_all` to use assumptions of the shape `∀ x, P x`)) -/
      {simpArgs with addSimpThms := #[``forall_eq_forall']}
      -- TODO: it would be good to always simplify the target before exploring it to saturate
      (.targets assumptionsToPreprocess simpTarget)
    | trace[ScalarTac] "Goal proven by preprocessing!"; return none
  traceGoalWithNode `ScalarTac "Goal after first simplification"
  -- Apply the forward rules
  let satConfig := config.toSaturateConfig
  let satConfig := { satConfig with
    saturateAssumptions := satConfig.saturateAssumptions && config.saturate,
    saturateTarget := satConfig.saturateTarget && config.saturate,
  }
  let (saturateState, satAssumptions) ← scalarTacSaturateForward satConfig state.saturateState (some assumptions)
    fun saturateState nassumptions => pure (saturateState, nassumptions)
  withMainContext do
  let state := { state with saturateState }
  traceGoalWithNode `ScalarTac "Goal after saturation"
  /- Simplify the new assumptions with the old assumptions (it's often enough to go in that direction) -/
  let some assumptions ←
      withTraceNode `ScalarTac (fun _ => pure m!"simpAt") do
      Simp.simpAt true {dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1}
        {simpArgs with hypsToUse := hypsToUseForSimp} (.targets assumptions false)
    | trace[ScalarTac] "Goal proven by preprocessing!"; return none
  traceGoalWithNode `ScalarTac "Goal after simplifying the new assumptions with the old"
  /- Simplify the assumptions introduced through saturation with the old and new assumptions -/
  let some satAssumptions ← do
      withTraceNode `ScalarTac (fun _ => pure m!"simpAt") do
      Simp.simpAt true {dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1}
        {simpArgs with hypsToUse := hypsToUseForSimp ++ assumptions} (.targets satAssumptions false)
    | trace[ScalarTac] "Goal proven by preprocessing!"; return none
  traceGoalWithNode `ScalarTac "Goal after simplifying satAssumptions"
  /- Small helper -/
  let applySimpAll assumptions simpTarget := do
    let r ← tryTactic? do
        /- By setting the maxDischargeDepth at 0, we make sure that assumptions of the shape `∀ x, P x → ...`
            will not have any effect. This is important because it often happens that the user instantiates
            one such assumptions with specific arguments, meaning that if we call `simpAll` naively, those
            instantiations will get simplified to `True` and thus eliminated. -/
        Simp.evalSimpAllAssumptions
          {failIfUnchanged := false, maxSteps := config.simpAllMaxSteps, maxDischargeDepth := 0} true
          simpArgs assumptions simpTarget
    match r with
    | some r =>
      trace[ScalarTac] "applySimpAll succeeded"
      match r with
      | some (fvars, _) => pure (some fvars)
      | none => pure none -- Goal proven through `simpAll`
    | none =>
      trace[ScalarTac] "applySimpAll failed"
      -- `simpAll` failed: let's just continue with the same state as before
      pure (some assumptions)
  /- Apply simpAll to all the assumptions - we do it subset by subset: it is likely
      that applying simp_all on the new assumptions will finish the work, meaning that
      applying simp_all to *all* the assumptions will actually do nothing -/
  let some assumptions ← applySimpAll assumptions false
    | trace[ScalarTac] "Goal proven by preprocessing!"; return none
  traceGoalWithNode `ScalarTac "Goal after simpAll on assumptions"
  let some satAssumptions ← applySimpAll satAssumptions false
    | trace[ScalarTac] "Goal proven by preprocessing!"; return none
  traceGoalWithNode `ScalarTac "Goal after simpAll on satAssumptions"
  let assumptions := assumptions ++ satAssumptions
  let some assumptions ← applySimpAll assumptions false
    | trace[ScalarTac] "Goal proven by preprocessing!"; return none
  traceGoalWithNode `ScalarTac "Goal after simpAll on assumptions and satAssumptions"
  let some assumptions ← do
    if config.simpAllMaxSteps ≠ 0 ∧ hypsToUseForSimp.size + assumptions.size > 0 ∧ simpAllAssumptions then
      withTraceNode `ScalarTac (fun _ => pure m!"simpAll: all assumptions ") do
      applySimpAll (hypsToUseForSimp ++ assumptions) simpTarget
    else if (hypsToUseForSimp.size + assumptions.size > 0) && simpTarget then
      /- Even though there is nothing to preprocess, we want to simplify the goal by using the `hypsToUseForSimp`
          to use, to make sure we propagate equalities for instance -/
      let some _ ←
        withTraceNode `ScalarTac (fun _ => pure m!"simpAt (no assumptions to preprocess)") do
        Simp.simpAt true {failIfUnchanged := false, maxDischargeDepth := 0}
          { hypsToUse := hypsToUseForSimp ++ assumptions } (.targets #[] simpTarget)
        | trace[ScalarTac] "Goal proven by preprocessing!"; return none
      pure (some assumptions)
    else
      pure (some assumptions)
    | trace[ScalarTac] "Goal proven by preprocessing!"; return none
  traceGoalWithNode `ScalarTac "Goal after simpAll"

  -- Call `simp` again, this time to inline the let-bindings (otherwise, omega doesn't always manage to deal with them)
  let r ← do
    withTraceNode `ScalarTac (fun _ => pure m!"simpAt") do
    if zetaDelta then
      Simp.simpAt true {zetaDelta := true, failIfUnchanged := false, maxDischargeDepth := 1} simpArgs
        (.targets assumptions simpTarget)
    else pure assumptions
  -- We might have proven the goal
  let some assumptions := r
    | trace[ScalarTac] "Goal proven by preprocessing!"; return none
  traceGoalWithNode `ScalarTac "Goal after 2nd simp (with zetaDelta)"
  -- Apply normCast
  let some assumptions ←
    withTraceNode `ScalarTac (fun _ => pure m!"normCast") do
    Utils.normCastAt (.targets assumptions simpTarget)
    | trace[ScalarTac] "Goal proven by preprocessing!"; return none
  traceGoalWithNode `ScalarTac "Goal after normCast"
  -- Call `simp` again because `normCast` sometimes does weird things
  let some assumptions ←
    withTraceNode `ScalarTac (fun _ => pure m!"simpAt") do
    Simp.simpAt true {failIfUnchanged := false, maxDischargeDepth := 1} simpArgs
      (.targets assumptions simpTarget)
      | trace[ScalarTac] "Goal proven by preprocessing!"; return none
  traceGoalWithNode `ScalarTac "Goal after 2nd call to simpAt"
  /- Remove the occurrences of `forall'` in the target -/
  if simpTarget then
    let some _ ←
      withTraceNode `ScalarTac (fun _ => pure m!"simpAt") do
      Simp.simpAt true {failIfUnchanged := false, maxDischargeDepth := 0}
        { declsToUnfold := #[``forall'] } (.targets #[] simpTarget)
        | trace[ScalarTac] "Goal proven by preprocessing!"; return none
    traceGoalWithNode `ScalarTac "Goal after eliminating `forall'` in the target"
  -- We modified the assumptions in the context so we need to update the state accordingly
  let saturateState ←
    Saturate.recomputeAssumptions state.saturateState none
      -- TODO: do something smarter
      (if simpAllAssumptions then assumptions else hypsToUseForSimp ++ assumptions)
  let state := { state with saturateState }
  -- We're done
  return some (state, assumptions)

elab "scalar_tac_preprocess" config:Parser.Tactic.optConfig : tactic => do
  let config ← elabConfig config
  preprocess config

def scalarTacCore (config : Config) : Tactic.TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure m!"scalarTacCore") do
  Tactic.withMainContext do
  Tactic.focus do
  let simpArgs : Simp.SimpArgs ← getSimpArgs
  let g ← Tactic.getMainGoal
  trace[ScalarTac] "Original goal: {g}"
  -- Introduce all the universally quantified variables (includes the assumptions)
  let (_, g) ← g.intros
  Tactic.setGoals [g]
  -- Preprocess - wondering if we should do this before or after splitting
  -- the goal. I think before leads to a smaller proof term?
  allGoalsNoRecover (preprocess config)
  allGoalsNoRecover do
    if config.split then do
      trace[ScalarTac] "Splitting the goal"
      /- If we split the `if then else` call `simp_all` again -/
      splitAll do
        allGoalsNoRecover
          (tryTac do
            Simp.simpAll {failIfUnchanged := false, maxSteps := config.simpAllMaxSteps, maxDischargeDepth := 0}
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
  withTraceNode `ScalarTac (fun _ => pure m!"scalarTac") do
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

/-- Incremental version of `scalar_tac`, where we call preprocessing several times to incrementally
    saturate the context.
    TODO: do we really need the config?
 -/
def incrScalarTac (config : Config) (state : State) (toClear : Array FVarId)
  (simpAllAssumptions : Bool) (assumptions : Array FVarId) : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure m!"incrScalarTac") do
  Tactic.focus do
  Tactic.withMainContext do
  /- Clear the useless assumptions -/
  let mvarId ← (← getMainGoal).tryClearMany toClear
  setGoals [mvarId]
  /- Saturate by exploring only the goal -/
  let some (_, _) ← partialPreprocess config (← ScalarTac.getSimpArgs) state (zetaDelta := true)
    simpAllAssumptions assumptions #[] true
    | trace[ScalarTac] "incrScalarTac: goal proven by preprocessing"
  trace[ScalarTac] "Goal after preprocessing: {← getMainGoal}"
  /- Call omega -/
  trace[ScalarTac] "Calling omega"
  Tactic.Omega.omegaTactic {}
  trace[ScalarTac] "Goal proved!"

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

end ScalarTac

end Aeneas
