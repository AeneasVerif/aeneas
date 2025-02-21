import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Ring.RingNF
import Aeneas.Utils
import Aeneas.ScalarTac.Core
import Aeneas.ScalarTac.Init
import Aeneas.Saturate

namespace Aeneas

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

def scalarTacSimpRocs : List Name := [
  ``Nat.reducePow, ``Nat.reduceAdd, ``Nat.reduceSub, ``Nat.reduceMul, ``Nat.reduceDiv, ``Nat.reduceMod,
  ``Int.reducePow, ``Int.reduceAdd, ``Int.reduceSub, ``Int.reduceMul, ``Int.reduceDiv, ``Int.reduceMod,
  ``Int.reduceNegSucc, ``Int.reduceNeg,]

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
  /- if `true`, split the goal if it is a conjunction so as to introduce one
     subgoal per conjunction. -/
  splitGoal : Bool := false
  /- Maximum number of steps to take with `simpAll` during the preprocessing phase.
     If equal to 0, we do not call `simpAll` at all.
   -/
  simpAllMaxSteps : Nat := 200

declare_config_elab elabConfig Config

/-- Apply the scalar_tac forward rules -/
def scalarTacSaturateForward (nonLin : Bool): Tactic.TacticM Unit := do
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
  Saturate.evalSaturate ruleSets

-- For debugging
elab "scalar_tac_saturate" config:Parser.Tactic.optConfig : tactic => do
  let config ← elabConfig config
  scalarTacSaturateForward config.nonLin

/-  Boosting a bit the `omega` tac.

    - `extraPrePreprocess`: extra-preprocessing to be done *before* this preprocessing
    - `extraPreprocess`: extra-preprocessing to be done *after* this preprocessing
 -/
def scalarTacPreprocess (config : Config) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  let simpLemmas ← scalarTacSimpExt.getTheorems
  -- Pre-preprocessing
  /- First get rid of [ofInt] (if there are dependent arguments, we may not
     manage to simplify the context) -/
  Utils.simpAt true {dsimp := false, failIfUnchanged := false}
                -- Simprocs
                scalarTacSimpRocs
                -- Simp theorems
                [simpLemmas]
                -- Unfoldings
                []
                -- Simp lemmas
                []
                -- Hypotheses
                [] .wildcard
  -- Apply the forward rules
  allGoalsNoRecover (scalarTacSaturateForward config.nonLin)
  -- Reduce all the terms in the goal - note that the extra preprocessing step
  -- might have proven the goal, hence the `allGoals`
  let dsimp :=
    allGoalsNoRecover do tryTac (
      -- We set `simpOnly` at false on purpose.
      -- Also, we need `zetaDelta` to inline the let-bindings (otherwise, omega doesn't always manages
      -- to deal with them)
      dsimpAt false {zetaDelta := true} scalarTacSimpRocs
        -- Simp theorems
        []
        -- Declarations to unfold
        []
        -- Theorems
        []
        [] Tactic.Location.wildcard)
  dsimp
  -- More preprocessing: apply norm_cast to the whole context
  allGoalsNoRecover (Utils.tryTac (Utils.normCastAtAll))
  -- norm_cast does weird things with negative numbers so we reapply simp
  dsimp
  allGoalsNoRecover do Utils.tryTac (
    Utils.simpAt true {}
               -- Simprocs
               []
               -- Simp theorems
               [simpLemmas]
               -- Unfoldings
               []
                -- Simp lemmas
                [-- Int.subNatNat is very annoying - TODO: there is probably something more general thing to do
                 ``Int.subNatNat_eq_coe,
                 -- We also need this, in case the goal is: ¬ False
                 ``not_false_eq_true,
                 -- Remove the forall quantifiers to prepare for the call of `simp_all` (we
                 -- don't want `simp_all` to use assumptions of the shape `∀ x, P x`))
                 ``forall_eq_forall'
                 ]
                -- Hypotheses
                [] .wildcard)

elab "scalar_tac_preprocess" config:Parser.Tactic.optConfig : tactic => do
  let config ← elabConfig config
  scalarTacPreprocess config

/-- - `splitAllDisjs`: if true, also split all the matches/if then else in the context (note that
      `omega` splits the *disjunctions*)
    - `splitGoalConjs`: if true, split the goal if it is a conjunction so as to introduce one
      subgoal per conjunction.
-/
def scalarTac (config : Config) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  Tactic.focus do
  let g ← Tactic.getMainGoal
  trace[ScalarTac] "Original goal: {g}"
  -- Introduce all the universally quantified variables (includes the assumptions)
  let (_, g) ← g.intros
  Tactic.setGoals [g]
  -- Preprocess - wondering if we should do this before or after splitting
  -- the goal. I think before leads to a smaller proof term?
  allGoalsNoRecover (scalarTacPreprocess config)
  -- Split the conjunctions in the goal
  if config.splitGoal then allGoalsNoRecover (Utils.repeatTac Utils.splitConjTarget)
  /- If we split the disjunctions, split then use simp_all. Otherwise only use simp_all.
     Note that simp_all is very useful here as a "congruence" procedure. Note however that we
     only activate a very restricted set of simp lemmas (otherwise it can be very expensive,
     and have surprising behaviors). -/
  allGoalsNoRecover do
    try do
      let simpThenOmega := do
        if config.simpAllMaxSteps ≠ 0 then
          Utils.tryTac (
            -- TODO: is there a simproc to simplify propositional logic?
            Utils.simpAll {failIfUnchanged := false, maxSteps := config.simpAllMaxSteps, maxDischargeDepth := 1} true
              [``reduceIte] [] []
              [``and_self, ``false_implies, ``true_implies, ``Prod.mk.injEq,
              ``not_false_eq_true, ``not_true_eq_false,
              ``true_and, ``and_true, ``false_and, ``and_false,
              ``true_or, ``or_true,``false_or, ``or_false,
              ``Bool.true_eq_false, ``Bool.false_eq_true,
              -- The following lemmas are used to simplify occurrences of `decide`
              ``decide_eq_true_eq, ``Bool.or_eq_true, ``Bool.and_eq_true] [])
        allGoalsNoRecover (do
          trace[ScalarTac] "Goal after simplification: {← getMainGoal}"
          trace[ScalarTac] "Calling omega"
          Tactic.Omega.omegaTactic {}
          trace[ScalarTac] "Omega solved the goal")
      if config.split then do
        /- In order to improve performance, we first try to prove the goal without splitting. If it
           fails, we split. -/
        try
          trace[ScalarTac] "First trying to solve the goal without splitting"
          simpThenOmega
        catch _ =>
          trace[ScalarTac] "First attempt failed: splitting the goal and retrying"
          splitAll (allGoalsNoRecover simpThenOmega)
      else
        simpThenOmega
    catch _ =>
      let g ← Tactic.getMainGoal
      throwError "scalar_tac failed to prove the goal below.\n\nNote that scalar_tac is almost equivalent to:\n  scalar_tac_preprocess; split_all <;> simp_all only <;> omega\n\nGoal: \n{g}"

example : True := by simp

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

-- Checking that things happen correctly when there are several disjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y := by
  scalar_tac +splitGoal

-- Checking that things happen correctly when there are several disjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y ∧ x + y ≥ 2 := by
  scalar_tac +splitGoal

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

end ScalarTac

end Aeneas
