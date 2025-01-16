/- This file contains tactics to solve arithmetic goals -/

import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Ring.RingNF
import Base.Utils
import Base.Arith.Base
import Base.Arith.Init
import Base.Saturate

namespace Arith

open Utils
open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

/- Defining a custom attribute for Aesop - we use Aesop tactic in the arithmetic tactics -/

attribute [aesop (rule_sets := [Aeneas.ScalarTac]) unfold norm] Function.comp

/-
-- DEPRECATED: `int_tac` and `scalar_tac` used to rely on `aesop`. As there are performance issues
-- with the saturation tactic for now we use our own tactic. We will revert once the performance
-- is improved.
/-- The `int_tac` attribute used to tag forward theorems for the `int_tac` and `scalar_tac` tactics. -/
macro "int_tac" pat:term : attr =>
  `(attr|aesop safe forward (rule_sets := [$(Lean.mkIdent `Aeneas.ScalarTac):ident]) (pattern := $pat))

/-- The `scalar_tac` attribute used to tag forward theorems for the `int_tac` and `scalar_tac` tactics. -/
macro "scalar_tac" pat:term : attr =>
  `(attr|aesop safe forward (rule_sets := [$(Lean.mkIdent `Aeneas.ScalarTac):ident]) (pattern := $pat))

/-- The `nonlin_scalar_tac` attribute used to tag forward theorems for the `int_tac` and `scalar_tac` tactics. -/
macro "nonlin_scalar_tac" pat:term : attr =>
  `(attr|aesop safe forward (rule_sets := [$(Lean.mkIdent `Aeneas.ScalarTacNonLin):ident]) (pattern := $pat))
-/

/-- The `int_tac` attribute used to tag forward theorems for the `int_tac` and `scalar_tac` tactics. -/
macro "int_tac" pat:term : attr =>
  `(attr|aeneas_saturate (set := $(Lean.mkIdent `Aeneas.ScalarTac)) (pattern := $pat))

/-- The `scalar_tac` attribute used to tag forward theorems for the `int_tac` and `scalar_tac` tactics. -/
macro "scalar_tac" pat:term : attr =>
  `(attr|aeneas_saturate (set := $(Lean.mkIdent `Aeneas.ScalarTac)) (pattern := $pat))

/-- The `nonlin_scalar_tac` attribute used to tag forward theorems for the `int_tac` and `scalar_tac` tactics. -/
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

def intTacSimpRocs : List Name := [``Int.reduceNegSucc, ``Int.reduceNeg]

/-- Apply the scalar_tac forward rules -/
def intTacSaturateForward : Tactic.TacticM Unit := do
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
    if scalarTac.nonLin.get (← getOptions) then `Aeneas.ScalarTacNonLin :: ruleSets
    else ruleSets
  -- TODO
  -- evalAesopSaturate options ruleSets.toArray
  Saturate.evalSaturate ruleSets

-- For debugging
elab "int_tac_saturate" : tactic =>
  intTacSaturateForward

/-  Boosting a bit the `omega` tac.

    - `extraPrePreprocess`: extra-preprocessing to be done *before* this preprocessing
    - `extraPreprocess`: extra-preprocessing to be done *after* this preprocessing
 -/
def intTacPreprocess (extraPrePreprocess extraPreprocess :  Tactic.TacticM Unit) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  -- Pre-preprocessing
  extraPrePreprocess
  -- Apply the forward rules
  allGoalsNoRecover intTacSaturateForward
  -- Extra preprocessing
  allGoalsNoRecover extraPreprocess
  -- Reduce all the terms in the goal - note that the extra preprocessing step
  -- might have proven the goal, hence the `allGoals`
  let dsimp :=
    allGoalsNoRecover do tryTac (
      -- We set `simpOnly` at false on purpose.
      -- Also, we need `zetaDelta` to inline the let-bindings (otherwise, omega doesn't always manages
      -- to deal with them)
      dsimpAt false {zetaDelta := true} intTacSimpRocs
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
               -- Unfoldings
               []
                -- Simp lemmas
                [-- Int.subNatNat is very annoying - TODO: there is probably something more general thing to do
                 ``Int.subNatNat_eq_coe,
                 -- We also need this, in case the goal is: ¬ False
                 ``not_false_eq_true]
                -- Hypotheses
                [] .wildcard)

elab "int_tac_preprocess" : tactic =>
  intTacPreprocess (do pure ()) (do pure ())

/-- - `splitAllDisjs`: if true, also split all the matches/if then else in the context (note that
      `omega` splits the *disjunctions*)
    - `splitGoalConjs`: if true, split the goal if it is a conjunction so as to introduce one
      subgoal per conjunction.
-/
def intTac (tacName : String) (splitAllDisjs splitGoalConjs : Bool)
  (extraPrePreprocess extraPreprocess :  Tactic.TacticM Unit) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  Tactic.focus do
  let g ← Tactic.getMainGoal
  trace[Arith] "Original goal: {g}"
  -- Introduce all the universally quantified variables (includes the assumptions)
  let (_, g) ← g.intros
  Tactic.setGoals [g]
  -- Preprocess - wondering if we should do this before or after splitting
  -- the goal. I think before leads to a smaller proof term?
  allGoalsNoRecover (intTacPreprocess extraPrePreprocess extraPreprocess)
  -- Split the conjunctions in the goal
  if splitGoalConjs then allGoalsNoRecover (Utils.repeatTac Utils.splitConjTarget)
  /- If we split the disjunctions, split then use simp_all. Otherwise only use simp_all.
     Note that simp_all is very useful here as a "congruence" procedure. Note however that we
     only activate a very restricted set of simp lemmas (otherwise it can be very expensive,
     and have surprising behaviors). -/
  allGoalsNoRecover do
    try do
      let simpThenOmega := do
        /- IMPORTANT: we put a quite low number for `maxSteps`.
           There are two reasons.
           First, `simp_all` seems to loop at times, so by controling the maximum number of steps
           we make sure it doesn't exceed the maximum number of heart beats (or worse, overflows the
           stack).
           Second, this makes the tactic very snappy.
         -/
        Utils.tryTac (
          -- TODO: is there a simproc to simplify propositional logic?
          Utils.simpAll {failIfUnchanged := false, maxSteps := 75} true [``reduceIte] []
            [``and_self, ``false_implies, ``true_implies, ``Prod.mk.injEq,
             ``not_false_eq_true, ``not_true_eq_false,
             ``true_and, ``and_true, ``false_and, ``and_false,
             ``true_or, ``or_true,``false_or, ``or_false,
             ``Bool.true_eq_false, ``Bool.false_eq_true] [])
        allGoalsNoRecover (do
          trace[Arith] "Goal after simplification: {← getMainGoal}"
          trace[Arith] "Calling omega"
          Tactic.Omega.omegaTactic {}
          trace[Arith] "Omega solved the goal")
      if splitAllDisjs then do
        /- In order to improve performance, we first try to prove the goal without splitting. If it
           fails, we split. -/
        try
          trace[Arith] "First trying to solve the goal without splitting"
          simpThenOmega
        catch _ =>
          trace[Arith] "First attempt failed: splitting the goal and retrying"
          splitAll (allGoalsNoRecover simpThenOmega)
      else
        simpThenOmega
    catch _ =>
      let g ← Tactic.getMainGoal
      throwError "{tacName} failed to prove the goal below.\n\nNote that {tacName} is almost equivalent to:\n  {tacName}_preprocess; split_all <;> simp_all only <;> omega\n\nGoal: \n{g}"

elab "int_tac" args:(" split_goal"?): tactic =>
  let splitConjs := args.raw.getArgs.size > 0
  intTac "int_tac" true splitConjs (do pure ()) (do pure ())

-- For termination proofs
syntax "int_decr_tac" : tactic
macro_rules
  | `(tactic| int_decr_tac) =>
    `(tactic|
      simp_wf;
      -- TODO: don't use a macro (namespace problems)
      (first | apply Arith.to_int_to_nat_lt
             | apply Arith.to_int_sub_to_nat_lt) <;>
      simp_all <;> int_tac)

-- Checking that things happen correctly when there are several disjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y := by
  int_tac split_goal

--example (x y : Int) : x + y ≥ 2 := by
--  int_tac split_goal

-- Checking that things happen correctly when there are several disjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y ∧ x + y ≥ 2 := by
  int_tac split_goal

-- Checking that we can prove exfalso
example (a : Prop) (x : Int) (h0: 0 < x) (h1: x < 0) : a := by
  int_tac

-- Intermediate cast through natural numbers
example (a : Prop) (x : Int) (h0: (0 : Nat) < x) (h1: x < 0) : a := by
  int_tac

example (x : Int) (h : x ≤ -3) : x ≤ -2 := by
  int_tac

example (x y : Int) (h : x + y = 3) :
  let z := x + y
  z = 3 := by
  intro z
  omega

-- Checking that we manage to split the cases/if then else
example (x : Int) (b : Bool) (h : if b then x ≤ 0 else x ≤ 0) : x ≤ 0 := by
  int_tac

end Arith
