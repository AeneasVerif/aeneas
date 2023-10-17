/- This file contains tactics to solve arithmetic goals -/

import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.Linarith
-- TODO: there is no Omega tactic for now - it seems it hasn't been ported yet
--import Mathlib.Tactic.Omega
import Base.Utils
import Base.Arith.Base

namespace Arith

open Utils

-- Remark: I tried a version of the shape `HasScalarProp {a : Type} (x : a)`
-- but the lookup didn't work
class HasIntProp (a : Sort u) where
  prop_ty : a → Prop
  prop : ∀ x:a, prop_ty x

class PropHasImp (x : Prop) where
  concl : Prop
  prop : x → concl

instance (p : Int → Prop) : HasIntProp (Subtype p) where
  prop_ty := λ x => p x
  prop := λ x => x.property

-- This also works for `x ≠ y` because this expression reduces to `¬ x = y`
-- and `Ne` is marked as `reducible`
instance (x y : Int) : PropHasImp (¬ x = y) where
  concl := x < y ∨ x > y
  prop := λ (h:x ≠ y) => ne_is_lt_or_gt h

-- Check if a proposition is a linear integer proposition.
-- We notably use this to check the goals.
class IsLinearIntProp (x : Prop) where

instance (x y : Int) : IsLinearIntProp (x < y) where
instance (x y : Int) : IsLinearIntProp (x > y) where
instance (x y : Int) : IsLinearIntProp (x ≤ y) where
instance (x y : Int) : IsLinearIntProp (x ≥ y) where
instance (x y : Int) : IsLinearIntProp (x ≥ y) where
instance (x y : Int) : IsLinearIntProp (x = y) where
/- It seems we don't need to do any special preprocessing when the *goal*
   has the following shape - I guess `linarith` automatically calls `intro` -/
instance (x y : Int) : IsLinearIntProp (¬ x = y) where

open Lean Lean.Elab Lean.Meta

-- Explore a term by decomposing the applications (we explore the applied
-- functions and their arguments, but ignore lambdas, forall, etc. -
-- should we go inside?).
-- Remark: we pretend projections are applications, and explore the projected
-- terms.
partial def foldTermApps (k : α → Expr → MetaM α) (s : α) (e : Expr) : MetaM α := do
  -- Explore the current expression
  let e := e.consumeMData
  let s ← k s e
  -- Recurse
  match e with
  | .proj _ _ e' =>
    foldTermApps k s e'
  | .app .. =>
    e.withApp fun f args => do
      let s ← k s f
      args.foldlM (foldTermApps k) s
  | _ => pure s

-- Provided a function `k` which lookups type class instances on an expression,
-- collect all the instances lookuped by applying `k` on the sub-expressions of `e`.
def collectInstances
  (k : Expr → MetaM (Option Expr)) (s : HashSet Expr) (e : Expr) : MetaM (HashSet Expr) := do
  let k s e := do
    match ← k e with
    | none => pure s
    | some i => pure (s.insert i)
  foldTermApps k s e

-- Similar to `collectInstances`, but explores all the local declarations in the
-- main context.
def collectInstancesFromMainCtx (k : Expr → MetaM (Option Expr)) : Tactic.TacticM (HashSet Expr) := do
  Tactic.withMainContext do
  -- Get the local context
  let ctx ← Lean.MonadLCtx.getLCtx
  -- Just a matter of precaution
  let ctx ← instantiateLCtxMVars ctx
  -- Initialize the hashset
  let hs := HashSet.empty
  -- Explore the declarations
  let decls ← ctx.getDecls
  let hs ← decls.foldlM (fun hs d => collectInstances k hs d.toExpr) hs
  -- Also explore the goal
  collectInstances k hs (← Tactic.getMainTarget)

-- Helper
def lookupProp (fName : String) (className : Name) (e : Expr) : MetaM (Option Expr) := do
  trace[Arith] fName
  -- TODO: do we need Lean.observing?
  -- This actually eliminates the error messages
  trace[Arith] m!"{fName}: {e}"
  Lean.observing? do
    trace[Arith] m!"{fName}: observing: {e}"
    let ty ← Lean.Meta.inferType e
    let hasProp ← mkAppM className #[ty]
    let hasPropInst ← trySynthInstance hasProp
    match hasPropInst with
    | LOption.some i =>
      trace[Arith] "Found {fName} instance"
      let i_prop ← mkProjection i (Name.mkSimple "prop")
      some (← mkAppM' i_prop #[e])
    | _ => none

-- Return an instance of `HasIntProp` for `e` if it has some
def lookupHasIntProp (e : Expr) : MetaM (Option Expr) :=
  lookupProp "lookupHasIntProp" ``HasIntProp e

-- Collect the instances of `HasIntProp` for the subexpressions in the context
def collectHasIntPropInstancesFromMainCtx : Tactic.TacticM (HashSet Expr) := do
  collectInstancesFromMainCtx lookupHasIntProp

-- Return an instance of `PropHasImp` for `e` if it has some
def lookupPropHasImp (e : Expr) : MetaM (Option Expr) := do
  trace[Arith] m!"lookupPropHasImp: {e}"
  -- TODO: do we need Lean.observing?
  -- This actually eliminates the error messages
  Lean.observing? do
    trace[Arith] "lookupPropHasImp: observing: {e}"
    let ty ← Lean.Meta.inferType e
    trace[Arith] "lookupPropHasImp: ty: {ty}"
    let cl ← mkAppM ``PropHasImp #[ty]
    let inst ← trySynthInstance cl
    match inst with
    | LOption.some i =>
      trace[Arith] "Found PropHasImp instance"
      let i_prop ←  mkProjection i (Name.mkSimple "prop")
      some (← mkAppM' i_prop #[e])
    | _ => none

-- Collect the instances of `PropHasImp` for the subexpressions in the context
def collectPropHasImpInstancesFromMainCtx : Tactic.TacticM (HashSet Expr) := do
  collectInstancesFromMainCtx lookupPropHasImp

elab "display_prop_has_imp_instances" : tactic => do
  trace[Arith] "Displaying the PropHasImp instances"
  let hs ← collectPropHasImpInstancesFromMainCtx
  hs.forM fun e => do
    trace[Arith] "+ PropHasImp instance: {e}"

example (x y : Int) (_ : x ≠ y) (_ : ¬ x = y) : True := by
  display_prop_has_imp_instances
  simp

-- Lookup instances in a context and introduce them with additional declarations.
def introInstances (declToUnfold : Name) (lookup : Expr → MetaM (Option Expr)) : Tactic.TacticM (Array Expr) := do
  let hs ← collectInstancesFromMainCtx lookup
  hs.toArray.mapM fun e => do
    let type ← inferType e
    let name ← mkFreshAnonPropUserName
    -- Add a declaration
    let nval ← Utils.addDeclTac name e type (asLet := false)
    -- Simplify to unfold the declaration to unfold (i.e., the projector)
    Utils.simpAt [declToUnfold] [] [] (Tactic.Location.targets #[mkIdent name] false)
    -- Return the new value
    pure nval

def introHasIntPropInstances : Tactic.TacticM (Array Expr) := do
  trace[Arith] "Introducing the HasIntProp instances"
  introInstances ``HasIntProp.prop_ty lookupHasIntProp

-- Lookup the instances of `HasIntProp for all the sub-expressions in the context,
-- and introduce the corresponding assumptions
elab "intro_has_int_prop_instances" : tactic => do
  let _ ← introHasIntPropInstances

-- Lookup the instances of `PropHasImp for all the sub-expressions in the context,
-- and introduce the corresponding assumptions
elab "intro_prop_has_imp_instances" : tactic => do
  trace[Arith] "Introducing the PropHasImp instances"
  let _ ← introInstances ``PropHasImp.concl lookupPropHasImp

example (x y : Int) (h0 : x ≤ y) (h1 : x ≠ y) : x < y := by
  intro_prop_has_imp_instances
  rename_i h
  split_disj h
  . linarith
  . linarith

/- Boosting a bit the linarith tac.

   We do the following:
   - for all the assumptions of the shape `(x : Int) ≠ y` or `¬ (x = y), we
     introduce two goals with the assumptions `x < y` and `x > y`
     TODO: we could create a PR for mathlib.
 -/
def intTacPreprocess (extraPreprocess :  Tactic.TacticM Unit) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  -- Lookup the instances of PropHasImp (this is how we detect assumptions
  -- of the proper shape), introduce assumptions in the context and split
  -- on those
  -- TODO: get rid of the assumptions that we split
  let rec splitOnAsms (asms : List Expr) : Tactic.TacticM Unit :=
    match asms with
    | [] => pure ()
    | asm :: asms =>
      let k := splitOnAsms asms
      Utils.splitDisjTac asm k k
  -- Introduce the scalar bounds
  let _ ← introHasIntPropInstances
  -- Extra preprocessing, before we split on the disjunctions
  extraPreprocess
  -- Split - note that the extra-preprocessing step might actually have
  -- proven the goal (by doing simplifications for instance)
  Tactic.allGoals do
    let asms ← introInstances ``PropHasImp.concl lookupPropHasImp
    splitOnAsms asms.toList

elab "int_tac_preprocess" : tactic =>
  intTacPreprocess (do pure ())

-- Check if the goal is a linear arithmetic goal
def goalIsLinearInt : Tactic.TacticM Bool := do
  Tactic.withMainContext do
  let gty ← Tactic.getMainTarget
  match ← trySynthInstance (← mkAppM ``IsLinearIntProp #[gty]) with
  | .some _ => pure true
  | _ => pure false

def intTac (splitGoalConjs : Bool) (extraPreprocess :  Tactic.TacticM Unit) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  Tactic.focus do
  let g ← Tactic.getMainGoal
  trace[Arith] "Original goal: {g}"
  -- Introduce all the universally quantified variables (includes the assumptions)
  let (_, g) ← g.intros
  Tactic.setGoals [g]
  -- Preprocess - wondering if we should do this before or after splitting
  -- the goal. I think before leads to a smaller proof term?
  Tactic.allGoals (intTacPreprocess extraPreprocess)
  -- More preprocessing
  Tactic.allGoals (Utils.tryTac (Utils.simpAt [] [``nat_zero_eq_int_zero] [] .wildcard))
  -- Split the conjunctions in the goal
  if splitGoalConjs then Tactic.allGoals (Utils.repeatTac Utils.splitConjTarget)
  -- Call linarith
  let linarith := do
    let cfg : Linarith.LinarithConfig := {
      -- We do this with our custom preprocessing
      splitNe := false
    }
    Tactic.liftMetaFinishingTactic <| Linarith.linarith false [] cfg
  Tactic.allGoals do
    -- We check if the goal is a linear arithmetic goal: if yes, we directly
    -- call linarith, otherwise we first apply exfalso (we do this because
    -- linarith is too general and sometimes fails to do this correctly).
    if ← goalIsLinearInt then do
      trace[Arith] "linarith goal: {← Tactic.getMainGoal}"
      linarith
    else do
      let g ← Tactic.getMainGoal
      let gs ← g.apply (Expr.const ``False.elim [.zero])
      let goals ← Tactic.getGoals
      Tactic.setGoals (gs ++ goals)
      Tactic.allGoals do
        trace[Arith] "linarith goal: {← Tactic.getMainGoal}"
        linarith

elab "int_tac" args:(" split_goal"?): tactic =>
  let split := args.raw.getArgs.size > 0
  intTac split (do pure ())

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

example (x : Int) (h0: 0 ≤ x) (h1: x ≠ 0) : 0 < x := by
  int_tac_preprocess
  linarith
  linarith

example (x : Int) (h0: 0 ≤ x) (h1: x ≠ 0) : 0 < x := by
  int_tac

-- Checking that things append correctly when there are several disjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y := by
  int_tac split_goal

-- Checking that things append correctly when there are several disjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y ∧ x + y ≥ 2 := by
  int_tac split_goal

-- Checking that we can prove exfalso
example (a : Prop) (x : Int) (h0: 0 < x) (h1: x < 0) : a := by
  int_tac

end Arith
