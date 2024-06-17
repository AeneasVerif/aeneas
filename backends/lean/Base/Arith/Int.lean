/- This file contains tactics to solve arithmetic goals -/

import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Base.Utils
import Base.Arith.Base

namespace Arith

open Utils
open Lean Lean.Elab Lean.Meta

/- We can introduce a term in the context.
   For instance, if we find `x : U32` in the context we can introduce `0 ≤ x ∧ x ≤ U32.max`

   Remark: I tried a version of the shape `HasScalarProp {a : Type} (x : a)`
   but the lookup didn't work.
 -/
class HasIntProp (a : Sort u) where
  prop_ty : a → Prop
  prop : ∀ x:a, prop_ty x

/- Terms that induces predicates: if we can find the term `x`, we can introduce `concl` in the context. -/
class HasIntPred {a: Sort u} (x: a) where
  concl : Prop
  prop : concl

/- Proposition with implications: if we find P we can introduce Q in the context -/
class PropHasImp (x : Sort u) where
  concl : Prop
  prop : x → concl

instance (p : Int → Prop) : HasIntProp (Subtype p) where
  prop_ty := λ x => p x
  prop := λ x => x.property

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

/- Explore a term by decomposing the applications (we explore the applied
   functions and their arguments, but ignore lambdas, forall, etc. -
   should we go inside?).

   Remark: we pretend projections are applications, and explore the projected
   terms. -/
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

/- Provided a function `k` which lookups type class instances on an expression,
   collect all the instances lookuped by applying `k` on the sub-expressions of `e`. -/
def collectInstances
  (k : Expr → MetaM (Option Expr)) (s : HashSet Expr) (e : Expr) : MetaM (HashSet Expr) := do
  let k s e := do
    match ← k e with
    | none => pure s
    | some i => pure (s.insert i)
  foldTermApps k s e

/- Similar to `collectInstances`, but explores all the local declarations in the
   main context. -/
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
  let hs ← decls.foldlM (fun hs d => do 
    -- Collect instances over all subexpressions
    -- of the inferred type rather than the declaration expression
    -- which is often just a name.
    let ty ← Lean.Meta.inferType d.toExpr
    collectInstances k hs ty
  ) hs
  -- Also explore the goal
  collectInstances k hs (← Tactic.getMainTarget)

-- Helper
def lookupProp (fName : String) (className : Name) (e : Expr) (instantiateClassFn : Expr → Expr → Array Expr) (instantiateProjectionFn : Expr → Array Expr) : MetaM (Option Expr) := do
  trace[Arith] fName
  -- TODO: do we need Lean.observing?
  -- This actually eliminates the error messages
  trace[Arith] m!"{fName}: {e}"
  Lean.observing? do
    trace[Arith] m!"{fName}: observing: {e}"
    let ty ← Lean.Meta.inferType e
    let hasProp ← mkAppM className (instantiateClassFn ty e)
    let hasPropInst ← trySynthInstance hasProp
    match hasPropInst with
    | LOption.some i =>
      trace[Arith] "Found {fName} instance"
      let i_prop ← mkProjection i (Name.mkSimple "prop")
      some (← mkAppM' i_prop (instantiateProjectionFn e))
    | _ => none

-- Return an instance of `HasIntProp` for `e` if it has some
def lookupHasIntProp (e : Expr) : MetaM (Option Expr) :=
  lookupProp "lookupHasIntProp" ``HasIntProp e (fun ty _ => #[ty]) (fun e => #[e])

-- Collect the instances of `HasIntProp` for the subexpressions in the context
def collectHasIntPropInstancesFromMainCtx : Tactic.TacticM (HashSet Expr) := do
  collectInstancesFromMainCtx lookupHasIntProp

-- Return an instance of `HasIntPred` for `e` if it has some
def lookupHasIntPred (e : Expr) : MetaM (Option Expr) :=
  lookupProp "lookupHasIntPred" ``HasIntPred e (fun _ term => #[term]) (fun _ => #[])

-- Collect the instances of `HasIntPred` for the subexpressions in the context
def collectHasIntPredInstancesFromMainCtx : Tactic.TacticM (HashSet Expr) := do 
  collectInstancesFromMainCtx lookupHasIntPred

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

example (x y : Int) (h0 : x ≤ y) (h1 : x ≠ y) : x < y := by
  omega

-- Lookup instances in a context and introduce them with additional declarations.
def introInstances (declToUnfold : Name) (lookup : Expr → MetaM (Option Expr)) : Tactic.TacticM (Array Expr) := do
  let hs ← collectInstancesFromMainCtx lookup
  hs.toArray.mapM fun e => do
    let type ← inferType e
    let name ← mkFreshAnonPropUserName
    -- Add a declaration
    let nval ← Utils.addDeclTac name e type (asLet := false)
    -- Simplify to unfold the declaration to unfold (i.e., the projector)
    Utils.simpAt true {} #[] [declToUnfold] [] [] (Location.targets #[mkIdent name] false)
    -- Return the new value
    pure nval

def introHasIntPropInstances : Tactic.TacticM (Array Expr) := do
  trace[Arith] "Introducing the HasIntProp instances"
  introInstances ``HasIntProp.prop_ty lookupHasIntProp

-- Lookup the instances of `HasIntProp for all the sub-expressions in the context,
-- and introduce the corresponding assumptions
elab "intro_has_int_prop_instances" : tactic => do
  let _ ← introHasIntPropInstances

def introHasIntPredInstances : Tactic.TacticM (Array Expr) := do 
  trace[Arith] "Introducing the HasIntPred instances"
  introInstances ``HasIntPred.concl lookupHasIntPred

elab "intro_has_int_pred_instances" : tactic => do
  let _ ← introHasIntPredInstances

def introPropHasImpInstances : Tactic.TacticM (Array Expr) := do
  trace[Arith] "Introducing the PropHasImp instances"
  introInstances ``PropHasImp.concl lookupPropHasImp

-- Lookup the instances of `PropHasImp for all the sub-expressions in the context,
-- and introduce the corresponding assumptions
elab "intro_prop_has_imp_instances" : tactic => do
  let _ ← introPropHasImpInstances

/- Boosting a bit the `omega` tac.
 -/
def intTacPreprocess (extraPreprocess :  Tactic.TacticM Unit) : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  -- Introduce the instances of `HasIntProp`
  let _ ← introHasIntPropInstances
  -- Introduce the instances of `HasIntPred`
  let _ ← introHasIntPredInstances
  -- Introduce the instances of `PropHasImp`
  let _ ← introPropHasImpInstances
  -- Extra preprocessing
  extraPreprocess
  -- Reduce all the terms in the goal - note that the extra preprocessing step
  -- might have proven the goal, hence the `Tactic.allGoals`
  Tactic.allGoals do tryTac (dsimpAt false {} #[] [] [] [] Tactic.Location.wildcard)

elab "int_tac_preprocess" : tactic =>
  intTacPreprocess (do pure ())

def intTac (tacName : String) (splitGoalConjs : Bool) (extraPreprocess :  Tactic.TacticM Unit) : Tactic.TacticM Unit := do
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
  Tactic.allGoals (Utils.tryTac (Utils.simpAt true {} #[] [] [``nat_zero_eq_int_zero] [] .wildcard))
  -- Split the conjunctions in the goal
  if splitGoalConjs then Tactic.allGoals (Utils.repeatTac Utils.splitConjTarget)
  -- Call omega
  Tactic.allGoals do
    try do Tactic.Omega.omegaTactic {}
    catch _ =>
      let g ← Tactic.getMainGoal
      throwError "{tacName} failed to prove the goal:\n{g}"

elab "int_tac" args:(" split_goal"?): tactic =>
  let split := args.raw.getArgs.size > 0
  intTac "int_tac" split (do pure ())

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

-- Checking that things happen correctly when there are several disjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y ∧ x + y ≥ 2 := by
  int_tac split_goal

-- Checking that we can prove exfalso
example (a : Prop) (x : Int) (h0: 0 < x) (h1: x < 0) : a := by
  int_tac

end Arith
