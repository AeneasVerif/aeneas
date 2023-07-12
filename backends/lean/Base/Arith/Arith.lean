/- This file contains tactics to solve arithmetic goals -/

import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.Linarith
-- TODO: there is no Omega tactic for now - it seems it hasn't been ported yet
--import Mathlib.Tactic.Omega
import Base.Primitives
import Base.Utils
import Base.Arith.Base

/-
Mathlib tactics:
- rcases: https://leanprover-community.github.io/mathlib_docs/tactics.html#rcases
- split_ifs: https://leanprover-community.github.io/mathlib_docs/tactics.html#split_ifs
- norm_num: https://leanprover-community.github.io/mathlib_docs/tactics.html#norm_num
- should we use linarith or omega?
- hint: https://leanprover-community.github.io/mathlib_docs/tactics.html#hint
- classical: https://leanprover-community.github.io/mathlib_docs/tactics.html#classical
-/

namespace List

  -- TODO: I could not find this function??
  @[simp] def flatten {a : Type u} : List (List a) → List a
  | [] => []
  | x :: ls => x ++ flatten ls

end List

namespace Lean

namespace LocalContext

  open Lean Lean.Elab Command Term Lean.Meta

  -- Small utility: return the list of declarations in the context, from
  -- the last to the first.
  def getAllDecls (lctx : Lean.LocalContext) : MetaM (List Lean.LocalDecl) :=
    lctx.foldrM (fun d ls => do let d ← instantiateLocalDeclMVars d; pure (d :: ls)) []

  -- Return the list of declarations in the context, but filter the
  -- declarations which are considered as implementation details
  def getDecls (lctx : Lean.LocalContext) : MetaM (List Lean.LocalDecl) := do
    let ls ← lctx.getAllDecls
    pure (ls.filter (fun d => not d.isImplementationDetail))

end LocalContext

end Lean

namespace Arith

open Primitives

-- TODO: move?
theorem ne_zero_is_lt_or_gt {x : Int} (hne : x ≠ 0) : x < 0 ∨ x > 0 := by
  cases h: x <;> simp_all
  . rename_i n;
    cases n <;> simp_all
  . apply Int.negSucc_lt_zero

-- TODO: move?
theorem ne_is_lt_or_gt {x y : Int} (hne : x ≠ y) : x < y ∨ x > y := by
  have hne : x - y ≠ 0 := by
    simp
    intro h
    have: x = y := by linarith
    simp_all
  have h := ne_zero_is_lt_or_gt hne
  match h with
  | .inl _ => left; linarith
  | .inr _ => right; linarith

-- TODO: move
instance Vec.cast (a : Type): Coe (Vec a) (List a)  where coe := λ v => v.val

-- TODO: move
/- Remark: we can't write the following instance because of restrictions about
   the type class parameters (`ty` doesn't appear in the return type, which is
   forbidden):

   ```
   instance Scalar.cast (ty : ScalarTy) : Coe (Scalar ty) Int where coe := λ v => v.val
   ```
 -/
def Scalar.toInt {ty : ScalarTy} (x : Scalar ty) : Int := x.val

-- Remark: I tried a version of the shape `HasProp {a : Type} (x : a)`
-- but the lookup didn't work
class HasProp (a : Sort u) where
  prop_ty : a → Prop
  prop : ∀ x:a, prop_ty x

instance (ty : ScalarTy) : HasProp (Scalar ty) where
  -- prop_ty is inferred
  prop := λ x => And.intro x.hmin x.hmax

instance (a : Type) : HasProp (Vec a) where
  prop_ty := λ v => v.val.length ≤ Scalar.max ScalarTy.Usize
  prop := λ ⟨ _, l ⟩ => l

class PropHasImp (x : Prop) where
  concl : Prop
  prop : x → concl

-- This also works for `x ≠ y` because this expression reduces to `¬ x = y`
-- and `Ne` is marked as `reducible`
instance (x y : Int) : PropHasImp (¬ x = y) where
  concl := x < y ∨ x > y
  prop := λ (h:x ≠ y) => ne_is_lt_or_gt h

open Lean Lean.Elab Command Term Lean.Meta

-- Small utility: print all the declarations in the context
elab "print_all_decls" : tactic => do
  let ctx ← Lean.MonadLCtx.getLCtx
  for decl in ← ctx.getDecls do
    let ty ← Lean.Meta.inferType decl.toExpr
    logInfo m!"{decl.toExpr} : {ty}"
  pure ()

-- Explore a term by decomposing the applications (we explore the applied
-- functions and their arguments, but ignore lambdas, forall, etc. -
-- should we go inside?).
partial def foldTermApps (k : α → Expr → MetaM α) (s : α) (e : Expr) : MetaM α := do
  -- We do it in a very simpler manner: we deconstruct applications,
  -- and recursively explore the sub-expressions. Note that we do
  -- not go inside foralls and abstractions (should we?).
  e.withApp fun f args => do
    let s ← k s f
    args.foldlM (foldTermApps k) s

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
  decls.foldlM (fun hs d => collectInstances k hs d.toExpr) hs

-- Return an instance of `HasProp` for `e` if it has some
def lookupHasProp (e : Expr) : MetaM (Option Expr) := do
  trace[Arith] "lookupHasProp"
  -- TODO: do we need Lean.observing?
  -- This actually eliminates the error messages
  Lean.observing? do
    trace[Arith] "lookupHasProp: observing"
    let ty ← Lean.Meta.inferType e
    let hasProp ← mkAppM ``HasProp #[ty]
    let hasPropInst ← trySynthInstance hasProp
    match hasPropInst with
    | LOption.some i =>
      trace[Arith] "Found HasProp instance"
      let i_prop ← mkProjection i (Name.mkSimple "prop")
      some (← mkAppM' i_prop #[e])
    | _ => none

-- Collect the instances of `HasProp` for the subexpressions in the context
def collectHasPropInstancesFromMainCtx : Tactic.TacticM (HashSet Expr) := do
  collectInstancesFromMainCtx lookupHasProp

elab "display_has_prop_instances" : tactic => do
  trace[Arith] "Displaying the HasProp instances"
  let hs ← collectHasPropInstancesFromMainCtx
  hs.forM fun e => do
    trace[Arith] "+ HasProp instance: {e}"

example (x : U32) : True := by
  let i : HasProp U32 := inferInstance
  have p := @HasProp.prop _ i x
  simp only [HasProp.prop_ty] at p
  display_has_prop_instances
  simp

-- Return an instance of `PropHasImp` for `e` if it has some
def lookupPropHasImp (e : Expr) : MetaM (Option Expr) := do
  trace[Arith] "lookupPropHasImp"
  -- TODO: do we need Lean.observing?
  -- This actually eliminates the error messages
  Lean.observing? do
    trace[Arith] "lookupPropHasImp: observing"
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
    let name ← mkFreshUserName `h
    -- Add a declaration
    let nval ← Utils.addDeclTac name e type (asLet := false)
    -- Simplify to unfold the declaration to unfold (i.e., the projector)
    Utils.simpAt [declToUnfold] [] [] (Tactic.Location.targets #[mkIdent name] false)
    -- Return the new value
    pure nval

def introHasPropInstances : Tactic.TacticM (Array Expr) := do
  trace[Arith] "Introducing the HasProp instances"
  introInstances ``HasProp.prop_ty lookupHasProp

-- Lookup the instances of `HasProp for all the sub-expressions in the context,
-- and introduce the corresponding assumptions
elab "intro_has_prop_instances" : tactic => do
  let _ ← introHasPropInstances

example (x y : U32) : x.val ≤ Scalar.max ScalarTy.U32 := by
  intro_has_prop_instances
  simp [*]

example {a: Type} (v : Vec a) : v.val.length ≤ Scalar.max ScalarTy.Usize := by
  intro_has_prop_instances
  simp_all [Scalar.max, Scalar.min]

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
def intTacPreprocess : Tactic.TacticM Unit := do
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
  -- Introduce
  let asms ← introInstances ``PropHasImp.concl lookupPropHasImp
  -- Split
  splitOnAsms asms.toList

elab "int_tac_preprocess" : tactic =>
  intTacPreprocess

def intTac : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  Tactic.focus do
  -- Preprocess - wondering if we should do this before or after splitting
  -- the goal. I think before leads to a smaller proof term?
  Tactic.allGoals intTacPreprocess
  -- Split the conjunctions in the goal
  Utils.repeatTac Utils.splitConjTarget
  -- Call linarith
  let linarith :=
    let cfg : Linarith.LinarithConfig := {
      -- We do this with our custom preprocessing
      splitNe := false
    }
    Tactic.liftMetaFinishingTactic <| Linarith.linarith false [] cfg
  Tactic.allGoals linarith

elab "int_tac" : tactic =>
  intTac

example (x : Int) (h0: 0 ≤ x) (h1: x ≠ 0) : 0 < x := by
  int_tac_preprocess
  linarith
  linarith

example (x : Int) (h0: 0 ≤ x) (h1: x ≠ 0) : 0 < x := by
  int_tac

-- Checking that things append correctly when there are several disjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y := by
  int_tac

-- Checking that things append correctly when there are several disjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y ∧ x + y ≥ 2 := by
  int_tac

-- A tactic to solve linear arithmetic goals in the presence of scalars
def scalarTac : Tactic.TacticM Unit := do
  Tactic.withMainContext do
  -- Introduce the scalar bounds
  let _ ← introHasPropInstances
  Tactic.allGoals do
  -- Inroduce the bounds for the isize/usize types
  let add (e : Expr) : Tactic.TacticM Unit := do
    let ty ← inferType e
    let _ ← Utils.addDeclTac (← mkFreshUserName `h) e ty (asLet := false)
  add (← mkAppM ``Scalar.cMin_bound #[.const ``ScalarTy.Usize []])
  add (← mkAppM ``Scalar.cMin_bound #[.const ``ScalarTy.Isize []])
  add (← mkAppM ``Scalar.cMax_bound #[.const ``ScalarTy.Usize []])
  add (← mkAppM ``Scalar.cMax_bound #[.const ``ScalarTy.Isize []])
  -- Reveal the concrete bounds - TODO: not too sure about that.
  -- Maybe we should reveal the "concrete" bounds (after normalization)
  Utils.simpAt [``Scalar.max, ``Scalar.min, ``Scalar.cMin, ``Scalar.cMax] [] [] .wildcard
  -- Apply the integer tactic
  intTac

elab "scalar_tac" : tactic =>
  scalarTac

example (x y : U32) : x.val ≤ Scalar.max ScalarTy.U32 := by
  scalar_tac

example {a: Type} (v : Vec a) : v.val.length ≤ Scalar.max ScalarTy.Usize := by
  scalar_tac

end Arith
