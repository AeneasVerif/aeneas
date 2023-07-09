/- This file contains tactics to solve arithmetic goals -/

import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.Linarith
-- TODO: there is no Omega tactic for now - it seems it hasn't been ported yet
--import Mathlib.Tactic.Omega
import Base.Primitives
import Base.ArithBase

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
  Lean.Elab.Tactic.withMainContext do
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


set_option trace.Arith true

example (x : U32) : True := by
  let i : HasProp U32 := inferInstance
  have p := @HasProp.prop _ i x
  simp only [HasProp.prop_ty] at p
  display_has_prop_instances
  simp

set_option trace.Arith false

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

set_option trace.Arith true

example (x y : Int) (h0 : x ≠ y) (h1 : ¬ x = y) : True := by
  display_prop_has_imp_instances
  simp

set_option trace.Arith false

def addDecl (name : Name) (val : Expr) (type : Expr) (asLet : Bool) : Tactic.TacticM Expr :=
  -- I don't think we need that
  Lean.Elab.Tactic.withMainContext do
  -- Insert the new declaration
  let withDecl := if asLet then withLetDecl name type val else withLocalDeclD name type
  withDecl fun nval => do
    -- For debugging
    let lctx ← Lean.MonadLCtx.getLCtx
    let fid := nval.fvarId!
    let decl := lctx.get! fid
    trace[Arith] "  new decl: \"{decl.userName}\" ({nval}) : {decl.type} := {decl.value}"
    --
    -- Tranform the main goal `?m0` to `let x = nval in ?m1`
    let mvarId ← Tactic.getMainGoal
    let newMVar ← mkFreshExprSyntheticOpaqueMVar (← mvarId.getType)
    let newVal ← mkLetFVars #[nval] newMVar
    -- There are two cases:
    -- - asLet is true: newVal is `let $name := $val in $newMVar`
    -- - asLet is false: ewVal is `λ $name => $newMVar`
    --   We need to apply it to `val`
    let newVal := if asLet then newVal else mkAppN newVal #[val]
    -- Assign the main goal and update the current goal
    mvarId.assign newVal
    let goals ← Tactic.getUnsolvedGoals
    Lean.Elab.Tactic.setGoals (newMVar.mvarId! :: goals)
    -- Return the new value - note: we are in the *new* context, created
    -- after the declaration was added, so it will persist
    pure nval

def addDeclSyntax (name : Name) (val : Syntax) (asLet : Bool) : Tactic.TacticM Unit :=
  -- I don't think we need that
  Lean.Elab.Tactic.withMainContext do
  --
  let val ← elabTerm val .none
  let type ← inferType val
  -- In some situations, the type will be left as a metavariable (for instance,
  -- if the term is `3`, Lean has the choice between `Nat` and `Int` and will
  -- not choose): we force the instantiation of the meta-variable
  synthesizeSyntheticMVarsUsingDefault
  --
  let _ ← addDecl name val type asLet

elab "custom_let " n:ident " := " v:term : tactic => do
  addDeclSyntax n.getId v (asLet := true)

elab "custom_have " n:ident " := " v:term : tactic =>
  addDeclSyntax n.getId v (asLet := false)

example : Nat := by
  custom_let x := 4
  custom_have y := 4
  apply y

example (x : Bool) : Nat := by
  cases x <;> custom_let x := 3 <;> apply x

-- Lookup instances in a context and introduce them with additional declarations.
def introInstances (declToUnfold : Name) (lookup : Expr → MetaM (Option Expr)) : Tactic.TacticM (Array Expr) := do
  let hs ← collectInstancesFromMainCtx lookup
  hs.toArray.mapM fun e => do
    let type ← inferType e
    let name ← mkFreshUserName `h
    -- Add a declaration
    let nval ← addDecl name e type (asLet := false)
    -- Simplify to unfold the declaration to unfold (i.e., the projector)
    let simpTheorems ← Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
    -- Add the equational theorem for the decl to unfold
    let simpTheorems ← simpTheorems.addDeclToUnfold declToUnfold
    let congrTheorems ← getSimpCongrTheorems
    let ctx : Simp.Context := { simpTheorems := #[simpTheorems], congrTheorems }
    -- Where to apply the simplifier
    let loc := Tactic.Location.targets #[mkIdent name] false
    -- Apply the simplifier
    let _ ← Tactic.simpLocation ctx (discharge? := .none) loc
    -- Return the new value
    pure nval

-- Lookup the instances of `HasProp for all the sub-expressions in the context,
-- and introduce the corresponding assumptions
elab "intro_has_prop_instances" : tactic => do
  trace[Arith] "Introducing the HasProp instances"
  let _ ← introInstances ``HasProp.prop_ty lookupHasProp

example (x y : U32) : x.val ≤ Scalar.max ScalarTy.U32 := by
  intro_has_prop_instances
  simp [*]

example {a: Type} (v : Vec a) : v.val.length ≤ Scalar.max ScalarTy.Usize := by
  intro_has_prop_instances
  simp_all [Scalar.max, Scalar.min]

-- Tactic to split on a disjunction
def splitDisj (h : Expr) (kleft kright : Tactic.TacticM Unit) : Tactic.TacticM Unit := do
  trace[Arith] "assumption on which to split: {h}"
  -- Retrieve the main goal
  Lean.Elab.Tactic.withMainContext do
  let goalType ← Lean.Elab.Tactic.getMainTarget
  -- Case disjunction
  let hTy ← inferType h
  hTy.withApp fun f xs => do
  trace[Arith] "as app: {f} {xs}"
  -- Sanity check
  if ¬ (f.isConstOf ``Or ∧ xs.size = 2) then throwError "Invalid argument to splitDisj"
  let a := xs.get! 0
  let b := xs.get! 1
  -- Introduce the new goals
  -- Returns:
  -- - the match branch
  -- - a fresh new mvar id
  let mkGoal (hTy : Expr) (nGoalName : String) : MetaM (Expr × MVarId) := do
    -- Introduce a variable for the assumption (`a` or `b`)
    let asmName ← mkFreshUserName `h
    withLocalDeclD asmName hTy fun var => do
    -- The new goal
    let mgoal ← mkFreshExprSyntheticOpaqueMVar goalType (tag := Name.mkSimple nGoalName)
    -- The branch expression
    let branch ← mkLambdaFVars #[var] mgoal
    pure (branch, mgoal.mvarId!)
  let (inl, mleft) ← mkGoal a "left"
  let (inr, mright) ← mkGoal b "right"
  trace[Arith] "left: {inl}: {mleft}"
  trace[Arith] "right: {inr}: {mright}"
  -- Create the match expression
  withLocalDeclD (← mkFreshUserName `h) hTy fun hVar => do
  let motive ← mkLambdaFVars #[hVar] goalType
  let casesExpr ← mkAppOptM ``Or.casesOn #[a, b, motive, h, inl, inr]
  let mgoal ← Tactic.getMainGoal
  trace[Arith] "goals: {← Tactic.getUnsolvedGoals}"
  trace[Arith] "main goal: {mgoal}"
  mgoal.assign casesExpr
  let goals ← Tactic.getUnsolvedGoals
  -- Focus on the left
  Tactic.setGoals [mleft]
  kleft
  let leftGoals ← Tactic.getUnsolvedGoals
  -- Focus on the right
  Tactic.setGoals [mright]
  kright
  let rightGoals ← Tactic.getUnsolvedGoals
  -- Put all the goals back
  Tactic.setGoals (leftGoals ++ rightGoals ++ goals)
  trace[Arith] "new goals: {← Tactic.getUnsolvedGoals}"

elab "split_disj " n:ident : tactic => do
  Lean.Elab.Tactic.withMainContext do
  let decl ← Lean.Meta.getLocalDeclFromUserName n.getId
  let fvar := mkFVar decl.fvarId
  splitDisj fvar (fun _ => pure ()) (fun _ => pure ())

example (x y : Int) (h0 : x ≤ y ∨ x ≥ y) : x ≤ y ∨ x ≥ y := by
  split_disj h0
  . left; assumption
  . right; assumption

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

--syntax "int_tac_preprocess" : tactic

/- Boosting a bit the linarith tac.

   We do the following:
   - for all the assumptions of the shape `(x : Int) ≠ y` or `¬ (x = y), we
     introduce two goals with the assumptions `x < y` and `x > y`
     TODO: we could create a PR for mathlib.
 -/
def intTacPreprocess : Tactic.TacticM Unit := do
  Lean.Elab.Tactic.withMainContext do
  -- Lookup the instances of PropHasImp (this is how we detect assumptions
  -- of the proper shape), introduce assumptions in the context and split
  -- on those
  -- TODO: get rid of the assumption that we split
  let rec splitOnAsms (asms : List Expr) : Tactic.TacticM Unit :=
    match asms with
    | [] => pure ()
    | asm :: asms =>
      let k := splitOnAsms asms
      splitDisj asm k k
  -- Introduce
  let asms ← introInstances ``PropHasImp.concl lookupPropHasImp
  -- Split
  splitOnAsms asms.toList

elab "int_tac_preprocess" : tactic =>
  intTacPreprocess

example (x : Int) (h0: 0 ≤ x) (h1: x ≠ 0) : 0 < x := by
  int_tac_preprocess
  linarith
  linarith

syntax "int_tac" : tactic
macro_rules
  | `(tactic| int_tac) =>
    `(tactic|
      int_tac_preprocess <;>
      linarith)

example (x : Int) (h0: 0 ≤ x) (h1: x ≠ 0) : 0 < x := by int_tac

-- Checking that things append correctly when there are several disjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y := by
  int_tac_preprocess <;> apply And.intro <;> linarith

-- A tactic to solve linear arithmetic goals in the presence of scalars
syntax "scalar_tac" : tactic
macro_rules
  | `(tactic| scalar_tac) =>
    `(tactic|
      intro_has_prop_instances;
      have := Scalar.cMin_bound ScalarTy.Usize;
      have := Scalar.cMin_bound ScalarTy.Isize;
      have := Scalar.cMax_bound ScalarTy.Usize;
      have := Scalar.cMax_bound ScalarTy.Isize;
      -- TODO: not too sure about that
      simp only [*, Scalar.max, Scalar.min, Scalar.cMin, Scalar.cMax] at *;
      -- TODO: use int_tac
      linarith)

example (x y : U32) : x.val ≤ Scalar.max ScalarTy.U32 := by
  scalar_tac

example {a: Type} (v : Vec a) : v.val.length ≤ Scalar.max ScalarTy.Usize := by
  scalar_tac

end Arith
