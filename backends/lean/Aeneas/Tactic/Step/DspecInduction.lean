import Lean
import Mathlib.Tactic.Simproc.ExistsAndEq
import AeneasMeta.Utils
import AeneasMeta.Extensions
import Aeneas.Tactic.Step.Trace

/- Tactic for unfolding partial_fixpoint definitions with fixpoint_induct.
   Normally you would use the normal unfold tactic, but that requires the proof to be terminating.
   Instead, you need to use the .fixpoint_induct theorem that is automatically created by lean.
   However, this requires a bunch of boilerplate that can be automated in the case that
   the conclusion is a dspec theorem about a function call.
   In particular, the statement needs to be proven to be admissible.

   See the examples below to see what the tactic does
   and the manual examples show what the tactic is doing written out directly. -/


namespace Aeneas

namespace DspecInduction

open Lean Elab Term Meta Tactic
open Utils
open Lean.Order

/-! ## The `dspec_admissible` attribute -/
initialize dspecAdmissibleExt : SimplePersistentEnvExtension Name NameSet ←
  Extensions.mkSetDeclarationExtension `dspecAdmissibleMap

initialize dspecAdmissibleAttr : AttributeImpl ← do
  let attrImpl : AttributeImpl := {
    name := `dspec_admissible
    descr := "Registers a theorem used by `dspec_induction` to discharge the \
              admissibility side-goal it generates. Such a theorem must have the shape \
              `Order.admissible fun f => <judgment> (f arg)`, for instance \
              `Order.admissible fun (f : ι → Result α) => WP.dspec (f arg) post`."
    add := fun declName stx _ => do
      Attribute.Builtin.ensureNoArgs stx
      modifyEnv fun env => dspecAdmissibleExt.addEntry env declName
    erase := fun declName => do
      modifyEnv fun env =>
        dspecAdmissibleExt.modifyState env fun s => s.erase declName
  }
  registerBuiltinAttribute attrImpl
  pure attrImpl

/-- Get the theorems registered with the `dspec_admissible` attribute. -/
def getAdmissibleThms [Monad m] [MonadEnv m] : m (List Name) := do
  pure (dspecAdmissibleExt.getState (← getEnv)).toList

theorem curry_admissible (a1 a2 a3) (P : (a1 → a2 → a3) → Prop) [CCPO a3]
  (h : Order.admissible fun (f : (a1 × a2) → a3) => P (fun x y => f (x, y)))
  : Order.admissible fun (f : a1 → a2 → a3) => P f := by
  intros c hchain hc
  simp only at hc
  unfold admissible at h
  simp only at h
  have h := h (fun f => c (fun x y => f (x, y))) (
    by
      unfold chain
      unfold chain at hchain
      intros s1 s2 cs1 cs2
      have thing := hchain (fun x y => s1 (x, y)) (fun x y => s2 (x, y)) cs1 cs2
      unfold PartialOrder.rel
      unfold instCCPOPi
      simp only
      unfold instOrderPi
      simp only
      cases thing with
      | inl thing =>
          apply Or.inl
          intros
          apply thing
      | inr thing =>
        apply Or.inr
        intros
        apply thing
  ) ( by
    intros f
    apply hc
  )
  --
  rw [← Order.fun_csup_eq]
  unfold fun_csup
  simp only
  --
  simp only [← Order.fun_csup_eq]
  unfold fun_csup
  simp only
  --
  simp only [← Order.fun_csup_eq] at h
  unfold fun_csup at h
  simp only at h
  --
  have lemma1 (x : a1) (y : a2)
    : (fun z => ∃ (f : a1 × a2 → a3), (c fun x y => f (x, y)) ∧ f (x, y) = z)
      = (fun z => ∃ f, (∃ f_1, c f_1 ∧ f_1 x = f) ∧ f y = z) := by
    simp
    funext z
    simp only [eq_iff_iff]
    apply Iff.intro
    · intros h
      rcases h with ⟨f, a, b⟩
      exists (fun x y => f (x, y))
    · intros h
      rcases h with ⟨f, a, b⟩
      exists (fun p => f p.fst p.snd)
  --
  simp [lemma1] at h
  simp only [↓existsAndEq, and_true] at *
  apply h

/-- Close `g` by applying one of the theorems registered with the `dspec_admissible`
attribute. -/
private partial def applyAdmissibleThm (g : MVarId) (thms : List Name) : TacticM Unit := do
  match thms with
  | [] =>
    throwError "failed to prove admissibility condition: none of the theorems registered \
                with the `dspec_admissible` attribute applies to \
                {← instantiateMVars (← g.getType)}"
  | thm :: thms => do
    let s ← saveState
    try
      let [] ← g.apply (← mkConstWithFreshMVarLevels thm) | failure
    catch _ =>
      s.restore
      applyAdmissibleThm g thms

def getParamNames (ty : Expr) : MetaM (Array Name) := do
  forallTelescope ty fun xs _ => do
    xs.mapM fun x => do
      let localDecl ← x.fvarId!.getDecl
      return localDecl.userName

-- given a function type, return list of input types
def getInputTypes (ty : Expr) : List Expr :=
  match ty with
  | .forallE _ ty body _ => .cons ty (getInputTypes body)
  | _ => []

elab "dspec_induction" func:ident : tactic => do
  let mut goal ← getMainGoal
  let goalTy ← goal.getType

  let func_expr ← Term.elabTerm func none
  let func_expr := func_expr.getAppFn
  let func_expr_name := func_expr.constName!

  let func_name ← resolveGlobalConstNoOverload func
  let fi_name := func_name ++ `fixpoint_induct
  executeReservedNameAction fi_name -- see https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/.60.2Efixpoint_induct.60.20doesn.27t.20exist.20in.20environment.20until.20used.3F/with/602621282
  let fixpoint_induct ← Meta.mkConstWithFreshMVarLevels fi_name

  -- sadly, there are many possible forms that fixpoint_induct can take.
  -- we need to reverse engineer which form it is by looking at its type.
  -- see the examples at the end of this file, it depends on which parameters to the
  -- original function are unchanged in recursive calls.
  let func_params ← getParamNames (← inferType func_expr)
  let fixpoint_induct_params ← getParamNames (← inferType fixpoint_induct)
  -- the last 3 parameters are the motive, admissibility, and proof of induction
  let fixpoint_induct_params := fixpoint_induct_params.extract 0 (fixpoint_induct_params.size - 3)
  -- which params are constant, these are treated specially by fixpoint_induct
  let constant_params := func_params.map (fun x => fixpoint_induct_params.contains x)
  trace[DspecInduction] "constant_params: {constant_params}"
  let .some func_application := goalTy.find? (fun e => e.getAppFn.isConstOf func_expr_name)
  | throwError "{func} not found in goal"
  trace[DspecInduction] "func app in goal is: {func_application}"
  let args_in_goal := func_application.getAppArgs
  let const_args := (args_in_goal.zip constant_params).filterMap
    fun (x, b) => if b then some x else none
  let nonconst_args := (args_in_goal.zip constant_params).filterMap
    fun (x, b) => if b then none else some x
  trace[DspecInduction] "const_args: {const_args}"

  -- make a type family that abstracts over instances of func in the goal type
  -- first, we need to find out what type the motive expects, by inspecting the theorem
  -- this should be something that inputs all of the nonconst_args
  let applied_fixpoint_induct_type ← inferType (mkAppN fixpoint_induct const_args)
  let applied_func_type := (getInputTypes (getInputTypes applied_fixpoint_induct_type).getLast!)[0]!
  let fmvar ← Meta.mkFreshExprMVar (some applied_func_type)
  let value_to_replace_in_motive := mkAppN fmvar nonconst_args
  let abs_goal_ty := goalTy.replace
    (fun x => if x.getAppFn.isConstOf func_expr_name then some value_to_replace_in_motive else none)
  let abs_goal_ty := abs_goal_ty.abstract #[fmvar]
  let abs_goal_ty := Expr.lam `func applied_func_type abs_goal_ty .default

  trace[DspecInduction] "fixpoint_induct with motive: {abs_goal_ty}"

  let fi_app := mkAppN fixpoint_induct (const_args ++ #[abs_goal_ty])

  trace[DspecInduction] "going to apply {fi_app}"
  trace[DspecInduction] "of type : {← inferType fi_app}"

  let [g_admissible, g_main] ← goal.apply fi_app | throwError "this shouldn't happen 1"

  -- Prove the admissibility condition
  let _ ← withTransparency .default <| do -- using a more restricted reducibility doesn't work on some tests below
    let onError {α} : TacticM α := throwError "failed to prove admissibility condition"
    let curry_admissible ← mkConstWithFreshMVarLevels `Aeneas.DspecInduction.curry_admissible
    let admissible_pi ← mkConstWithFreshMVarLevels `Lean.Order.admissible_pi
    let admissibleThms ← getAdmissibleThms
    let [g_admissible]
      ← repeat' (fun g => g.apply curry_admissible) [g_admissible] | onError
    let [g_admissible]
      ← repeat' (fun g => do
          let [g] ← (g.apply admissible_pi) | onError
          pure [(← g.intro1P).snd]
      ) [g_admissible] | onError
    applyAdmissibleThm g_admissible admissibleThms

  replaceMainGoal [g_main]
  pure ()

-- uncomment to see debug traces:
-- set_option trace.DspecInduction true

end DspecInduction
end Aeneas
