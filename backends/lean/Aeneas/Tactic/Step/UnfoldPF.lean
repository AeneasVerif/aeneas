import Lean
import Aeneas.Tactic.Solver.ScalarTac
import Aeneas.Tactic.Step.Init
import Aeneas.Tactic.Step.GrindState
import Aeneas.Std
import Aeneas.Tactic.Simp.SimpLemmas
import AeneasMeta.Async
import Aeneas.Tactic.Solver.Grind.Init
import Aeneas.Tactic.Step.InferPost
import Aeneas.Tactic.Step

-- tactic for unfolding partial_fixpoint definitions with fixpoint_induct
-- normally you would use the normal unfold tactic, but that requires the proof to be terminating

namespace Aeneas

namespace UnfoldPF

open Lean Elab Term Meta Tactic
open Utils
open Lean.Order
open Std Result


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
    simp at h
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
      ·
        intros h
        rcases h with ⟨f, a, b⟩
        exists (fun p => f p.fst p.snd)
        --
      --
    simp [lemma1] at h
    simp only [↓existsAndEq, and_true] at *
    apply h

  theorem WP_func_admissible (α β) (arg) (post)
    : Order.admissible fun (f : α → Result β) => WP.dspec (f arg) post := by
    apply Lean.Order.admissible_apply (fun _ fx => WP.dspec fx _)
    apply Lean.Order.admissible_flatOrder
    simp only [WP.dspec]

  macro "prove_admissible" : tactic =>
    `(tactic| (
        (repeat' apply curry_admissible)
        (repeat' (apply Lean.Order.admissible_pi ; intro))
        (apply WP_func_admissible)
    )
    )

  elab "unfold_div_old" : tactic => do
    let mut goal ← getMainGoal
    let ty ← goal.getType

    let (thHead, thArgs) := ty.consumeMData.withApp (fun f args => (f, args))
    -- TODO: here is where it should be able to lift from spec to dspec
    if !thHead.isConst || thHead.constName! != ``Std.WP.dspec then
      throwError "Not dspec statement"
    -- let .app WP.dspec a b := ty
    let (func, funcargs) := thArgs[1]!.consumeMData.withApp (fun f args => (f, args))
    if !func.isConst then
      throwError "Can only unfold (dspec (func... ) post) when func is a constant"

    let post := thArgs[2]!
    -- the goal is now split into (dspec (func ..funcargs) post)

    -- let mut vars : Array FVarId := #[]

    -- should we automatically revert variables? could this ever cause a problem?
    -- -- first, we need to revert free variables that are arguments to the function
    -- for arg in funcargs do
    --   -- TODO: maybe its not always a free var, what cases need to be handled here?
    --   let var := arg.fvarId!
    --   vars := vars.push var
    --   (_, goal) ← goal.revert #[var]


    -- do some wierd hacky nonsense to get `func.fixpoint_induct`
    let namee := func.constName!.mkStr "fixpoint_induct"
    let fi_stx : Syntax ← `(term | $(mkIdent namee))
    let fixpoint_induct ← Term.elabTerm fi_stx none
    trace[UnfoldPF] "type of fixpoint_induct is {← inferType fixpoint_induct}"

    -- apply fixpoint_induct
    let fi_app := mkAppN fixpoint_induct #[
      .lam `func (← inferType func)
      (mkAppN (.bvar 0) #[])
      .default
    ]

    replaceMainGoal [goal]
    pure ()

  -- this new version doesn't try to revert the variables, and is more general.
  -- but it requires that you give it the name of the thing to induct over
  elab "fixpoint_induction" func:ident : tactic => do
    let mut goal ← getMainGoal
    let ty ← goal.getType

    let func_expr ← Term.elabTerm func none

    -- do some wierd hacky nonsense to get `func.fixpoint_induct`
    let namee := func.getId.mkStr "fixpoint_induct"
    let fi_stx : Syntax ← `(term | $(mkIdent namee))
    let fixpoint_induct ← Term.elabTerm fi_stx none
    trace[UnfoldPF] "type of fixpoint_induct is {← inferType fixpoint_induct}"
    -- apply fixpoint_induct

    -- make a type family that abstracts over instances of func in the goal type
    let abs_goal_ty := ty.abstract #[func_expr]

    let fi_app := mkAppN fixpoint_induct #[.lam `func (← inferType func_expr)
      (abs_goal_ty.instantiate1 (.bvar 0)) .default
    ]

    let [g1, g2] ← goal.apply fi_app
      | throwError "bla"

    setGoals [g1]
    evalTactic (← `(tactic|prove_admissible))

    replaceMainGoal [g2]
    pure ()

  set_option trace.UnfoldPF true
  -- #check simple_diverge.fixpoint_induct

  theorem test_div_2 (x : Std.I32) : Std.WP.dspec (simple_diverge x) (fun res => res = 10#i32)
    := by
    unfold_div
    --
    sorry

namespace Test

  open Std Result Aeneas.UnfoldPF
  def simple_diverge (x : Std.I32) : Result Std.I32 := do
    if x = 0#i32
    then ok 10#i32
    else
      let i1 ← 1#i32 + 1#i32
      simple_diverge i1
  partial_fixpoint

  theorem test_div2 (x : Std.I32) : Std.WP.dspec (simple_diverge x) (fun res => res = 10#i32)
    := by
      unfold simple_diverge
      --
      sorry

  -- TODO: if i use unfold then sorry, print proof term, i can see how it proves admissibility
  #check simple_diverge.fixpoint_induct
  @[step]
  theorem test_div (x : Std.I32) : Std.WP.dspec (simple_diverge x) (fun res => res = 10#i32)
    := by
      --
      revert x
      apply simple_diverge.fixpoint_induct
        (motive := fun simple_diverge => ∀ x, WP.dspec (simple_diverge x) (fun res => res = 10#i32))
      · apply Lean.Order.admissible_pi
        intros y
        apply Lean.Order.admissible_apply (fun _ fx => WP.dspec fx _)
        apply Lean.Order.admissible_flatOrder
        simp only [WP.dspec]
      · intros
        simp only
        split
        . simp [*]
        . step
          step
          simp [*]

  theorem test_div_no_revert (x : Std.I32) : Std.WP.dspec (simple_diverge x) (fun res => res = 10#i32)
    := by
      --
      apply simple_diverge.fixpoint_induct
        (motive := fun simple_diverge => ∀ x, WP.dspec (simple_diverge x) (fun res => res = 10#i32))
      · apply Lean.Order.admissible_pi
        intros y
        apply Lean.Order.admissible_apply (fun _ fx => WP.dspec fx _)
        apply Lean.Order.admissible_flatOrder
        simp only [WP.dspec]
        --
      · intros
        simp only
        split
        . simp [*]
        . step
          step
          simp [*]

  theorem test_div_no_revert_no_all (x : Std.I32) : Std.WP.dspec (simple_diverge x) (fun res => res = 10#i32)
    := by
      --
      apply simple_diverge.fixpoint_induct
        (motive := fun simple_diverge => WP.dspec (simple_diverge x) (fun res => res = 10#i32))
      · apply Lean.Order.admissible_apply (fun _ fx => WP.dspec fx _)
        apply Lean.Order.admissible_flatOrder
        simp only [WP.dspec]
      · intros
        simp only
        split
        . simp [*]
        . step
          step
          simp [*]
  def simple_diverge_2 (x y : Std.I32) : Result Std.I32 := do
    if x = y#i32
    then ok 10#i32
    else
      let i1 ← 1#i32 + 1#i32
      let i2 ← 1#i32 + 1#i32
      simple_diverge_2 i1 i2
  partial_fixpoint

  def admissible_apply_simpler {α : Sort u}{β : Sort v} [CCPO β] (P : β → Prop) (x : α)
    (hadm : admissible P) : admissible (fun (f : α → β) => P (f x)) := by
    apply admissible_apply (fun _ => P) x
    assumption

  theorem test_add_2 (a1 a2 β) (post)
    : Order.admissible fun (f : a1 → a2 → Result β) => ∀ (x : a1) (y : a2), WP.dspec (f x y) post := by
    apply Lean.Order.admissible_pi
    intros y1
    apply Lean.Order.admissible_pi
    intros y2
    --
    apply admissible_apply_simpler (β := a2 → Result β) (fun fx => WP.dspec (fx y2) post) y1
    -- apply Lean.Order.admissible_apply (β := fun _ => a2 → Result β)
      -- (fun x fx => WP.dspec (fx y2) post) y1
    apply Lean.Order.admissible_apply (fun _ fx => WP.dspec fx _)
    apply Lean.Order.admissible_flatOrder
    simp only [WP.dspec]

  theorem test_div_2 (x y : Std.I32) : Std.WP.dspec (simple_diverge_2 x y) (fun res => res = 10#i32)
    := by
      --
      revert x y
      apply simple_diverge_2.fixpoint_induct
        (motive := fun simple_diverge_2 => ∀ x y, WP.dspec (simple_diverge_2 x y) (fun res => res = 10#i32))
      ·
        -- apply test_add_2
        prove_admissible
        --
      · intros
        simp only
        split
        . simp [*]
        . step
          step
          simp [*]
          --
end Test


end UnfoldPF
end Aeneas
