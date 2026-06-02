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

  theorem WP_func_admissible (α β : Type) (arg) (post)
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

  elab "dspec_induction" func:ident : tactic => do
    let mut goal ← getMainGoal
    let ty ← goal.getType

    let func_expr ← Term.elabTerm func none

    -- do some wierd hacky nonsense to get `func.fixpoint_induct`
    let namee := func.getId.mkStr "fixpoint_induct"
    let fi_stx : Syntax ← `(term | $(mkIdent namee))
    let fixpoint_induct ← Term.elabTerm fi_stx none
    trace[UnfoldPF] "type of fixpoint_induct is {← inferType fixpoint_induct}"

    -- make a type family that abstracts over instances of func in the goal type
    let func_expr_ty ← inferType func_expr
    let fmvar ← Meta.mkFreshExprMVar (some func_expr_ty)
    let abs_goal_ty := ty.replace (fun x => if x == func_expr then some fmvar else none)
    let abs_goal_ty := abs_goal_ty.abstract #[fmvar]
    let abs_goal_ty := Expr.lam `func func_expr_ty abs_goal_ty .default

    trace[UnfoldPF] abs_goal_ty

    let fi_app := mkAppN fixpoint_induct #[abs_goal_ty]

    let [g_admissible, g_main] ← goal.apply fi_app
      | throwError "bla"


    -- prove the admissibility condition. this chunk of code is equivalent to the
    -- `prove_admissible` tactic above, but apparently calling that directly might cause problems
    let _ ← withTransparency .none <| do
      let onError {α} : TacticM α := throwError "failed to prove admissibility condition"
      let curry_admissible ← mkConstWithFreshMVarLevels `Aeneas.UnfoldPF.curry_admissible
      let admissible_pi ← mkConstWithFreshMVarLevels `Lean.Order.admissible_pi
      let WP_func_admissible ← mkConstWithFreshMVarLevels `Aeneas.UnfoldPF.WP_func_admissible
      let [g_admissible]
        ← repeat' (fun g => g.apply curry_admissible) [g_admissible] | onError
      let [g_admissible]
        ← repeat' (fun g => do
            let [g] ← (g.apply admissible_pi) | onError
            pure [(← g.intro1P).snd]
        ) [g_admissible] | onError
      let [] ← g_admissible.apply WP_func_admissible | onError

    replaceMainGoal [g_main]
    pure ()

  -- uncomment to see debug traces:
  -- set_option trace.UnfoldPF true

namespace Test

  open Std Result Aeneas.UnfoldPF

  def simple_diverge (x : Std.I32) : Result Std.I32 := do
    if x = 0#i32
    then ok 10#i32
    else
      let i1 ← 1#i32 + 1#i32
      simple_diverge i1
  partial_fixpoint

  -- this version demonstrates what the dspec_induction tactic does, just done manually
  theorem test_div_manual (x : Std.I32) : Std.WP.dspec (simple_diverge x) (fun res => res = 10#i32)
    := by
      revert x
      apply simple_diverge.fixpoint_induct
        (motive := fun simple_diverge => ∀ x, WP.dspec (simple_diverge x) (fun res => res = 10#i32))
      · prove_admissible
      · intros
        simp only
        split
        . simp [*]
        . step
          step
          simp [*]

  -- here, done automatically with the tactic
  theorem test_div_tactic (x : Std.I32) : Std.WP.dspec (simple_diverge x) (fun res => res = 10#i32)
    := by
      revert x
      dspec_induction simple_diverge
      intros
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

  theorem test_div_2_manual (x y : Std.I32) : Std.WP.dspec (simple_diverge_2 x y) (fun res => res = 10#i32)
    := by
      --
      revert x y
      apply simple_diverge_2.fixpoint_induct
        (motive := fun simple_diverge_2 => ∀ x y, WP.dspec (simple_diverge_2 x y) (fun res => res = 10#i32))
      · prove_admissible
      · intros
        simp only
        split
        . simp [*]
        . step
          step
          simp [*]
          --

  theorem test_div_2_tactic (x y : Std.I32) : Std.WP.dspec (simple_diverge_2 x y) (fun res => res = 10#i32)
    := by
      revert x y
      dspec_induction simple_diverge_2
      intros
      simp only
      split
      . simp [*]
      . step
        step
        simp [*]

end Test


end UnfoldPF
end Aeneas
