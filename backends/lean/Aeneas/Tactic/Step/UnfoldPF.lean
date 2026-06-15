import Lean
import Aeneas.Tactic.Solver.ScalarTac
import Aeneas.Tactic.Step.Init
import Aeneas.Tactic.Step.GrindState
import Aeneas.Std
import Aeneas.Tactic.Simp.SimpLemmas
import AeneasMeta.Async
import Aeneas.Tactic.Solver.Grind.Init
import Aeneas.Tactic.Step.InferPost
import Aeneas.Tactic.Step.Step

-- tactic for unfolding partial_fixpoint definitions with fixpoint_induct
-- normally you would use the normal unfold tactic, but that requires the proof to be terminating
-- instead, you need to use the .fixpoint_induct theorem that is automatically created by lean
-- however, this requires a bunch of boilerplate that can be automated in the case that
-- the conclusion is a dspec theorem about a function call.
-- in particular, the statement needs to be proven to be admissible.
-- see the examples below to see what the tactic does
-- and the manual examples show what the tactic is doing written out directly

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
    · intros h
      rcases h with ⟨f, a, b⟩
      exists (fun p => f p.fst p.snd)
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

  -- do some wierd hacky nonsense to get `func.fixpoint_induct`.
  -- more obvious methods fail, presumably due to buggy lean behavior
  let namee := func.getId.mkStr "fixpoint_induct"
  let fi_stx : Syntax ← `(term | $(mkIdent namee))
  let fixpoint_induct ← Term.elabTerm fi_stx none
  let fixpoint_induct := fixpoint_induct.getAppFn
  trace[UnfoldPF] "type of fixpoint_induct is {← inferType fixpoint_induct}"

  -- sadly, there are many possible forms that fixpoint_induct can take.
  -- we need to reverse engineer which form it is by looking at its type.
  -- see the examples at the end of this file, it depends on which parameters to the
  -- original function are unchanged in recursive calls. {
  let func_params ← getParamNames (← inferType func_expr)
  let fixpoint_induct_params ← getParamNames (← inferType fixpoint_induct)
  -- the last 3 parameters are the motive, admissibility, and proof of induction
  let fixpoint_induct_params := fixpoint_induct_params.extract 0 (fixpoint_induct_params.size - 3)
  -- which params are constant, these are treated specially by fixpoint_induct
  let constant_params := func_params.map (fun x => fixpoint_induct_params.contains x)
  trace[UnfoldPF] "constant_params: {constant_params}"
  let .some func_application := goalTy.find? (fun e => e.getAppFn.isConstOf func_expr_name)
  | throwError "{func} not found in goal"
  trace[UnfoldPF] "func app in goal is: {func_application}"
  let args_in_goal := func_application.getAppArgs
  let const_args := (args_in_goal.zip constant_params).filterMap
    fun (x, b) => if b then some x else none
  let nonconst_args := (args_in_goal.zip constant_params).filterMap
    fun (x, b) => if b then none else some x
  trace[UnfoldPF] "const_args: {const_args}"
  -- }

  -- make a type family that abstracts over instances of func in the goal type
  -- first, we need to find out what type the motive expects, by inspecting the theorem
  -- this should be something that inputs all of the nonconst_args
  let applied_fixpoint_induct_type ← inferType (mkAppN fixpoint_induct const_args)
  let applied_func_type := (getInputTypes (getInputTypes applied_fixpoint_induct_type).getLast!)[0]!
  -- let applied_func_type ← inferType func_expr
  let fmvar ← Meta.mkFreshExprMVar (some applied_func_type)
  let value_to_replace_in_motive := mkAppN fmvar nonconst_args
  let abs_goal_ty := goalTy.replace
    (fun x => if x.getAppFn.isConstOf func_expr_name then some value_to_replace_in_motive else none)
  let abs_goal_ty := abs_goal_ty.abstract #[fmvar]
  let abs_goal_ty := Expr.lam `func applied_func_type abs_goal_ty .default

  trace[UnfoldPF] "fixpoint_induct with motive: {abs_goal_ty}"

  let fi_app := mkAppN fixpoint_induct (const_args ++ #[abs_goal_ty])

  trace[UnfoldPF] "going to apply {fi_app}"
  trace[UnfoldPF] "of type : {← inferType fi_app}"

  let [g_admissible, g_main] ← goal.apply fi_app | throwError "this shouldn't happen 1"

  -- prove the admissibility condition. this chunk of code is equivalent to the
  -- `prove_admissible` tactic above, but apparently calling that directly might cause problems
  let _ ← withTransparency .default <| do -- using a more restricted reducibility doesn't work on some tests below
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

open Std Result Aeneas.Step

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

def simple_diverge_2' (x y : Std.I32) : Result Std.I32 := do
  if x = y#i32
  then ok 10#i32
  else
    let i1 ← 1#i32 + 1#i32
    let i2 ← 1#i32 + 1#i32
    simple_diverge_2' i1 i2
partial_fixpoint

theorem test_div_2_manual (x y : Std.I32) : Std.WP.dspec (simple_diverge_2' x y) (fun res => res = 10#i32)
  := by
    --
    revert x y
    apply simple_diverge_2'.fixpoint_induct
      (motive := fun simple_diverge_2' => ∀ x y, WP.dspec (simple_diverge_2' x y) (fun res => res = 10#i32))
    · prove_admissible
    · intros
      simp only
      split
      . simp [*]
      . step
        step
        simp [*]
        --

theorem test_div_2_tactic (x y : Std.I32) : Std.WP.dspec (simple_diverge_2' x y) (fun res => res = 10#i32)
  := by
    revert x y
    dspec_induction simple_diverge_2'
    intros
    simp only
    split
    . simp [*]
    . step
      step
      simp [*]


def dummy_hash (_i : Std.U32) : Result Std.U32 := do
  ok 1000#u32

open ControlFlow

/-- [tutorial::pseudo_random]: loop body 0:
    Source: 'src/lib.rs', lines 258:2-260:3
    Visibility: public -/
def pseudo_random_loop.body
  (state : Std.U32) : Result (ControlFlow Std.U32 Std.U32) := do
  if state < 100#u32
  then let state1 ← dummy_hash state
       ok (cont state1)
  else ok (done state)

/-- [tutorial::pseudo_random]: loop 0:
    Source: 'src/lib.rs', lines 258:2-260:3
    Visibility: public -/
def pseudo_random_loop (state : Std.U32) : Result Std.U32 := do
  loop
    (fun state1 => pseudo_random_loop.body state1)
    state

/-- [tutorial::pseudo_random]:
    Source: 'src/lib.rs', lines 255:0-262:1
    Visibility: public -/
@[reducible] def pseudo_random : Result Std.U32 := do
               pseudo_random_loop 0#u32


theorem pseudo_random_spec :
  pseudo_random div⦃fun x => x.val >= 100⦄ := by
  unfold pseudo_random
  unfold pseudo_random_loop
  -- note here that we must make a potentially non-obvious decision about
  -- what to generalize and how to do the induction
  generalize 0#u32 = x
  revert x
  dspec_induction loop
  intros loop' ih x
  simp only
  unfold pseudo_random_loop.body
  simp
  by_cases ((↑x : Nat) < 100)
  ·
    simp [*]
    unfold dummy_hash
    simp
    -- note that here, i am refraining from using the result of dummy_hash,
    -- since its supposed to represent a hash function where we can't predict the result,
    -- but it actually is just a constant
    step
    grind
  ·
    simp [*]
    grind

-- these two examples demonstrate how .fixpoint_induct theorems can take various forms.
def first_arg_const (x y : Nat) : Option Nat :=
  if x = 0 then Option.some 0
  else first_arg_const x (y + 1)
partial_fixpoint

def second_arg_const (x y : Nat) : Option Nat :=
  if y = 0 then Option.some 0
  else second_arg_const (x + 1) y
partial_fixpoint


end Test

end UnfoldPF
end Aeneas
