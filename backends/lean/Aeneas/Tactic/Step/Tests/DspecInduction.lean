module
public import Lean
public import Aeneas.Tactic.Step.DspecInduction
import Aeneas.Tactic.Step.Step
import Aeneas.Tactic.Solver.ScalarTac
import Aeneas.Std

/-! # Tests for `dspec_induction` -/

namespace Aeneas

namespace DspecInduction

namespace Test

open Std Result Aeneas.Step

def simple_diverge (x : Std.I32) : Result Std.I32 := do
  if x = 0#i32
  then ok 10#i32
  else
    let i1 ← 1#i32 + 1#i32
    simple_diverge i1
partial_fixpoint

macro "prove_admissible" : tactic =>
  `(tactic| (
      (repeat' apply curry_admissible)
      (repeat' (apply Lean.Order.admissible_pi ; intro))
      (apply WP.dspec_func_admissible)
  )
  )

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

def pseudo_random_loop.body
  (state : Std.U32) : Result (ControlFlow Std.U32 Std.U32) := do
  if state < 100#u32
  then let state1 ← dummy_hash state
       ok (cont state1)
  else ok (done state)

def pseudo_random_loop (state : Std.U32) : Result Std.U32 := do
  loop
    (fun state1 => pseudo_random_loop.body state1)
    state

@[reducible] def pseudo_random : Result Std.U32 := do
  pseudo_random_loop 0#u32


theorem pseudo_random_spec :
  pseudo_random ⦃fun x => x.val >= 100⦄div := by
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
  · simp [*]
    unfold dummy_hash
    simp
    -- here we treat `dummy_hash` as opaque and use `step`
    step
    grind
  · simp [*]
    grind

-- these two examples demonstrate how .fixpoint_induct theorems can take various forms.
def first_arg_const (x y : Nat) : Result Nat :=
  if x = 0 then .ok 0
  else first_arg_const x (y + 1)
partial_fixpoint

def second_arg_const (x y : Nat) : Result Nat :=
  if y = 0 then .ok 0
  else second_arg_const (x + 1) y
partial_fixpoint

-- note how the two induction principles differ:
/--
info: Aeneas.DspecInduction.Test.first_arg_const.fixpoint_induct (x : ℕ) (motive : (ℕ → Result ℕ) → Prop)
  (adm : Lean.Order.admissible motive)
  (h :
    ∀ (first_arg_const : ℕ → Result ℕ),
      motive first_arg_const → motive fun y => if x = 0 then ok 0 else first_arg_const (y + 1)) :
  motive (first_arg_const x)
-/
#guard_msgs in
#check first_arg_const.fixpoint_induct

/--
info: Aeneas.DspecInduction.Test.second_arg_const.fixpoint_induct (y : ℕ) (motive : (ℕ → Result ℕ) → Prop)
  (adm : Lean.Order.admissible motive)
  (h :
    ∀ (second_arg_const : ℕ → Result ℕ),
      motive second_arg_const → motive fun x => if y = 0 then ok 0 else second_arg_const (x + 1)) :
  motive fun x => second_arg_const x y
-/
#guard_msgs in
#check second_arg_const.fixpoint_induct

example x y : (first_arg_const x y) ⦃fun x => x = 0⦄div := by
  revert y
  dspec_induction first_arg_const
  intros first_arg_const' ih y
  split
  · simp
  · apply ih

example x y : (second_arg_const x y) ⦃fun x => x = 0⦄div := by
  revert x
  dspec_induction second_arg_const
  intros second_arg_const' ih y
  split
  · simp
  · apply ih

-- the admissibility theorems are looked up by the shape of the admissibility goal
open Lean Elab Term in
elab "#admissible_thms " t:term : command => Command.liftTermElabM do
  let ty ← elabTermAndSynthesize t none
  logInfo m!"{← getAdmissibleThms ty}"

/-- info: [Aeneas.Std.WP.dspec_func_admissible] -/
#guard_msgs in
#admissible_thms Lean.Order.admissible (fun f : Nat → Result Nat => WP.dspec (f 0) (fun _ => True))

-- the key is `WP.dspec ?e ?post`: the argument of `WP.dspec` is not inspected
/-- info: [Aeneas.Std.WP.dspec_func_admissible] -/
#guard_msgs in
#admissible_thms Lean.Order.admissible (fun _ : Nat → Result Nat => WP.dspec (.ok 0) (fun _ => True))

/-- info: [] -/
#guard_msgs in
#admissible_thms Lean.Order.admissible (fun _ : Nat → Result Nat => True)

end Test

end DspecInduction

end Aeneas
