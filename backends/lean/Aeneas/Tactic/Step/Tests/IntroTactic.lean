import Aeneas.Tactic.Step

open Aeneas

/-!
# Tests for `SpecInfo.intro_tactic`
-/

namespace Aeneas.Tactic.Step.Tests.IntroTactic

abbrev Post (α : Type) := α → Prop

def Post.entails (P Q : Post α) : Prop := ∀ value, P value → Q value

theorem Post.entails_iff (P Q : Post α) :
    Post.entails P Q ↔ ∀ value, P value → Q value :=
  Iff.rfl

axiom TestM : Type → Type
axiom instMonadTestM : Monad TestM
attribute [instance] instMonadTestM

axiom triple (P : Prop) (m : TestM α) (Q : Post α) : Prop

/-- The precondition of a triple is a binder of the statement. `intro_tactic` is what turns one
into the other, for `step` to introduce and name it. -/
axiom triple_pull {P : Prop} {m : TestM α} {Q : Post α} :
    triple P m Q ↔ (P → triple True m Q)

theorem and_imp_iff (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) := by
  constructor
  · intro h hP hQ
    exact h ⟨hP, hQ⟩
  · intro h hPQ
    exact h hPQ.1 hPQ.2

syntax "pull_pre" : tactic

macro_rules
  | `(tactic| pull_pre) => `(tactic| try (rw [triple_pull]; try rw [and_imp_iff]))

axiom triple_step_mono {P Pm : Prop} {Q : Post α}
    (m : TestM α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (hPost : Post.entails Qm Q) :
    triple P m Q

/-- The continuation inherits the postcondition of the stepped call as its precondition. -/
axiom triple_step_bind {P Pm : Prop} {next : α → TestM β} {Q : Post β}
    (m : TestM α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (hNext : ∀ value, triple (Qm value) (next value) Q) :
    triple P (m >>= next) Q

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    qimp_elim_tactics := #[``Post.entails_iff, ``true_imp_iff]
    intro_tactic := SpecInfo.tac `(tactic| pull_pre)
    to_mvcgen := none
    liftings := #[]
  }

axiom solvingTriple (P : Prop) (m : TestM α) (Q : Post α) : Prop

axiom solvingTriple_step_mono {P Pm : Prop} {Q : Post α}
    (m : TestM α) (Qm : Post α) (hStep : solvingTriple Pm m Qm)
    (hPre : P → Pm)
    (hPost : Post.entails Qm Q) :
    solvingTriple P m Q

axiom introGoal : Prop
axiom introGoal_proof : introGoal

axiom solvingTriple_step_bind {P Pm : Prop} {next : α → TestM β} {Q : Post β}
    (m : TestM α) (Qm : Post α) (hStep : solvingTriple Pm m Qm)
    (hPre : P → Pm)
    (hNext : ∀ _value : α, introGoal) :
    solvingTriple P (m >>= next) Q

#register_spec_info {
    spec_name := ``solvingTriple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``solvingTriple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``solvingTriple_step_bind
    mk_spec_bind_skip_args := 6
    qimp_elim_tactics := #[``Post.entails_iff, ``true_imp_iff]
    intro_tactic := SpecInfo.tac `(tactic| exact introGoal_proof)
    to_mvcgen := none
    liftings := #[]
  }

axiom incr (value : Nat) : TestM Nat

@[step]
axiom incr_spec (value : Nat) :
    triple True (incr value) (fun result => result = value + 1)

axiom solvingIncr_spec (value : Nat) :
    solvingTriple True (incr value) (fun result => result = value + 1)

noncomputable def incrTwice (value : Nat) : TestM Nat := do
  let once ← incr value
  incr once

/- The registered `intro_tactic` proves the bind continuation, so `step` closes the goal. -/
example (value : Nat) :
    solvingTriple True (incrTwice value) (fun result => result = value + 2) := by
  unfold incrTwice
  step with solvingIncr_spec

/- `intro_tactic` pulls the precondition of the continuation out of the triple, so that `step`
introduces it and gives it the name provided for it. -/
/--
trace: case hNext
value once : ℕ
hOnce : once = value + 1
⊢ triple True (incr once) fun result => result = value + 1 + 1
-/
#guard_msgs in
set_option pp.mvars false in
example (value : Nat) :
    triple True (incrTwice value) (fun result => result = value + 1 + 1) := by
  unfold incrTwice
  step as ⟨ once, hOnce ⟩
  trace_state
  guard_hyp hOnce : once = value + 1
  step*

axiom incrWithFacts (value : Nat) : TestM Nat

@[step]
axiom incrWithFacts_spec (value : Nat) :
    triple True (incrWithFacts value)
      (fun result => result = value + 1 ∧ value < result)

noncomputable def incrWithFactsThenIncr (value : Nat) : TestM Nat := do
  let once ← incrWithFacts value
  incr once

/- `step as` names the result and every hypothesis exposed by `intro_tactic`. -/
example (value : Nat) :
    triple True (incrWithFactsThenIncr value) (fun result => result = value + 1 + 1) := by
  unfold incrWithFactsThenIncr
  step as ⟨ once, hOnce, hGreater ⟩
  guard_hyp hOnce : once = value + 1
  guard_hyp hGreater : value < once
  step*

elab "run_constructor_under_binders" : tactic => do
  Step.runTacUnderBinders (← `(tactic| constructor))

/- An intro tactic is a preprocessing step and must not branch. -/
/--
error: `intro_tactic` must not create multiple goals
-/
#guard_msgs in
example (P Q : Prop) : P → Q → P ∧ Q := by
  run_constructor_under_binders

elab "run_assumption_under_binders" : tactic => do
  Step.runTacUnderBinders (← `(tactic| assumption))

/- An intro tactic may solve the goal after its leading binders are introduced. -/
example (P : Prop) : P → P := by
  run_assumption_under_binders

end Aeneas.Tactic.Step.Tests.IntroTactic
