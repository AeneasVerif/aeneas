module
import Aeneas.Tactic.Step
public meta import Lean
public meta import Aeneas.Tactic.Step

open Aeneas

/-!
# Tests for `SpecInfo.prepare_intro_outputs`

The fixture is irreducible so that the tests depend on defining a `prepare_intro_outputs` tactic.
-/

namespace Aeneas.Tactic.Step.Tests.IntroTactic

abbrev Post (α : Type) := α → Prop

def Post.entails (P Q : Post α) : Prop := ∀ value, P value → Q value

theorem Post.entails_iff (P Q : Post α) :
    Post.entails P Q ↔ ∀ value, P value → Q value :=
  Iff.rfl

def triple (P : Prop) (m : Id α) (Q : Post α) : Prop :=
  P → Q m

theorem triple_step_mono {P Pm : Prop} {Q : Post α}
    (m : Id α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (hPost : Post.entails Qm Q) :
    triple P m Q := by
  intro hP
  exact hPost m (hStep (hPre hP))

theorem triple_step_bind {P Pm : Prop} {next : α → Id β} {Q : Post β}
    (m : Id α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (hNext : ∀ value, triple (Qm value) (next value) Q) :
    triple P (m >>= next) Q := by
  intro hP
  exact hNext m (hStep (hPre hP))

theorem triple_pull {P : Prop} {m : Id α} {Q : Post α} :
    triple P m Q ↔ (P → triple True m Q) := by
  constructor
  · intro h hP _
    exact h hP
  · intro h hP
    exact h hP True.intro

theorem triple_true (P : Prop) (m : Id α) :
    triple P m (fun _ => True) := by
  intro _
  trivial

syntax (name := pullPre) "pull_pre" : tactic
macro_rules
  | `(tactic| pull_pre) =>
    `(tactic|
        first
        | rw [Post.entails_iff]
        | (intro value
           first
           | exact triple_true _ _
           | (rw [triple_pull]; (try rw [and_imp]); revert value)))

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    prepare_intro_outputs := some ``pullPre
    to_mvcgen := none
    liftings := #[]
  }

/-! ### Programs and tests -/

@[irreducible] def incr (value : Nat) : Id Nat :=
  value + 1

@[step]
theorem incr_spec (value : Nat) :
    triple True (incr value) (fun result => result = value + 1) := by
  unfold incr
  intro _
  rfl

attribute [irreducible] triple

@[irreducible] def incrTwice (value : Nat) : Id Nat := do
  let once ← incr value
  incr once

/- `step as` names the result and the hypothesis exposed by `prepare_intro_outputs`. -/
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

/- `step*?` includes hypotheses exposed by `prepare_intro_outputs` in its suggestion. -/
/--
info: Try this:

  [apply]     let* ⟨ once, once_post ⟩ ← incr_spec
    let* ⟨ result, result_post ⟩ ← incr_spec
    agrind
-/
#guard_msgs in
example (value : Nat) :
    triple True (incrTwice value) (fun result => result = value + 1 + 1) := by
  unfold incrTwice
  step*?

/- `prepare_intro_outputs` may solve a prepared continuation completely. -/
example (value : Nat) :
    triple True (incrTwice value) (fun _ => True) := by
  unfold incrTwice
  step

/-! ## `runPrepareIntroOutputs` contract -/

elab "run_constructor" : tactic => do
  Step.runPrepareIntroOutputs ``Lean.Parser.Tactic.constructor

/- `runPrepareIntroOutputs` rejects tactics that create multiple goals. -/
/--
error: `prepare_intro_outputs` must not create multiple goals
-/
#guard_msgs in
example (P Q : Prop) : P ∧ Q := by
  run_constructor

elab "run_assumption" : tactic => do
  Step.runPrepareIntroOutputs ``Lean.Parser.Tactic.assumption

/- `runPrepareIntroOutputs` permits tactics that solve the goal completely. -/
example (P : Prop) (h : P) : P := by
  run_assumption

theorem triple_step_mono_plain {P Pm : Prop} {Q : Post α}
    (m : Id α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm) (hPost : ∀ value, Qm value → Q value) :
    triple P m Q :=
  triple_step_mono m Qm hStep hPre hPost

meta def bundledSpecInfo : SpecInfo := {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono_plain
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    to_mvcgen := none
    liftings := #[]
  }

#register_spec_info bundledSpecInfo

example (m : Id (Nat × Nat)) (n : Nat)
    (h : triple True m (fun p => p.2 = n)) :
    triple True m (Aeneas.Std.uncurry fun (_a : Nat) (b : Nat) => b ≤ n) := by
  step with h
  guard_hyp b_post : b = n
  exact Nat.le_of_eq b_post

example (m : Id Nat) (P Q : Nat → Prop)
    (h : triple True m (fun r => P r ∧ Q r)) : triple True m P := by
  step with h as ⟨result, post⟩
  guard_hyp post : P result ∧ Q result
  exact post.1

syntax (name := keepBundled) "keep_bundled" : tactic
macro_rules
  | `(tactic| keep_bundled) => `(tactic| try (intro value; rw [triple_pull]; revert value))

#register_spec_info { bundledSpecInfo with prepare_intro_outputs := some ``keepBundled }

example (m : Id Nat) (next : Nat → Id Nat) (P Q S : Nat → Prop)
    (h : triple True m (fun r => P r ∧ Q r))
    (hNext : ∀ r, P r → triple True (next r) S) :
    triple True (m >>= next) S := by
  step with h as ⟨result, post⟩
  guard_hyp post : P result ∧ Q result
  exact hNext result post.1

end Aeneas.Tactic.Step.Tests.IntroTactic
