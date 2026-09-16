import Aeneas.Tactic.Step

open Aeneas

/-!
# Tests for `SpecInfo.intro_tactic`

The fixture is irreducible so that the tests depend on defining an `intro_tactic`.
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

/- intro tactic: it is responsible for the whole normalization of the mono and bind
   premises, so it exposes the binders of `Post.entails` itself, introduces them — `step`
   reverts what it introduces — and pulls the precondition of the continuation. -/
syntax (name := pullPre) "pull_pre" : tactic
macro_rules
  | `(tactic| pull_pre) =>
    `(tactic| (
        try rw [Post.entails_iff]
        intros
        first
        | exact triple_true _ _
        | (rw [triple_pull]; try rw [and_imp])
        | skip))

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    intro_tactic := some ``pullPre
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

/- `step as` names the result and the hypothesis exposed by `intro_tactic`. -/
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

/- `step*?` includes hypotheses exposed by `intro_tactic` in its suggestion. -/
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

/- `intro_tactic` may solve a prepared continuation completely. -/
example (value : Nat) :
    triple True (incrTwice value) (fun _ => True) := by
  unfold incrTwice
  step

/-! ## `runIntroTactic` contract -/

elab "run_constructor" : tactic => do
  Step.runIntroTactic ``Lean.Parser.Tactic.constructor

/- `runIntroTactic` rejects tactics that create multiple goals. -/
/--
error: `intro_tactic` must not create multiple goals
-/
#guard_msgs in
example (P Q : Prop) : P ∧ Q := by
  run_constructor

elab "run_assumption" : tactic => do
  Step.runIntroTactic ``Lean.Parser.Tactic.assumption

/- `runIntroTactic` permits tactics that solve the goal completely. -/
example (P : Prop) (h : P) : P := by
  run_assumption

elab "run_intro_split" : tactic => do
  Step.runIntroTactic ``Aeneas.Step.Intro.introSplit

/- What the tactic introduces is reverted, one binder per fact: `intro_split` splits the
   conjunction it introduces, and the premise comes back with one binder per conjunct. -/
example (P Q R : Prop) (hR : R) : P ∧ Q → R := by
  run_intro_split
  guard_target = P → Q → R
  intro _ _
  exact hR

end Aeneas.Tactic.Step.Tests.IntroTactic
