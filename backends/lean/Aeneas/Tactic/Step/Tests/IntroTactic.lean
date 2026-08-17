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

theorem triple_uncurry (P : α → β → Prop) (next : α × β → Id γ) (Q : Post γ) :
    (∀ value, triple (Std.WP.uncurry' P value) (next value) Q) ↔
    (∀ first second, triple (P first second) (next (first, second)) Q) := by
  constructor
  · intro h first second
    simpa [Std.WP.uncurry'] using h (first, second)
  · rintro h ⟨ first, second ⟩
    simpa [Std.WP.uncurry'] using h first second

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

/- intro tactic -/
syntax (name := pullPre) "pull_pre" : tactic
macro_rules
  | `(tactic| pull_pre) =>
    `(tactic| first
      | exact triple_true _ _
      | (rw [triple_pull]; try rw [and_imp])
      | skip)

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    uncurry_elim_tactics := #[``triple_uncurry]
    qimp_elim_tactics := #[``Post.entails_iff, ``true_imp_iff]
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

def pair (value : Nat) : Id (Nat × Nat) :=
  (value, value + 1)

@[step]
theorem pair_spec (value : Nat) :
    triple True (pair value)
      (Std.WP.uncurry' fun first second => first = value ∧ second = value + 1) := by
  unfold triple pair Std.WP.uncurry'
  simp

attribute [irreducible] triple

@[irreducible] def incrTwice (value : Nat) : Id Nat := do
  let once ← incr value
  incr once

def incrPair (value : Nat) : Id Nat :=
  pair value >>= fun output => incr (output.1 + output.2)

/- Registered uncurrying runs before `intro_tactic`, which then exposes both hypotheses. -/
example (value : Nat) :
    triple True (incrPair value) (fun result => result = value + (value + 1) + 1) := by
  unfold incrPair
  step as ⟨ first, second, hFirst, hSecond ⟩
  guard_hyp hFirst : first = value
  guard_hyp hSecond : second = value + 1
  step*

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

/-! ## `runTacUnderBinders` contract -/

elab "run_constructor_under_binders" : tactic => do
  Step.runTacUnderBinders ``Lean.Parser.Tactic.constructor

/- `runTacUnderBinders` rejects tactics that create multiple goals. -/
/--
error: `intro_tactic` must not create multiple goals
-/
#guard_msgs in
example (P Q : Prop) : P → Q → P ∧ Q := by
  run_constructor_under_binders

elab "run_assumption_under_binders" : tactic => do
  Step.runTacUnderBinders ``Lean.Parser.Tactic.assumption

/- `runTacUnderBinders` permits tactics that solve the goal completely. -/
example (P : Prop) : P → P := by
  run_assumption_under_binders

end Aeneas.Tactic.Step.Tests.IntroTactic
