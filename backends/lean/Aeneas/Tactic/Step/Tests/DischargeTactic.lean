module
public import Lean.Elab.Tactic.Basic
import Aeneas.Tactic.Step

open Aeneas

/-!
# Tests for `SpecInfo.discharge_tactic`
-/

namespace Aeneas.Tactic.Step.Tests.DischargeTactic

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
    (hPost : ∀ value, Qm value → Q value) :
    triple P m Q :=
  fun hP => hPost m (hStep (hPre hP))

inductive DischargeMarker : Prop where
  | intro

theorem triple_step_bind {P Pm : Prop} {next : α → Id β} {Q : Post β}
    (m : Id α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (_ : DischargeMarker) -- `step` must apply the registered discharge tactic.
    (hNext : ∀ value, Qm value → triple True (next value) Q) :
    triple P (m >>= next) Q :=
  fun hP => hNext m (hStep (hPre hP)) trivial


theorem dischargeMarker : DischargeMarker :=
  .intro

inductive Terminal (value : Nat) : Prop where
  | intro

theorem terminalZero : Terminal 0 :=
  .intro

inductive EqualityMarker : Prop where
  | intro

elab "discharge_equality_marker" : tactic => Lean.Elab.Tactic.withMainContext do
  unless (← Lean.getLCtx).any (fun decl => decl.type.isAppOf ``Eq) do
    Lean.throwError "Expected an equality hypothesis"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact EqualityMarker.intro))

elab "discharge_markers" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| first
    | exact dischargeMarker
    | (subst_vars; exact terminalZero)
    | discharge_equality_marker
    | assumption))

open Lean Meta Elab Tactic in
meta def prepareIntroOutputs : PrepareIntroOutputs := do
  withMainContext do
  let goalTy ← instantiateMVars (← getMainTarget)
  unless goalTy.isForall do
    throwError "Expected a quantified continuation, got:\n{goalTy}"
  Step.prepareIntroOutputsWith goalTy (.leaf none) do
    let _ ← Simp.simpAt true { failIfUnchanged := false }
      { simpThms := #[← Step.stepSimpExt.getTheorems] }
      (.targets #[] true)

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    prepare_intro_outputs := ``prepareIntroOutputs
    discharge_tactic := some `discharge_markers
    to_mvcgen := none
    liftings := #[]
  }

def pureValue (value : Nat) : Id Nat :=
  value

@[step]
theorem pureValue_spec (value : Nat) (h : DischargeMarker) :
    triple True (pureValue value) (fun _ => DischargeMarker) :=
  fun _ => h

/- Should infer the ghost argument from the precondition. -/
example (value : Nat) :
    triple True (pureValue value) (fun  _ => DischargeMarker) := by
  step
  assumption -- Plain `step` leaves the mono goal for the caller.

/- `step*` runs the specification's discharge tactic on the final mono goal. -/
example (value : Nat) :
    triple True (pureValue value) (fun _ => DischargeMarker) := by
  step*

/--
info: Try this:

  [apply]     let* ⟨ _, _ ⟩ ← pureValue_spec
    agrind
-/
#guard_msgs in
example (value : Nat) :
    triple True (pureValue value) (fun _ => DischargeMarker) := by
  step*?

def zero : Id Nat := 0

@[step]
theorem zero_spec : triple True zero (fun value => value = 0) :=
  fun _ => rfl

def finishValue (value : Nat) : Id Nat := value

theorem triple_finishValue (value : Nat) (Q : Post Nat) :
    triple True (finishValue value) Q ↔ Q value := by
  simp [triple, finishValue]

attribute [local step_simps] triple_finishValue

/- The mono goal needs equality substitution, which the registered tactic performs. -/
/--
info: Try this:

  [apply]     let* ⟨ value, value_post ⟩ ← zero_spec
    discharge_markers
-/
#guard_msgs in
example : triple True zero (fun value => Terminal value) := by
  step*?

/- Simplifying the bind continuation removes the registered specification. -/
/--
info: Try this:

  [apply]     let* ⟨ value, value_post ⟩ ← zero_spec
    discharge_markers
-/
#guard_msgs in
example : triple True (zero >>= fun value => finishValue value) Terminal := by
  step*?

/- Continue traversing while the main goal is still a registered specification. -/
example : triple True (zero >>= fun _ => zero >>= finishValue) Terminal := by
  step*

/- The discharge tactic sees the equalities, which `step*` does not substitute. -/
example : triple True zero (fun _ => EqualityMarker) := by
  step*

/--
info: Try this:

  [apply]     let* ⟨ value, value_post ⟩ ← zero_spec
    discharge_markers
-/
#guard_msgs in
example : triple True (zero >>= fun value => finishValue value) (fun _ => EqualityMarker) := by
  step*?

/- Replay the generated scripts. -/
example : triple True zero (fun value => Terminal value) := by
  let* ⟨ value, value_post ⟩ ← zero_spec
  discharge_markers

example : triple True (zero >>= fun value => finishValue value) Terminal := by
  let* ⟨ value, value_post ⟩ ← zero_spec
  discharge_markers

example : triple True (zero >>= fun value => finishValue value) (fun _ => EqualityMarker) := by
  let* ⟨ value, value_post ⟩ ← zero_spec
  discharge_markers

end Aeneas.Tactic.Step.Tests.DischargeTactic
