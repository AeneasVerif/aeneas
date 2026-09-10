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
    (hPost : Post.entails Qm Q) :
    triple P m Q :=
  fun hP => hPost m (hStep (hPre hP))

inductive DischargeMarker : Prop where
  | intro

theorem triple_step_bind {P Pm : Prop} {next : α → Id β} {Q : Post β}
    (m : Id α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (_ : DischargeMarker) -- `step` must apply the registered discharge tactic.
    (hNext : ∀ value, triple (Qm value) (next value) Q) :
    triple P (m >>= next) Q :=
  fun hP => hNext m (hStep (hPre hP))


theorem dischargeMarker : DischargeMarker :=
  .intro

elab "discharge_markers" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| first
    | exact dischargeMarker
    | assumption))

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    discharge_tactic := some `discharge_markers
    qimp_elim_tactics := #[``Post.entails_iff, ``true_imp_iff]
    uncurry_elim_tactics := #[]
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

end Aeneas.Tactic.Step.Tests.DischargeTactic
