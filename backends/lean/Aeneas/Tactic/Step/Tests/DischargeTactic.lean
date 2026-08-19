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

axiom TestM : Type → Type
axiom instMonadTestM : Monad TestM
attribute [instance] instMonadTestM

axiom triple (P : Prop) (m : TestM α) (Q : Post α) : Prop

axiom triple_step_mono {P Pm : Prop} {Q : Post α}
    (m : TestM α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (hPost : Post.entails Qm Q) :
    triple P m Q

axiom DischargeMarker : Prop

axiom triple_step_bind {P Pm : Prop} {next : α → TestM β} {Q : Post β}
    (m : TestM α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (h : DischargeMarker) -- to prove this, step has to
                          -- apply the registered discharge tactic
    (hNext : ∀ value, triple (Qm value) (next value) Q) :
    triple P (m >>= next) Q


axiom dischargeMarker : DischargeMarker
axiom GhostMarker : Nat → Prop
axiom ghostMarker : GhostMarker 0
axiom GhostPairMarker : Nat → Nat → Prop
axiom ghostPairMarker : GhostPairMarker 0 1
axiom PairMarker : Nat → Nat → Prop
axiom LeftMarker : Nat → Prop
axiom RightMarker : Nat → Prop
axiom PartialMarker : Nat → Prop
axiom ResultMarker : Nat → Prop
axiom FinalMarker : Prop
axiom pairMarker : PairMarker 0 1
axiom leftMarker : LeftMarker 0
axiom rightMarker : RightMarker 1
axiom partialMarker : PartialMarker 0
axiom resultMarkerDischarge : ResultMarker 0 → FinalMarker

elab "exact_concrete_pair_marker" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless (← Utils.getMVarIds target).isEmpty do
    throwError "pair marker target still contains metavariables"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact pairMarker))

elab "exact_partial_marker" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless (← Utils.getMVarIds target).isEmpty do
    Lean.Elab.Tactic.evalTactic (← `(tactic| change PartialMarker 0))
    throwError "partial marker target initially contained metavariables"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact partialMarker))

elab "discharge_markers" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| first
    | exact dischargeMarker
    | exact ghostMarker
    | exact ghostPairMarker
    | exact_concrete_pair_marker
    | exact_partial_marker
    | apply resultMarkerDischarge <;> assumption
    | exact leftMarker
    | exact rightMarker))

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
    to_mvcgen := none
    liftings := #[]
  }

axiom pureValue (value : Nat) : TestM Nat

@[step]
axiom pureValue_spec (value : Nat) (h:DischargeMarker) :
    triple True (pureValue value) (fun _ => DischargeMarker)

/- Should infer the ghost argument from the precondition. -/
example (value : Nat) :
    triple True (pureValue value) (fun  _ => DischargeMarker) := by
  step
  assumption -- Plain `step` leaves the mono goal for the caller.

/- `step*` runs the specification's discharge tactic on the final mono goal. -/
example (value : Nat) :
    triple True (pureValue value) (fun _ => DischargeMarker) := by
  step*

axiom pureValue_ghost_pair_spec (value leftGhost rightGhost : Nat)
    (h : GhostPairMarker leftGhost rightGhost) :
    triple True (pureValue value) (fun _ => DischargeMarker)

/- Should infer the two ghost arguments `leftGhost` and `rightGhost`. -/
example (value : Nat) :
    triple True (pureValue value) (fun _ => DischargeMarker) := by
  step with pureValue_ghost_pair_spec
  assumption

axiom pureValue_staged_ghost_spec (value leftGhost rightGhost : Nat)
    (hPair : PairMarker leftGhost rightGhost)
    (hLeft : LeftMarker leftGhost)
    (hRight : RightMarker rightGhost) :
    triple True (pureValue value) (fun result => result = value)

/- The first precondition, `hPair`, cannot be discharged while it contains metavariables.
The other two preconditions, `hLeft` and `hRight`, can be inferred later,
so the inference phase must revisit `hPair`. -/
example (value : Nat) :
    triple True (pureValue value) (fun result => result = value) := by
  step with pureValue_staged_ghost_spec
  assumption

axiom finalDischargeValue : TestM Nat

@[step]
axiom finalDischargeValue_spec (ghost : Nat)
    (h : PairMarker ghost 1) :
    triple True finalDischargeValue (fun _ => ResultMarker ghost)

/- The final discharge solves `ghost`, so `step*` must retry the precondition that
could not be discharged before `ghost` was known. -/
/--
error: unsolved goals
case h
⊢ PairMarker 0 1
-/
#guard_msgs in
example :
    triple True finalDischargeValue (fun _ => FinalMarker) := by
  step*

axiom partialDischargeValue : TestM Nat

axiom partialDischargeValue_spec (ghost : Nat)
    (hPartial : PartialMarker ghost)
    (hPair : PairMarker ghost 1) :
    triple True partialDischargeValue (fun _ => True)

/- Discharging `hPartial` unifies `ghost` with `0` before failing. The unification
must be retained so that `hPair` can be solved and `hPartial` retried. -/
/--
error: Tactic `assumption` failed

case ghost
⊢ ℕ
-/
#guard_msgs in
example :
    triple True partialDischargeValue (fun _ => True) := by
  step with partialDischargeValue_spec
  assumption

axiom dischargeValue (value : Nat) : TestM Nat

@[step]
axiom dischargeValue_spec (value leftGhost rightGhost : Nat)
    (hPair : PairMarker leftGhost rightGhost)
    (hLeft : LeftMarker leftGhost)
    (hRight : RightMarker rightGhost)
    (hDischarge : DischargeMarker) :
    triple True (dischargeValue value)
      (fun result => result = value + leftGhost + rightGhost)

/- The solution suggested by `step?` works for a mono step whose specification
requires the registered discharge tactic. -/
example (value : Nat) :
    triple True (dischargeValue value) (fun _ => DischargeMarker) := by
  step? says step with dischargeValue_spec
  exact dischargeMarker

/- The solution suggested by `step?` also works for a bind step whose specification
requires the registered discharge tactic. -/
example (value : Nat) :
    triple True
      (dischargeValue value >>= fun first =>
       dischargeValue (first + value) >>= fun second =>
       dischargeValue (first + second))
      (fun _ => DischargeMarker) := by
  step? says step with dischargeValue_spec
  step? says step with dischargeValue_spec
  step
  exact dischargeMarker

/--
info: Try this:

  [apply]     let* ⟨ _, _ ⟩ ← pureValue_spec
    agrind
-/
#guard_msgs in
example (value : Nat) :
    triple True (pureValue value) (fun _ => DischargeMarker) := by
  step*?

/--
info: Try this:

  [apply]     let* ⟨ result, result_post ⟩ ← dischargeValue_spec
    discharge_markers
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (value : Nat) :
    triple True (dischargeValue value) (fun result => DischargeMarker) := by
  step*?

/- The solution emitted by `step*?` must also work when replayed. -/
set_option linter.unusedVariables false in
example (value : Nat) :
    triple True (dischargeValue value) (fun result => DischargeMarker) := by
  let* ⟨ result, result_post ⟩ ← dischargeValue_spec
  discharge_markers

/--
info: Try this:

  [apply]     let* ⟨ first ⟩ ← dischargeValue_spec
    let* ⟨ second ⟩ ← dischargeValue_spec
    let* ⟨ result, result_post ⟩ ← dischargeValue_spec
    discharge_markers
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (value : Nat) :
    triple True
      (dischargeValue value >>= fun first =>
       dischargeValue (first + value) >>= fun second =>
       dischargeValue (first + second))
      (fun result => DischargeMarker) := by
  step*?

/- The bind solution emitted by `step*?` must also work when replayed. -/
set_option linter.unusedVariables false in
example (value : Nat) :
    triple True
      (dischargeValue value >>= fun first =>
       dischargeValue (first + value) >>= fun second =>
       dischargeValue (first + second))
      (fun result => DischargeMarker) := by
  let* ⟨ first ⟩ ← dischargeValue_spec
  let* ⟨ second ⟩ ← dischargeValue_spec
  let* ⟨ result, result_post ⟩ ← dischargeValue_spec
  discharge_markers

end Aeneas.Tactic.Step.Tests.DischargeTactic
