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

axiom triple_step_bind {P Pm : Prop} {next : α → TestM β} {Q : Post β}
    (m : TestM α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : P → Pm)
    (hNext : ∀ value, Qm value → triple True (next value) Q) :
    triple P (m >>= next) Q

axiom DischargeMarker : Prop
axiom dischargeMarker : DischargeMarker
axiom GhostMarker : Nat → Prop
axiom ghostMarker : GhostMarker 0
axiom GhostPairMarker : Nat → Nat → Prop
axiom ghostPairMarker : GhostPairMarker 0 1
axiom PairMarker : Nat → Nat → Prop
axiom LeftMarker : Nat → Prop
axiom RightMarker : Nat → Prop
axiom pairMarker : PairMarker 0 1
axiom leftMarker : LeftMarker 0
axiom rightMarker : RightMarker 1

elab "exact_concrete_pair_marker" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless (← Utils.getMVarIds target).isEmpty do
    throwError "pair marker target still contains metavariables"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact pairMarker))

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    discharge_tactic := SpecInfo.tac
      `(tactic| first
        | exact dischargeMarker
        | exact ghostMarker
        | exact ghostPairMarker
        | exact_concrete_pair_marker
        | exact leftMarker
        | exact rightMarker
        | simp)
    qimp_elim_tactics := #[``Post.entails_iff, ``true_imp_iff]
    to_mvcgen := none
    liftings := #[]
  }

axiom pureValue (value : Nat) : TestM Nat

@[step]
axiom pureValue_spec (value : Nat) :
    triple True (pureValue value) (fun result => result = value)

axiom pureValue_ghost_spec (value ghost : Nat) (h : GhostMarker ghost) :
    triple True (pureValue value) (fun result => result = value)

/- Like the iterator calls in `VerusDoublyLinkedList.run.spec`: the discharge
tactic infers one ghost argument from a precondition. -/
example (value : Nat) :
    triple True (pureValue value) (fun result => result = value) := by
  step with pureValue_ghost_spec
  assumption

axiom pureValue_ghost_pair_spec (value leftGhost rightGhost : Nat)
    (h : GhostPairMarker leftGhost rightGhost) :
    triple True (pureValue value) (fun result => result = value)

/- Like the recursive call in `VerusBitmap.orCells.disjoint_spec`: the discharge
tactic simultaneously infers two ghost arguments from a precondition. -/
example (value : Nat) :
    triple True (pureValue value) (fun result => result = value) := by
  step with pureValue_ghost_pair_spec
  assumption

axiom pureValue_staged_ghost_spec (value leftGhost rightGhost : Nat)
    (hPair : PairMarker leftGhost rightGhost)
    (hLeft : LeftMarker leftGhost)
    (hRight : RightMarker rightGhost) :
    triple True (pureValue value) (fun result => result = value)

/- The first precondition cannot be discharged while it contains metavariables.
The other two preconditions infer them, so the inference phase must revisit it. -/
example (value : Nat) :
    triple True (pureValue value) (fun result => result = value) := by
  step (config := { grind := false }) with pureValue_staged_ghost_spec
  assumption

/- Plain `step` leaves the mono goal for the caller. -/
example (value : Nat) :
    triple True (pureValue value) (fun _ => DischargeMarker) := by
  step
  exact dischargeMarker

/- `step*` runs the specification's discharge tactic on the final mono goal. -/
example (value : Nat) :
    triple True (pureValue value) (fun _ => DischargeMarker) := by
  step*

/--
info: Try this:

  [apply]     let* ⟨ _, _ ⟩ ← pureValue_spec
    first
    | exact dischargeMarker✝
    | exact ghostMarker✝
    | exact ghostPairMarker✝
    | exact_concrete_pair_marker
    | exact leftMarker✝
    | exact rightMarker✝
    | simp
-/
#guard_msgs in
example (value : Nat) :
    triple True (pureValue value) (fun _ => DischargeMarker) := by
  step*?

end Aeneas.Tactic.Step.Tests.DischargeTactic
