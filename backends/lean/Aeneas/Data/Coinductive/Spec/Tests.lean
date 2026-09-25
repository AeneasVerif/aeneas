module
import Aeneas.Data.Coinductive.Spec.SpecDerived
import all Init.Internal.Order.Basic

/-! # Tests for the generic total- and partial-correctness specifications -/

namespace Aeneas.Data.Coinductive.StateTest

inductive StateEvent : Type 1 where
  | get
  | put (value : Nat)
  | fail
  | choose (α : Type)

@[reducible]
def StateEvent.output : StateEvent → Type 1
  | .get => ULift Nat
  | .put _ => ULift Unit
  | .fail => ULift Unit
  | .choose α => ULift α

@[reducible]
def StateEffect : Effect where
  I := StateEvent
  O := StateEvent.output

@[reducible]
def effectSpec : EffectSpec StateEffect where
  State := Nat
  wp event C state :=
    match event with
    | .get => C ⟨state⟩ state
    | .put value => C ⟨()⟩ value
    | .fail => False
    | .choose α => Nonempty α ∧ ∀ answer, C ⟨answer⟩ state
  wp_mono := by
    rintro event C C' hC state hWp
    cases event
    · exact hC _ _ hWp
    · exact hC _ _ hWp
    · exact hWp.elim
    · exact ⟨hWp.1, fun answer => hC _ _ (hWp.2 answer)⟩
  wp_conj := by
    rintro event state Demands ⟨C₀, hC₀⟩ hAll
    cases event
    · exact fun C hC => hAll C hC
    · exact fun C hC => hAll C hC
    · exact (hAll C₀ hC₀).elim
    · exact ⟨(hAll C₀ hC₀).1, fun answer C hC => (hAll C hC).2 answer⟩
  wp_noMiracle := by
    rintro (_ | _ | _ | _) _ h
    · exact h
    · exact h
    · exact h
    · exact h.1.elim h.2

def spec (m : ITree StateEffect α) (p : effectSpec.Post α) (state : Nat) : Prop :=
  TotalSpec effectSpec p m state

def dspec (m : ITree StateEffect α) (p : effectSpec.Post α) (state : Nat) : Prop :=
  PartialSpec effectSpec p m state

example (Q : effectSpec.Post Nat) :
    Lean.Order.admissible fun computation : ITree StateEffect Nat =>
      dspec computation Q 0 :=
  PartialSpec.admissible effectSpec Q 0

def get : ITree StateEffect Nat :=
  .vis .get fun value => .ret value.down

def put (value : Nat) : ITree StateEffect Unit :=
  .vis (.put value) fun result => .ret result.down

def fail : ITree StateEffect Unit :=
  .vis .fail fun result => .ret result.down

def choose (α : Type) : ITree StateEffect α :=
  .vis (.choose α) fun result => .ret result.down

def increment : ITree StateEffect Nat :=
  do
    let value ← get
    let _ ← put (value + 1)
    return value

def failure : ITree StateEffect Unit :=
  do
    let _ ← fail
    return ()

def flip : ITree StateEffect Nat :=
  do
    let answer ← choose Bool
    return if answer then 0 else 1

theorem increment_spec (state : Nat) :
    spec increment (fun value state' => value = state ∧ state' = state + 1)
      state := by
  simp [spec, increment, get, put, Bind.bind]
  apply TotalSpec.vis
  apply TotalSpec.vis
  exact TotalSpec.ret_iff.mpr ⟨rfl, rfl⟩

example (state : Nat) :
    spec increment (fun value state' => value = state ∧ state' = state + 1)
      state :=
  increment_spec state

example (state : Nat) :
    dspec increment (fun value state' => value = state ∧ state' = state + 1)
      state :=
  TotalSpec.toPartial (increment_spec state)

example (state : Nat) :
    spec flip (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      state := by
  simp [spec, flip, choose, Bind.bind]
  apply TotalSpec.vis
  change Nonempty Bool ∧ ∀ answer : Bool,
    TotalSpec effectSpec
      (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      (.ret (if answer then 0 else 1)) state
  constructor
  · exact ⟨true⟩
  · intro answer
    apply TotalSpec.ret_iff.mpr
    cases answer
    · simp
    · simp

example (state : Nat) :
    dspec flip (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      state :=
  TotalSpec.toPartial (show
    spec flip (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      state by
    simp [spec, flip, choose, Bind.bind]
    apply TotalSpec.vis
    change Nonempty Bool ∧ ∀ answer : Bool,
      TotalSpec effectSpec
        (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
        (.ret (if answer then 0 else 1)) state
    constructor
    · exact ⟨true⟩
    · intro answer
      apply TotalSpec.ret_iff.mpr
      cases answer
      · simp
      · simp)

example (state : Nat) (Q : effectSpec.Post Unit) :
    ¬ spec failure Q state := by
  intro hSpec
  simp [spec, failure, fail, Bind.bind] at hSpec
  exact hSpec.vis_view

example (state : Nat) (Q : effectSpec.Post Unit) :
    ¬ dspec failure Q state := by
  intro hSpec
  simp [dspec, failure, fail, Bind.bind] at hSpec
  exact hSpec.vis_view

end Aeneas.Data.Coinductive.StateTest
