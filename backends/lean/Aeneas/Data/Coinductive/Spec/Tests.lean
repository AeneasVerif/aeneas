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

theorem effectSpec_conjunctive : effectSpec.Conjunctive := by
  rintro event state Demands ⟨C₀, hC₀⟩ hAll
  cases event
  · exact fun C hC => hAll C hC
  · exact fun C hC => hAll C hC
  · exact (hAll C₀ hC₀).elim
  · exact ⟨(hAll C₀ hC₀).1, fun answer C hC => (hAll C hC).2 answer⟩

def spec (m : ITree StateEffect α) (p : effectSpec.Post α) (state : Nat) : Prop :=
  TotalSpec effectSpec p m state

def dspec (m : ITree StateEffect α) (p : effectSpec.Post α) (state : Nat) : Prop :=
  PartialSpec effectSpec p m state

example (Q : effectSpec.Post Nat) :
    Lean.Order.admissible fun computation : ITree StateEffect Nat =>
      dspec computation Q 0 :=
  PartialSpec.admissible effectSpec_conjunctive Q 0

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
  exact TotalSpec.ret ⟨rfl, rfl⟩

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
    apply TotalSpec.ret
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
      apply TotalSpec.ret
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

/-! A productive infite program. -/
def flipCoinIgnore : ITree StateEffect Unit := do
  let _ <- choose Bool
  flipCoinIgnore
partial_fixpoint

/-- Partial correctness accepts a productive infinite program. -/
theorem flipCoinIgnore_dspec (state : Nat) (Q : effectSpec.Post Unit) :
    dspec flipCoinIgnore Q state := by
  refine flipCoinIgnore.fixpoint_induct (fun x => dspec x Q state)
    (PartialSpec.admissible effectSpec_conjunctive Q state) ?_
  intro x hx
  simp only [dspec, choose, Bind.bind, itree_vis_bind, itree_ret_bind]
  exact PartialSpec.vis ⟨⟨true⟩, fun _ => hx⟩

/-- A computation which is totally correct cannot also be partially correct for the `False`
    postcondition, i.e., it must eventually return. -/
theorem not_spec_of_dspec_false {m : ITree StateEffect α} {state : Nat} {Q : effectSpec.Post α}
    (hNever : dspec m (fun _ _ => False) state) : ¬ spec m Q state := by
  intro hSpec
  refine TotalSpec.induction (P := fun m s => dspec m (fun _ _ => False) s → False)
    (fun _ _ _ h => PartialSpec.ret_post h)
    (fun event k s hWp h => ?_) hSpec hNever
  have h := PartialSpec.vis_view h
  cases event with
  | get | put _ => exact hWp h
  | fail => exact hWp
  | choose _ =>
    obtain ⟨⟨a⟩, h⟩ := h
    exact hWp.2 a (h a)

/- Total correctness does not accept a productive infinite program -/
example (state : Nat) : ¬ spec flipCoinIgnore (fun _ _ => True) state :=
  not_spec_of_dspec_false (flipCoinIgnore_dspec state _)

/-! A silent infinite program -/
def silentLoop : ITree StateEffect Unit := do
  let _ ← (pure () : ITree StateEffect Unit)
  silentLoop
partial_fixpoint

theorem silentLoop_eq_div : silentLoop = ITree.div := by
  apply ITree.le_div_is_div
  refine silentLoop.fixpoint_induct (fun x => Lean.Order.PartialOrder.rel x ITree.div)
    (fun _ hc h => Lean.Order.csup_le hc h) ?_
  intro x hx
  simpa only [Bind.bind, ITree.pure_eq_ret, itree_ret_bind] using hx

/- Total correctness does not accept a silent infinite program -/
example (state : Nat) : ¬ spec silentLoop (fun _ _ => True) state := by
  rw [spec, silentLoop_eq_div]
  exact TotalSpec.div_false

/- Partial correctness accepts a silent infinite program -/
example (state : Nat) (Q : effectSpec.Post Unit) : dspec silentLoop Q state := by
  rw [dspec, silentLoop_eq_div]
  exact PartialSpec.div

end Aeneas.Data.Coinductive.StateTest
