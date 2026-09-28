module
import Aeneas.Data.Coinductive.ITreeWP.Taxonomy
import all Init.Internal.Order.Basic


namespace Aeneas.Data.Coinductive.TotalTests

variable {E : Effect} {θ : EffectWP E}
variable [θ.Monotone]

/-! # Liberal versus total WPs under event health conditions -/

/-- Perform `event` forever, ignoring its answers. -/
def forever (event : E.I) : ITree E Unit :=
  .vis event fun _ => forever event
partial_fixpoint

/-- DWLP accepts a productive infinite program, as long as its event is safe. -/
theorem forever_partial {event : E.I} (hSafe : ∀ s, θ.wp event (fun _ _ => True) s)
    (Q : θ.Post Unit) (s : θ.State) : DWLP θ (forever event) Q s := by
  refine DWLP.coinduction (fun t _ => t = forever event) ?_ rfl
  rintro _ s' rfl
  rw [forever, FunctionalWP.vis]
  exact θ.wp_mono (fun _ _ _ => forever.eq_1 event) (hSafe s')

/-- DWP rejects a productive infinite program: since no event can guarantee
    `False`, a tree that never returns is never totally correct. -/
theorem forever_not_total [θ.NoMiracle] (event : E.I) (Q : θ.Post Unit) (s : θ.State) :
    ¬ DWP θ (forever event) Q s := by
  intro hSpec
  refine DWP.induction (P := fun t _ => t = forever event → False)
    (fun _ _ _ hEq => ?_) (fun _ k s' hWp hEq => ?_) hSpec rfl
  · rw [forever] at hEq
    exact not_vis_ret hEq
  · rw [forever] at hEq
    obtain ⟨rfl, hk⟩ := vis_inj hEq
    obtain rfl := eq_of_heq hk
    exact θ.wp_noMiracle _ s' (θ.wp_mono (fun _ _ h => h rfl) hWp)

example [θ.Conjunctive] [θ.NoMiracle] {event : E.I}
    (hSafe : ∀ s, θ.wp event (fun _ _ => True) s) (Q : θ.Post Unit) (s : θ.State) :
    ¬ DWP θ (forever event) Q s :=
  dwp_no_loops (forever_partial hSafe (fun _ _ => False) s)

/-- A silent infinite program -/
def silentLoop : ITree E Unit := do
  let _ ← (pure () : ITree E Unit)
  silentLoop
partial_fixpoint

theorem silentLoop_eq_div : (silentLoop : ITree E Unit) = ITree.div := by
  apply ITree.le_div_is_div
  refine silentLoop.fixpoint_induct (fun x => Lean.Order.PartialOrder.rel x ITree.div)
    (fun _ hc h => Lean.Order.csup_le hc h) ?_
  intro x hx
  simpa only [Bind.bind, ITree.pure_eq_ret, itree_ret_bind] using hx

/-- DWP rejects a silent infinite program. -/
example (Q : θ.Post Unit) (s : θ.State) : ¬ DWP θ silentLoop Q s := by
  rw [silentLoop_eq_div]
  exact DWP.div_false

/-- DWLP accepts a silent infinite program. -/
example (Q : θ.Post Unit) (s : θ.State) : DWLP θ silentLoop Q s := by
  rw [silentLoop_eq_div]
  exact DWLP.div

end Aeneas.Data.Coinductive.TotalTests

namespace Aeneas.Data.Coinductive.StateTest


/-! # Instantiate DWP and DWLP with multiple effects -/

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
def effectSpec : EffectWP StateEffect where
  State := Nat
  wp event C state :=
    match event with
    | .get => C ⟨state⟩ state
    | .put value => C ⟨()⟩ value
    | .fail => False
    | .choose α => Nonempty α ∧ ∀ answer, C ⟨answer⟩ state

instance : EffectWP.Monotone effectSpec where
  wp_mono := by
    rintro event C C' hC state hWp
    cases event
    · exact hC _ _ hWp
    · exact hC _ _ hWp
    · exact hWp.elim
    · exact ⟨hWp.1, fun answer => hC _ _ (hWp.2 answer)⟩

instance : EffectWP.Conjunctive effectSpec where
  wp_conj := by
    rintro event state Demands ⟨C₀, hC₀⟩ hAll
    cases event
    · exact fun C hC => hAll C hC
    · exact fun C hC => hAll C hC
    · exact (hAll C₀ hC₀).elim
    · exact ⟨(hAll C₀ hC₀).1, fun answer C hC => (hAll C hC).2 answer⟩

instance : EffectWP.NoMiracle effectSpec where
  wp_noMiracle := by
    rintro (_ | _ | _ | _) _ h
    · exact h
    · exact h
    · exact h
    · exact h.1.elim h.2

example (m : ITree StateEffect α) : effectSpec.Post α → effectSpec.Pre :=
  DWP effectSpec m

example (m : ITree StateEffect α) : effectSpec.Post α → effectSpec.Pre :=
  DWLP effectSpec m

def spec (m : ITree StateEffect α) (p : effectSpec.Post α) (state : Nat) : Prop :=
  DWP effectSpec m p state

def dspec (m : ITree StateEffect α) (p : effectSpec.Post α) (state : Nat) : Prop :=
  DWLP effectSpec m p state

example (Q : effectSpec.Post Nat) :
    Lean.Order.admissible fun computation : ITree StateEffect Nat =>
      dspec computation Q 0 :=
  DWLP.admissible effectSpec Q 0

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
  apply DWP.vis
  apply DWP.vis
  exact DWP.ret_iff.mpr ⟨rfl, rfl⟩

example (state : Nat) :
    spec increment (fun value state' => value = state ∧ state' = state + 1)
      state :=
  increment_spec state

example (state : Nat) :
    dspec increment (fun value state' => value = state ∧ state' = state + 1)
      state :=
  DWP.toPartial (increment_spec state)

example (state : Nat) :
    spec flip (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      state := by
  simp [spec, flip, choose, Bind.bind]
  apply DWP.vis
  change Nonempty Bool ∧ ∀ answer : Bool,
    DWP effectSpec (.ret (if answer then 0 else 1))
      (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state) state
  constructor
  · exact ⟨true⟩
  · intro answer
    apply DWP.ret_iff.mpr
    cases answer
    · simp
    · simp

example (state : Nat) :
    dspec flip (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      state :=
  DWP.toPartial (show
    spec flip (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      state by
    simp [spec, flip, choose, Bind.bind]
    apply DWP.vis
    change Nonempty Bool ∧ ∀ answer : Bool,
      DWP effectSpec (.ret (if answer then 0 else 1))
        (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state) state
    constructor
    · exact ⟨true⟩
    · intro answer
      apply DWP.ret_iff.mpr
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
