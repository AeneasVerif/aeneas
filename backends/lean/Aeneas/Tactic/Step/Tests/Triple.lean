import Aeneas.Tactic.Step

/-!
This file tests the use of a custom triple with `#register_spec_info`
-/

open Aeneas

namespace Aeneas.Tactic.Step.Tests.Triple

abbrev State := Nat × Nat
abbrev Pre := State → Prop
abbrev Post (α : Type) := State → α → Prop

def Pre.entails (P Q : Pre) : Prop :=
  ∀ state, P state → Q state

def Post.entails (P Q : Post α) : Prop :=
  ∀ state value, P state value → Q state value

class Post.Admissible (Q : Post α) : Prop where
  admissible : True

theorem Post.entails_iff (P Q : Post α) :
    Post.entails P Q ↔ ∀ state value, P state value → Q state value :=
  Iff.rfl

/- A simple state monad manipulating pairs of natural numbers. -/
def TestM (α : Type) := State → α × State

instance : Monad TestM where
  pure value := fun state => (value, state)
  bind m next := fun state => next (m state).1 (m state).2

/- The precondition constrains the initial state, while the postcondition constrains
the final state together with the returned value. -/
def triple (P : Pre) (m : TestM α) (Q : Post α) : Prop :=
  ∀ state, P state → Q (m state).2 (m state).1

theorem triple_step_mono {P Pm : Pre} {Q : Post α}
    (m : TestM α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : Pre.entails P Pm)
    (hPost : Post.entails Qm Q) :
    triple P m Q :=
  fun state hP => hPost _ _ (hStep state (hPre state hP))

theorem triple_step_bind {P Pm : Pre} {next : α → TestM β}
    {Q : Post β}
    (m : TestM α) (Qm : Post α) (hStep : triple Pm m Qm)
    [Post.Admissible Qm]
    (hPre : Pre.entails P Pm)
    (hNext :
      ∀ state value,
        Qm state value →
        triple (fun state' => state' = state) (next value) Q) :
    triple P (m >>= next) Q :=
  fun state hP =>
    hNext (m state).2 (m state).1 (hStep state (hPre state hP)) (m state).2 rfl

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 6
    uncurry_elim_tactics := #[``true_imp_iff]
    qimp_elim_tactics := #[``Post.entails_iff, ``true_imp_iff]
    to_mvcgen := none
    liftings := #[]
  }

@[step]
theorem pure_spec (value : α) :
    triple (fun _ => True) (pure value : TestM α)
      (fun _ result => result = value) :=
  fun _ _ => rfl

example (value : Nat) :
    triple (fun _ => True) (pure value : TestM Nat)
      (fun _ result => result = value) := by
  step* by simp [Pre.entails]

/- Stores `value` in the first component and `value + 1` in the second one. -/
def setAndReturn (value : Nat) : TestM Nat :=
  fun _ => (value, (value, value + 1))

instance setAndReturn_admissible (value : Nat) :
    Post.Admissible
      (fun (current, next) result =>
        current = value ∧ next = value + 1 ∧ result = value) :=
  ⟨trivial⟩

@[step]
theorem setAndReturn_spec (value : Nat) :
    triple (fun _ => True) (setAndReturn value)
      (fun (current, next) result =>
        current = value ∧ next = value + 1 ∧ result = value) :=
  fun _ _ => ⟨rfl, rfl, rfl⟩

example (value : Nat) :
    triple (fun state => state = (0, 0)) (setAndReturn value)
      (fun (current, next) result =>
        current = value ∧ next = value + 1 ∧ result = value) := by
  step by simp [Pre.entails]
  simp_all

/- The let-step syntax works for a computation living outside `Std.RustM`, and still
introduces the pretty equality that records where the outputs come from. -/
/--
trace: value : ℕ
state : State
_ : [> let state ← setAndReturn value <]
result : ℕ
hPost : state.1 = value ∧ state.2 = value + 1 ∧ result = value
⊢ state.1 = value ∧ state.2 = value + 1 ∧ result = value
-/
#guard_msgs in
set_option pp.mvars false in
example (value : Nat) :
    triple (fun state => state = (0, 0)) (setAndReturn value)
      (fun (current, next) result =>
        current = value ∧ next = value + 1 ∧ result = value) := by
  let* ⟨ state, result, hPost ⟩ ← setAndReturn_spec by
    simp [Pre.entails]
  trace_state
  simp_all

def setTwice (first second : Nat) : TestM Nat := do
  let _ ← setAndReturn first
  setAndReturn second

/- The bind rule produces a typeclass premise, an entailment, and the continuation. -/
example (first second : Nat) :
    triple (fun state => state = (0, 0)) (setTwice first second)
      (fun (current, next) result =>
        current = second ∧ next = second + 1 ∧ result = second) := by
  unfold setTwice
  step* by simp [Pre.entails]

/- Stores the pair `(left, right)` in the state and returns it. -/
def setAndReturnPair (left right : Nat) : TestM (Nat × Nat) :=
  fun _ => ((left, right), (left, right))

instance setAndReturnPair_admissible (left right : Nat) :
    Post.Admissible
      (fun (stateLeft, stateRight) (leftResult, rightResult) =>
        stateLeft = left ∧ stateRight = right ∧
        leftResult = left ∧ rightResult = right) :=
  ⟨trivial⟩

@[step]
theorem setAndReturnPair_spec (left right : Nat) :
    triple (fun _ => True) (setAndReturnPair left right)
      (fun (stateLeft, stateRight) (leftResult, rightResult) =>
        stateLeft = left ∧ stateRight = right ∧
        leftResult = left ∧ rightResult = right) :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

def setPairThenSum (left right : Nat) : TestM Nat := do
  let (leftResult, rightResult) ← setAndReturnPair left right
  setAndReturn (leftResult + rightResult)

/- Pair binders for both state and result must be uncurried before continuing. -/
example (left right : Nat) :
    triple (fun _ => True) (setPairThenSum left right)
      (fun (current, next) result =>
        current = left + right ∧ next = left + right + 1 ∧
        result = left + right) := by
  unfold setPairThenSum
  step* by simp [Pre.entails]

def setFromBool (condition : Bool) (onTrue onFalse : Nat) : TestM Nat :=
  if condition then setAndReturn onTrue else setAndReturn onFalse

/- `step*` must split conditionals under any registered specification predicate. -/
example (condition : Bool) (onTrue onFalse : Nat) :
    triple (fun _ => True) (setFromBool condition onTrue onFalse)
      (fun (current, next) result => current = result ∧ next = result + 1) := by
  unfold setFromBool
  step* by simp [Pre.entails]

def setFromOption (value : Option Nat) : TestM Nat :=
  match value with
  | some value => setAndReturn value
  | none => setAndReturn 0

/- The same registered-specification lookup is used for matcher case splits. -/
example (value : Option Nat) :
    triple (fun _ => True) (setFromOption value)
      (fun (current, next) result => current = result ∧ next = result + 1) := by
  unfold setFromOption
  step* by simp [Pre.entails]

/- A tactic such as `by_cases` leaves the goal's type as an assigned metavariable
rather than a syntactic application. `step*` must instantiate it before analyzing
the target, otherwise it treats the branch below as a terminal call and stops. -/
def bindThenIf (condition : Bool) (onTrue onFalse : Nat) : TestM Nat := do
  let _ ← setAndReturn 0
  if condition then setAndReturn onTrue else setAndReturn onFalse

example (condition : Bool) (onTrue onFalse : Nat) :
    triple (fun _ => True) (bindThenIf condition onTrue onFalse)
      (fun (current, next) result => current = result ∧ next = result + 1) := by
  unfold bindThenIf
  step by simp [Pre.entails]
  by_cases hIrrelevant : onTrue = onFalse
  · step* by simp [Pre.entails]
  · step* by simp [Pre.entails]

def bindThenMatch (value : Option Nat) : TestM Nat := do
  let _ ← setAndReturn 0
  match value with
  | some value => setAndReturn value
  | none => setAndReturn 0

example (value : Option Nat) (a b : Nat) :
    triple (fun _ => True) (bindThenMatch value)
      (fun (current, next) result => current = result ∧ next = result + 1) := by
  unfold bindThenMatch
  step by simp [Pre.entails]
  by_cases hIrrelevant : a = b
  · step* by simp [Pre.entails]
  · step* by simp [Pre.entails]

end Aeneas.Tactic.Step.Tests.Triple
