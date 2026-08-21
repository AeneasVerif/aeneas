import Aeneas.Tactic.Step

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

axiom TestM : Type → Type
axiom instMonadTestM : Monad TestM
attribute [instance] instMonadTestM

axiom triple (P : Pre) (m : TestM α) (Q : Post α) : Prop

axiom triple_step_mono {P Pm : Pre} {Q : Post α}
    (m : TestM α) (Qm : Post α) (hStep : triple Pm m Qm)
    (hPre : Pre.entails P Pm)
    (hPost : Post.entails Qm Q) :
    triple P m Q

axiom triple_step_bind {P Pm : Pre} {next : α → TestM β}
    {Q : Post β}
    (m : TestM α) (Qm : Post α) (hStep : triple Pm m Qm)
    [Post.Admissible Qm]
    (hPre : Pre.entails P Pm)
    (hNext :
      ∀ state value,
        Qm state value →
        triple (fun state' => state' = state) (next value) Q) :
    triple P (m >>= next) Q

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
axiom pure_spec (value : α) :
    triple (fun _ => True) (pure value : TestM α)
      (fun _ result => result = value)

example (value : Nat) :
    triple (fun _ => True) (pure value : TestM Nat)
      (fun _ result => result = value) := by
  step* by simp [Pre.entails]

axiom setAndReturn (value : Nat) : TestM Nat

axiom setAndReturn_admissible (value : Nat) :
    Post.Admissible
      (fun (current, next) result =>
        current = value ∧ next = value + 1 ∧ result = value)
attribute [instance] setAndReturn_admissible

@[step]
axiom setAndReturn_spec (value : Nat) :
    triple (fun _ => True) (setAndReturn value)
      (fun (current, next) result =>
        current = value ∧ next = value + 1 ∧ result = value)

example (value : Nat) :
    triple (fun state => state = (0, 0)) (setAndReturn value)
      (fun (current, next) result =>
        current = value ∧ next = value + 1 ∧ result = value) := by
  step by simp [Pre.entails]
  simp_all

/- The let-step syntax works for a computation living outside `Std.Result`, and still
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

noncomputable def setTwice (first second : Nat) : TestM Nat := do
  let _ ← setAndReturn first
  setAndReturn second

/- The bind rule produces a typeclass premise, an entailment, and the continuation. -/
example (first second : Nat) :
    triple (fun state => state = (0, 0)) (setTwice first second)
      (fun (current, next) result =>
        current = second ∧ next = second + 1 ∧ result = second) := by
  unfold setTwice
  step* by simp [Pre.entails]

axiom setAndReturnPair (left right : Nat) : TestM (Nat × Nat)

axiom setAndReturnPair_admissible (left right : Nat) :
    Post.Admissible
      (fun (stateLeft, stateRight) (leftResult, rightResult) =>
        stateLeft = left ∧ stateRight = right ∧
        leftResult = left ∧ rightResult = right)
attribute [instance] setAndReturnPair_admissible

@[step]
axiom setAndReturnPair_spec (left right : Nat) :
    triple (fun _ => True) (setAndReturnPair left right)
      (fun (stateLeft, stateRight) (leftResult, rightResult) =>
        stateLeft = left ∧ stateRight = right ∧
        leftResult = left ∧ rightResult = right)

noncomputable def setPairThenSum (left right : Nat) : TestM Nat := do
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

noncomputable def setFromBool (condition : Bool) (onTrue onFalse : Nat) : TestM Nat :=
  if condition then setAndReturn onTrue else setAndReturn onFalse

/- `step*` must split conditionals under any registered specification predicate. -/
example (condition : Bool) (onTrue onFalse : Nat) :
    triple (fun _ => True) (setFromBool condition onTrue onFalse)
      (fun (current, next) result => current = result ∧ next = result + 1) := by
  unfold setFromBool
  step* by simp [Pre.entails]

noncomputable def setFromOption (value : Option Nat) : TestM Nat :=
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
noncomputable def bindThenIf (condition : Bool) (onTrue onFalse : Nat) : TestM Nat := do
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

noncomputable def bindThenMatch (value : Option Nat) : TestM Nat := do
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
