import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Aeneas.Std.WP
open _root_.Std.Do (Triple SPred PostCond WPMonad)

set_option mvcgen.warning false

namespace Aeneas.MvcgenUniverseTests

/-! Heterogeneous `do` binds do not change `Std.Do`'s postcondition universes. -/

example : Type 1 := Heap
example : Type := Nat

/--
error: Application type mismatch: The argument
  Heap
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  Std.Do.PostShape.arg Heap
-/
#guard_msgs (error, drop info) in
#check _root_.Std.Do.WP Result.{0} (.arg Heap .pure)

/--
error: Application type mismatch: The argument
  Heap
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  ULift.{0, 0} Heap
-/
#guard_msgs (error, drop info) in
#check _root_.Std.Do.WP Result.{0} (.arg (ULift Heap) .pure)

def largeValue (n : Nat) : Result (ULift.{1} Nat) :=
  pure ⟨n⟩

def heterogeneous (n : Nat) : Result Nat := do
  let value ← largeValue n
  pure (value.down + 1)

example (n : Nat) :
    heterogeneous n = Aeneas.Std.bind (largeValue n)
      (fun value => Result.ok (value.down + 1)) :=
  rfl

theorem heterogeneous_eq (n : Nat) : heterogeneous n = Result.ok (n + 1) := by
  simp [heterogeneous, largeValue, pure]

/- A computation already returning `Type 1` values needs no result adapter. -/
example : WPMonad Result.{1} (.arg (ULift.{1} Heap) .pure) := inferInstance

example (n : Nat) :
    Triple (ps := .arg (ULift.{1} Heap) .pure) (largeValue n) (SPred.pure True)
      (PostCond.noThrow fun value => SPred.pure (value.down = n)) := by
  mvcgen [largeValue]

@[local step]
theorem heterogeneous_spec (n : Nat) :
    spec (heterogeneous n) (fun value => value = n + 1) := by
  rw [heterogeneous_eq]
  simp

/- The source still returns `Nat`; only the verification boundary lifts it. -/
example (n : Nat) :
    Triple (ps := .arg (ULift.{1} Heap) .pure) (Result.toMvcgen (heterogeneous n))
      (SPred.pure True)
      (PostCond.noThrow fun value => SPred.pure (value.down = n + 1)) := by
  mvcgen

example {α : Type u} (value : α) :
    Triple (ps := .arg (ULift.{u + 1} Heap) .pure)
      (Result.toMvcgen (pure value : Result α)) (SPred.pure True)
      (PostCond.noThrow fun result => SPred.pure (result.down = value)) := by
  mvcgen

end Aeneas.MvcgenUniverseTests
