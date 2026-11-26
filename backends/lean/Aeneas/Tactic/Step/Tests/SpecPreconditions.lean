module
import Aeneas.Std.Scalar
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

/-! # Tests for `Aeneas.Tactic.Step.SpecPreconditions` -/

namespace spec_preconditions

/-! ## The library -/

structure Shape (Self : Type) where
  area : Self → Result U32
  double_area : Self → Result U32

@[irreducible]
def Shape.double_area.default {Self : Type} (inst : Shape Self) (x : Self) : Result U32 := do
  let a ← inst.area x
  2#u32 * a

@[irreducible]
def sum_double {T : Type} (inst : Shape T) (a b : T) : Result U32 := do
  let d ← inst.double_area a
  let x ← inst.area b
  d + x

@[step]
theorem Shape.double_area.default_spec {Self : Type} (inst : Shape Self) (f : Self → Nat)
    (harea : ∀ x, f x ≤ U32.max → inst.area x ⦃ a => a.val = f x ⦄)
    (x : Self) (h : 2 * f x ≤ U32.max) :
    Shape.double_area.default inst x ⦃ r => r.val = 2 * f x ⦄ := by
  unfold Shape.double_area.default
  step*

@[step]
theorem sum_double_spec {T : Type} (inst : Shape T) (f g : T → Nat)
    (harea : ∀ x, f x ≤ U32.max → inst.area x ⦃ a => a.val = f x ⦄)
    (hdouble : ∀ x, g x ≤ U32.max → inst.double_area x ⦃ a => a.val = g x ⦄)
    (a b : T) (h : g a + f b ≤ U32.max) :
    sum_double inst a b ⦃ r => r.val = g a + f b ⦄ := by
  unfold sum_double
  step*

/-! ## The user -/

def sq (x : U32) : Result U32 := x * x

@[step]
theorem sq_spec (x : U32) (h : x.val * x.val ≤ U32.max) : sq x ⦃ y => y.val = x.val * x.val ⦄ := by
  unfold sq; step*

/-- `double_area` is the default, inlined (as `impl_def` does). -/
@[reducible]
def SqShape : Shape U32 := {
  area := sq
  double_area := fun x => do
    let a ← sq x
    2#u32 * a }

/-- Nested: the methods have specification preconditions themselves. -/
@[reducible]
def DoubledShape : Shape U32 := {
  area := Shape.double_area.default SqShape
  double_area := Shape.double_area.default SqShape }

/-! ## `step*?`, and replaying its scripts with the feature off

`g` needs the ghosts frozen: otherwise `sq`'s precondition instantiates it as `x.val * x.val`. -/

/--
info: Try this:

  [apply]     let* ⟨ r, r_post ⟩ ← [ -specPreconditions ]
      sum_double_spec (f := fun (x : U32) => ↑x * ↑x) (g := fun (x : U32) => 2 * (↑x * ↑x))
    case harea =>
      intros x _
      simp only [step_simps]
      let* ⟨ a, a_post ⟩ ← sq_spec
      agrind
    case hdouble =>
      intros x _
      simp only [step_simps]
      let* ⟨ a, a_post ⟩ ← sq_spec
      let* ⟨ a, a_post ⟩ ← U32.mul_spec
      agrind
    agrind
-/
#guard_msgs in
example (a b : U32) (h : 2 * (a.val * a.val) + b.val * b.val ≤ U32.max) :
    sum_double SqShape a b ⦃ r => r.val = 2 * (a.val * a.val) + b.val * b.val ⦄ := by
  step*?

set_option aeneas.step.specPreconditions false in
example (a b : U32) (h : 2 * (a.val * a.val) + b.val * b.val ≤ U32.max) :
    sum_double SqShape a b ⦃ r => r.val = 2 * (a.val * a.val) + b.val * b.val ⦄ := by
  let* ⟨ r, r_post ⟩ ← [ -specPreconditions ]
    sum_double_spec (f := fun (x : U32) => ↑x * ↑x) (g := fun (x : U32) => 2 * (↑x * ↑x))
  case harea =>
    intros x _
    simp only [step_simps]
    let* ⟨ a, a_post ⟩ ← sq_spec
    agrind
  case hdouble =>
    intros x _
    simp only [step_simps]
    let* ⟨ a, a_post ⟩ ← sq_spec
    let* ⟨ a, a_post ⟩ ← U32.mul_spec
    agrind
  agrind

/- Nested: the cases contain cases. -/
/--
info: Try this:

  [apply]     let* ⟨ r, r_post ⟩ ← [ -specPreconditions ]
      sum_double_spec (f := fun (x : U32) => 2 * (↑x * ↑x)) (g := fun (x : U32) => 2 * (↑x * ↑x))
    case harea =>
      intros x _
      simp only [step_simps]
      let* ⟨ a, a_post ⟩ ← [ -specPreconditions ] Shape.double_area.default_spec (f := fun (x : U32) => ↑x * ↑x)
      case harea =>
        intros x _
        simp only [step_simps]
        let* ⟨ a, a_post ⟩ ← sq_spec
        agrind
      agrind
    case hdouble =>
      intros x _
      simp only [step_simps]
      let* ⟨ a, a_post ⟩ ← [ -specPreconditions ] Shape.double_area.default_spec (f := fun (x : U32) => ↑x * ↑x)
      case harea =>
        intros x _
        simp only [step_simps]
        let* ⟨ a, a_post ⟩ ← sq_spec
        agrind
      agrind
    agrind
-/
#guard_msgs in
example (a b : U32) (h : 2 * (a.val * a.val) + 2 * (b.val * b.val) ≤ U32.max) :
    sum_double DoubledShape a b ⦃ r => r.val = 2 * (a.val * a.val) + 2 * (b.val * b.val) ⦄ := by
  step*?

set_option aeneas.step.specPreconditions false in
example (a b : U32) (h : 2 * (a.val * a.val) + 2 * (b.val * b.val) ≤ U32.max) :
    sum_double DoubledShape a b ⦃ r => r.val = 2 * (a.val * a.val) + 2 * (b.val * b.val) ⦄ := by
  let* ⟨ r, r_post ⟩ ← [ -specPreconditions ]
    sum_double_spec (f := fun (x : U32) => 2 * (↑x * ↑x)) (g := fun (x : U32) => 2 * (↑x * ↑x))
  case harea =>
    intros x _
    simp only [step_simps]
    let* ⟨ a, a_post ⟩ ← [ -specPreconditions ] Shape.double_area.default_spec (f := fun (x : U32) => ↑x * ↑x)
    case harea =>
      intros x _
      simp only [step_simps]
      let* ⟨ a, a_post ⟩ ← sq_spec
      agrind
    agrind
  case hdouble =>
    intros x _
    simp only [step_simps]
    let* ⟨ a, a_post ⟩ ← [ -specPreconditions ] Shape.double_area.default_spec (f := fun (x : U32) => ↑x * ↑x)
    case harea =>
      intros x _
      simp only [step_simps]
      let* ⟨ a, a_post ⟩ ← sq_spec
      agrind
    agrind
  agrind

/-! ## A ghost only in the preconditions (`b`) -/

structure Counter (Self : Type) where
  incr : Self → Result Self

@[irreducible]
def Counter.incr_twice {Self : Type} (inst : Counter Self) (x : Self) : Result Self := do
  let y ← inst.incr x
  inst.incr y

@[step]
theorem Counter.incr_twice_spec {Self : Type} (inst : Counter Self) (v : Self → Nat) (b : Nat)
    (hincr : ∀ x, v x < b → inst.incr x ⦃ y => v y = v x + 1 ⦄) (x : Self) (h : v x + 1 < b) :
    Counter.incr_twice inst x ⦃ y => v y = v x + 2 ⦄ := by
  unfold Counter.incr_twice
  step*

def tick (n : U32) : Result U32 := n + 1#u32

@[step]
theorem tick_spec (n : U32) (h : n.val < U32.max) : tick n ⦃ m => m.val = n.val + 1 ⦄ := by
  unfold tick; step*

example (n : U32) (h : n.val + 1 < U32.max) :
    Counter.incr_twice { incr := tick } n ⦃ m => m.val = n.val + 2 ⦄ := by
  step*

/-! ## A ghost instantiated by a constant (`global_simps`) -/

structure HasLen (Self : Type) where
  N : Result U32

@[irreducible]
def HasLen.twice {Self : Type} (inst : HasLen Self) : Result U32 := do
  let n ← inst.N
  2#u32 * n

@[step]
theorem HasLen.twice_spec {Self : Type} (inst : HasLen Self) (n : Nat)
    (hN : inst.N ⦃ r => r.val = n ⦄) (h : 2 * n ≤ U32.max) :
    HasLen.twice inst ⦃ r => r.val = 2 * n ⦄ := by
  unfold HasLen.twice
  step*

@[global_simps, irreducible]
def three : U32 := 3#u32

example : HasLen.twice ({ N := ok three } : HasLen Unit) ⦃ r => r.val = 6 ⦄ := by
  step*

/-! ## A precondition already in context: no `case` -/

/--
info: Try this:

  [apply]     let* ⟨ r, r_post ⟩ ← Shape.double_area.default_spec
    agrind
-/
#guard_msgs in
example (x : U32) (h : 2 * (x.val * x.val) ≤ U32.max)
    (harea : ∀ y : U32, y.val * y.val ≤ U32.max → sq y ⦃ a => a.val = y.val * y.val ⦄) :
    Shape.double_area.default SqShape x ⦃ r => r.val = 2 * (x.val * x.val) ⦄ := by
  step*?

/-! ## Failures: the precondition is left to the user -/
opaque mystery : U32 → Result U32

def MysterySpec : Prop := ∀ y, mystery y ⦃ r => r.val = y.val ⦄

example (x : U32) (hm : MysterySpec) (h : 2 * x.val ≤ U32.max) :
    Shape.double_area.default { area := mystery, double_area := mystery } x
      ⦃ r => r.val = 2 * x.val ⦄ := by
  step*
  case harea =>
    intro y _
    exact hm y

/- A circular specification: no loop. -/
opaque loopy : U32 → Result U32

@[step]
theorem loopy_spec (x : U32) (h : loopy x ⦃ r => r = x ⦄) : loopy x ⦃ r => r = x ⦄ := h

def LoopySpec : Prop := ∀ x, loopy x ⦃ r => r = x ⦄

example (x : U32) (h : LoopySpec) : loopy x ⦃ r => r = x ⦄ := by
  fail_if_success (step*; done)
  exact h x

end spec_preconditions
