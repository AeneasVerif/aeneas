import Aeneas.Do
import Aeneas.Std.Slice
import Aeneas.Tactic.Step

/-! # `introOutputs` tests -/

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.IntroOutputs

def pairProg : Result (Nat × Nat) := ok (1, 2)

@[step]
theorem pairProg_spec : pairProg ⦃ p => p.1 = 1 ∧ p.2 = 2 ⦄ := by
  unfold pairProg; step*

/--
info: Try this:

  [apply]     let* ⟨ p, p_post1, p_post2 ⟩ ← pairProg_spec
    agrind
-/
#guard_msgs in
example : pairProg ⦃ p => p.1 = 1 ∧ p.2 = 2 ⦄ := by
  step*?

/--
info: Try this:

  [apply]     let* ⟨ p, p_post1, p_post2 ⟩ ← pairProg_spec
    agrind
-/
#guard_msgs in
example : (do let p ← pairProg; ok p) ⦃ p => p.1 = 1 ∧ p.2 = 2 ⦄ := by
  step*?

def threeProg : Result (Nat × Nat × Nat) := ok (1, 2, 3)

@[step]
theorem threeProg_spec : threeProg ⦃ a b c => a = 1 ∧ b = 2 ∧ c = 3 ⦄ := by
  unfold threeProg; step*

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3 ⟩ ← threeProg_spec
    agrind
-/
#guard_msgs in
example : threeProg ⦃ a b c => a = 1 ∧ b = 2 ∧ c = 3 ⦄ := by
  step*?

/--
info: Try this:

  [apply]     let* ⟨ x, y, x_post1, x_post2, x_post3 ⟩ ← threeProg_spec
    agrind
-/
#guard_msgs in
example : (do let (x, y) ← threeProg; ok (x + y.1 + y.2)) ⦃ r => r = 6 ⦄ := by
  step*?

def nestedProg : Result ((Nat × Nat) × Nat) := ok ((5, 6), 7)

@[step]
theorem nestedProg_spec : nestedProg ⦃ ((a, b), c) => a = 5 ∧ b = 6 ∧ c = 7 ⦄ := by
  unfold nestedProg; step*

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3 ⟩ ← nestedProg_spec
    agrind
-/
#guard_msgs in
example : nestedProg ⦃ ((a, b), c) => a = 5 ∧ b = 6 ∧ c = 7 ⦄ := by
  step*?

/--
error: unsolved goals
case a
a : ℕ × ℕ
b : ℕ
a_post1 : a.1 = 5
a_post2 : a.2 = 6
a_post3 : b = 7
⊢ a.1 = 5 ∧ a.2 = 6 ∧ b = 7
-/
#guard_msgs in
example : nestedProg ⦃ a b => a.1 = 5 ∧ a.2 = 6 ∧ b = 7 ⦄ := by
  step with nestedProg_spec

/--
info: Try this:

  [apply]     let* ⟨ x, y, x_post1, x_post2, x_post3 ⟩ ← nestedProg_spec
    agrind
-/
#guard_msgs in
example : (do let (x, y) ← nestedProg; ok (x, y)) ⦃ a b => a.1 = 5 ∧ a.2 = 6 ∧ b = 7⦄ := by
  step*?

def quadProg : Result ((Nat × Nat) × (Nat × Nat)) := ok ((8, 9), (10, 11))

/-! ## `quadProg_spec` shape × bind-pattern matrix

`quadProg`'s return type `(Nat × Nat) × (Nat × Nat)` admits several distinct
spec encodings. Below, each section pins a different `quadProg_spec` via a
*scoped* `@[step]` attribute, then runs the same four `do`-block bind patterns
against it. Each cell embeds an arbitrary arithmetic expression involving the
bound variables — this exercises the bind-continuation expansion that `step`'s
call-site-tree extraction reads, and the trailing `agrind` checks the numeric
post-condition.

Every combination should produce the same `let* ⟨ ... ⟩ ← quadProg_spec`
output: the bind let-pattern dictates the destructure depth, and the spec's
own encoding has no influence on it.

The four bind shapes (rows):
- `let (a, b) ← …`            — pair-naming, no nested destructure
- `let ((a, b), c) ← …`       — destructure the left pair only
- `let (a, (b, c)) ← …`       — destructure the right pair only
- `let ((a, b), (c, d)) ← …`  — full destructure

The spec shapes tested (sections):
- `SpecNamed`       — `⦃ a b => a.1 = … ⦄`           (uncurry' only)
- `SpecLeftDestr`   — `⦃ (a, b) c => … ⦄`            (uncurry' + uncurry-left)
- `SpecRightDestr`  — `⦃ a (b, c) => … ⦄`            (uncurry' + uncurry-right)
- `SpecFullDestr`   — `⦃ (a, b) (c, d) => … ⦄`       (uncurry' + uncurry-both)
- `SpecSingleTuple` — `⦃ ((a, b), (c, d)) => … ⦄`    (single binder, nested uncurry)
- `SpecProjection`  — `⦃ p => p.1.1 = … ⦄`           (single binder, no destructure)
-/

namespace SpecNamed
@[scoped step]
theorem quadProg_spec :
    quadProg ⦃ a b => a.1 = 8 ∧ a.2 = 9 ∧ b.1 = 10 ∧ b.2 = 11 ⦄ := by
  unfold quadProg; step*

/--
info: Try this:

  [apply]     let* ⟨ a, b, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by step*?

/--
error: unsolved goals
case a
c : ℕ × ℕ
a b : ℕ
a_post1 : a = 8
a_post2 : b = 9
a_post3 : c.1 = 10
a_post4 : c.2 = 11
⊢ a + b * 2 + c.1 + c.2 = 47
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by
  step with quadProg_spec

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), (c, d)) ← quadProg
              ok (a + b + c * 2 + d)) ⦃ res => res = 48 ⦄ := by step*?
end SpecNamed

namespace SpecLeftDestr
@[scoped step]
theorem quadProg_spec :
    quadProg ⦃ (a, b) c => a = 8 ∧ b = 9 ∧ c.1 = 10 ∧ c.2 = 11 ⦄ := by
  unfold quadProg; step*

/--
error: unsolved goals
case a
a b : ℕ × ℕ
a_post1 : a.1 = 8
a_post2 : a.2 = 9
a_post3 : b.1 = 10
a_post4 : b.2 = 11
⊢ a.1 + a.2 + b.1 + b.2 = 38
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by
  step with quadProg_spec

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), (c, d)) ← quadProg
              ok (a + b + c * 2 + d)) ⦃ res => res = 48 ⦄ := by step*?
end SpecLeftDestr

namespace SpecRightDestr
@[scoped step]
theorem quadProg_spec :
    quadProg ⦃ a (b, c) => a.1 = 8 ∧ a.2 = 9 ∧ b = 10 ∧ c = 11 ⦄ := by
  unfold quadProg; step*

/--
info: Try this:

  [apply]     let* ⟨ a, b, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), (c, d)) ← quadProg
              ok (a + b + c * 2 + d)) ⦃ res => res = 48 ⦄ := by step*?
end SpecRightDestr

namespace SpecFullDestr
@[scoped step]
theorem quadProg_spec :
    quadProg ⦃ (a, b) (c, d) => a = 8 ∧ b = 9 ∧ c = 10 ∧ d = 11 ⦄ := by
  unfold quadProg; step*

/--
info: Try this:

  [apply]     let* ⟨ a, b, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), (c, d)) ← quadProg
              ok (a + b + c * 2 + d)) ⦃ res => res = 48 ⦄ := by step*?
end SpecFullDestr

namespace SpecSingleTuple
@[scoped step]
theorem quadProg_spec :
    quadProg ⦃ ((a, b), (c, d)) => a = 8 ∧ b = 9 ∧ c = 10 ∧ d = 11 ⦄ := by
  unfold quadProg; step*

/--
info: Try this:

  [apply]     let* ⟨ a, b, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), (c, d)) ← quadProg
              ok (a + b + c * 2 + d)) ⦃ res => res = 48 ⦄ := by step*?
end SpecSingleTuple

namespace SpecProjection
@[scoped step]
theorem quadProg_spec :
    quadProg ⦃ p => p.1.1 = 8 ∧ p.1.2 = 9 ∧ p.2.1 = 10 ∧ p.2.2 = 11 ⦄ := by
  unfold quadProg; step*

/--
info: Try this:

  [apply]     let* ⟨ a, b, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post1, a_post2, a_post3, a_post4 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), (c, d)) ← quadProg
              ok (a + b + c * 2 + d)) ⦃ res => res = 48 ⦄ := by step*?
end SpecProjection

-- tests for ∃ in postcondition
def existentialProg : Result (Nat × Nat) := ok (1, 2)

@[step]
theorem existentialProg_spec : existentialProg ⦃ x y => x = 1 ∧ ∃ z, z > 0 ∧ y = z + 1 ⦄ := by
  unfold existentialProg; simp

/--
error: unsolved goals
case a
x y : ℕ
hx : x = 1
z : ℕ
hz : z > 0
h : y = z + 1
⊢ x + y > 2
-/
#guard_msgs in
example : (do let (x, y) ← existentialProg; ok (x + y)) ⦃ res => res > 2 ⦄ := by
  step with existentialProg_spec as ⟨ x, y, hx, z, hz, h ⟩

-- Testing that we don't destructure too far when we don't have to

section

def pred (_ : Nat × Nat) : Prop := True

@[scoped step]
theorem quadProg_spec :
    quadProg ⦃ a b => pred a ∧ pred b ⦄ := by
  unfold quadProg; step*; simp [pred]

/--
error: unsolved goals
case a
a : ℕ × ℕ
b c : ℕ
a_post1 : pred a
a_post2 : pred (b, c)
⊢ a.1 + a.2 + b + c = 38
-/
#guard_msgs in
example :
  (do
     let (a, (b, c)) ← quadProg
     ok (a.1 + a.2 + b + c)) ⦃ res => res = 38 ⦄ := by
  step with quadProg_spec

end
