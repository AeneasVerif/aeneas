module
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

  [apply]     let* ⟨ p, p_post, p_post1 ⟩ ← pairProg_spec
    agrind
-/
#guard_msgs in
example : pairProg ⦃ p => p.1 = 1 ∧ p.2 = 2 ⦄ := by
  step*?

/--
info: Try this:

  [apply]     let* ⟨ p, p_post, p_post1 ⟩ ← pairProg_spec
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

  [apply]     let* ⟨ a, b, c, a_post, b_post, c_post ⟩ ← threeProg_spec
    agrind
-/
#guard_msgs in
example : threeProg ⦃ a b c => a = 1 ∧ b = 2 ∧ c = 3 ⦄ := by
  step*?

/--
info: Try this:

  [apply]     let* ⟨ x, y, x_post, x_post1, x_post2 ⟩ ← threeProg_spec
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

  [apply]     let* ⟨ a, b, c, a_post, b_post, c_post ⟩ ← nestedProg_spec
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
a_post : a.1 = 5
a_post1 : a.2 = 6
b_post : b = 7
⊢ a.1 = 5 ∧ a.2 = 6 ∧ b = 7
-/
#guard_msgs in
example : nestedProg ⦃ a b => a.1 = 5 ∧ a.2 = 6 ∧ b = 7 ⦄ := by
  step with nestedProg_spec

/--
info: Try this:

  [apply]     let* ⟨ x, y, x_post, x_post1, y_post ⟩ ← nestedProg_spec
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

  [apply]     let* ⟨ a, b, a_post, a_post1, a_post2, a_post3 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by step*?

/--
error: unsolved goals
case a
a b : ℕ
c : ℕ × ℕ
a_post : a = 8
b_post : b = 9
a_post1 : c.1 = 10
a_post2 : c.2 = 11
⊢ a + b * 2 + c.1 + c.2 = 47
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by
  step with quadProg_spec

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, a_post1, b_post, c_post ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post, b_post, c_post, d_post ⟩ ← quadProg_spec
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
a_post : a.1 = 8
a_post1 : a.2 = 9
a_post2 : b.1 = 10
a_post3 : b.2 = 11
⊢ a.1 + a.2 + b.1 + b.2 = 38
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by
  step with quadProg_spec

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, b_post, a_post1, a_post2 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, a_post1, b_post, c_post ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post, b_post, c_post, d_post ⟩ ← quadProg_spec
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

  [apply]     let* ⟨ a, b, a_post, a_post1, a_post2, a_post3 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, b_post, a_post1, a_post2 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, a_post1, b_post, c_post ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post, b_post, c_post, d_post ⟩ ← quadProg_spec
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

  [apply]     let* ⟨ a, b, a_post, a_post1, a_post2, a_post3 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, b_post, a_post1, a_post2 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, a_post1, b_post, c_post ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post, b_post, c_post, d_post ⟩ ← quadProg_spec
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

  [apply]     let* ⟨ a, b, a_post, a_post1, a_post2, a_post3 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, b_post, a_post1, a_post2 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, a_post1, b_post, c_post ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post, b_post, c_post, d_post ⟩ ← quadProg_spec
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

  [apply]     let* ⟨ a, b, a_post, a_post1, a_post2, a_post3 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, b) ← quadProg
              ok (a.1 + a.2 + b.1 + b.2)) ⦃ res => res = 38 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, b_post, a_post1, a_post2 ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let ((a, b), c) ← quadProg
              ok (a + b * 2 + c.1 + c.2)) ⦃ res => res = 47 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, a_post1, b_post, c_post ⟩ ← quadProg_spec
    agrind
-/
#guard_msgs in
example : (do let (a, (b, c)) ← quadProg
              ok (a.1 + a.2 * 3 + b + c)) ⦃ res => res = 56 ⦄ := by step*?

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, a_post, b_post, c_post, d_post ⟩ ← quadProg_spec
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

/- Outputs must precede existentially quantified variables, including when using nested tuples. -/
def nestedExistentialProg : Result ((Nat × Nat) × Nat) := ok ((1, 2), 3)

@[step]
theorem nestedExistentialProg_spec :
    nestedExistentialProg ⦃ (a, b) c => ∃ (_ : a = 1), b = 2 ∧ c = 3 ⦄ := by
  constructor
  simp

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post, b_post, c_post ⟩ ← nestedExistentialProg_spec
    agrind
-/
#guard_msgs in
example :
    (do let ((a, b), c) ← nestedExistentialProg; ok (a + b + c)) ⦃ x => x = 6 ⦄ := by
  step*?

/--
error: unsolved goals
case a
a b c : ℕ
ha : a = 1
hb : b = 2
hc : c = 3
⊢ a + b + c = 6
-/
#guard_msgs in
example :
    (do let ((a, b), c) ← nestedExistentialProg; ok (a + b + c)) ⦃ x => x = 6 ⦄ := by
  step with nestedExistentialProg_spec as ⟨ a, b, c, ha, hb, hc ⟩

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
a_post : pred a
a_post1 : pred (b, c)
⊢ a.1 + a.2 + b + c = 38
-/
#guard_msgs in
example :
  (do
     let (a, (b, c)) ← quadProg
     ok (a.1 + a.2 + b + c)) ⦃ res => res = 38 ⦄ := by
  step with quadProg_spec

end

/- Abbreviations can be inspected using reducible transparency. -/
abbrev NestedOutput := (Nat × Nat) × Nat

example (f : Result NestedOutput) (h : f ⦃ ((a, b), c) => a = 1 ∧ b = 2 ∧ c = 3 ⦄) :
    (do let ((a, b), c) ← f; ok (a + b + c)) ⦃ r => r = 6 ⦄ := by
  step with h as ⟨a, b, c, ha, hb, hc⟩
  simp [ha, hb, hc]

def genericPair {α : Type u} (x : α) : Result (α × Nat) := ok (x, 1)

@[step]
theorem genericPair_spec {α : Type u} (x : α) :
    genericPair x ⦃ (y : α) (k : Nat) => y = x ∧ k = 1 ⦄ := by
  unfold genericPair
  step*

example {α : Type u} (x : α) :
    (do let (y, k) ← genericPair x; ok (y, k + 1))
      ⦃ (y : α) (k : Nat) => y = x ∧ k = 2 ⦄ := by
  step*

/- Output binder types retain local let-bound variables. -/
example {α : Type u} (m : Nat) :
    let n := m + 1
    let size := n + 1
    ∀ x : Vector α size,
      (do let (y, k) ← genericPair x; ok (y, k + 1))
        ⦃ y k => y = x ∧ k = 2 ⦄ := by
  intro n size x
  step with genericPair_spec as ⟨y, k, hy, hk⟩
  guard_hyp y :ₛ Vector α size
  simp [hy, hk]

/- Test with the partial correctness predicate. -/
example :
    (do let ((a, b), c) ← nestedProg; ok (a + b + c))
      ⦃ (r : Nat) => r = 18 ⦄div := by
  step with nestedProg_spec as ⟨a, b, c, ha, hb, hc⟩
  simp [ha, hb, hc]

/- Outputs of type unit disappear even when the postcondition uses them explicitly. -/
def unitProg : Result Unit := ok ()

@[step]
theorem unitProg_spec : unitProg ⦃ (u : Unit) => u = () ⦄ := by
  unfold unitProg
  step*

abbrev UnitOutput := Unit

/- We preserve the anonymous name slots -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let post ← Lean.Elab.Term.elabTerm (← `(fun (_ : Unit) => True)) none
  let names ← Aeneas.Step.getPostNames post
  unless names == #[none] do
    throwError "Expected an anonymous name slot, got {names}"

example (f : Result UnitOutput) (h : f ⦃ (u : UnitOutput) => u = () ⦄) :
    (do let _ ← f; genericPair 5) ⦃ y k => y = 5 ∧ k = 1 ⦄ := by
  step with h as ⟨⟩
  step*

example : (do let _ ← unitProg; genericPair 5) ⦃ y k => y = 5 ∧ k = 1 ⦄ := by
  step*

example (g : Unit → Result Nat) (hg : ∀ u, g u ⦃ (n : Nat) => n = 0 ⦄) :
    (do let u ← unitProg; g u) ⦃ (n : Nat) => n = 0 ⦄ := by
  step with unitProg_spec
  step with hg as ⟨n, hn⟩
  exact hn

/- Outputs of type unit get eliminated, even when they are used in the post-condition. -/
example (f : Result (Bool × Unit)) (h : f ⦃ b u => b = true ∧ u = () ⦄)
    (g : Bool → Unit → Result Nat)
    (hg : ∀ b u, g b u ⦃ n => n = 0 ⦄) :
    (do let (b, u) ← f; g b u) ⦃ n => n = 0 ⦄ := by
  step with h as ⟨b, hb⟩
  guard_hyp b : Bool
  guard_hyp hb : b = true
  step with hg as ⟨n, hn⟩
  exact hn

example (f : Result ((Unit × Nat) × (Bool × Unit)))
    (h : f ⦃ ((u, n), (b, v)) => u = () ∧ n = 1 ∧ b = true ∧ v = () ⦄) :
    (do let ((_, n), (b, _)) ← f; ok (n, b)) ⦃ n b => n = 1 ∧ b = true ⦄ := by
  step with h as ⟨n, b, hn, hb⟩
  guard_hyp n : Nat
  guard_hyp b : Bool
  simp [hn, hb]

/- Inferred names skip outputs of type unit; they must not become postcondition names. -/
example (f : Result ((Unit × Nat) × (Bool × Unit)))
    (h : f ⦃ ((u, n), (b, v)) => u = () ∧ n = 1 ∧ b = true ∧ v = () ⦄) :
    (do let ((u, n), (b, v)) ← f; ok (u, n, b, v))
      ⦃ u n b v => u = () ∧ n = 1 ∧ b = true ∧ v = () ⦄ := by
  step with h
  guard_hyp n : Nat
  guard_hyp b : Bool
  guard_hyp n_post : n = 1
  guard_hyp b_post : b = true
  simp [n_post, b_post]

/- Quantifiers belonging to the final goal must remain for the caller to introduce. -/
example (f : Result Nat) (h : f ⦃ n => n = 0 ⦄) :
    (do let n ← f; ok n) ⦃ n => ∀ k : Nat, n + k = k ⦄ := by
  step with h as ⟨n, hn⟩
  intro k
  simp [hn]

/- Instantiating a Boolean input with `true` must not leave `True ∧ P` inside an iff. -/
example (f : Bool → Result Bool) (P : Prop)
    (h : ∀ valid, f valid ⦃ b => b = true ↔ valid = true ∧ P ⦄) :
    f true ⦃ b => b = true ↔ P ⦄ := by
  step with h as ⟨b, hb⟩
  guard_hyp hb : b = true ↔ P
  exact hb

/- We normalize equality-defined existentials below matches, without reordering tuple outputs. -/
example (f : Result (Nat × Bool)) (compute : Nat → Nat) (P R : Nat → Prop)
    (hR : ∀ k, R k)
    (h : f ⦃ n b => match b with
      | true => ∃ s, s = compute n ∧ P s
      | false => True ⦄) :
    (do let (n, b) ← f; ok (n, b))
      ⦃ n b => ∀ k : Nat, b = true → P (compute n) ∧ R k ⦄ := by
  step with h as ⟨n, b, hp⟩
  guard_hyp n : Nat
  guard_hyp b : Bool
  guard_hyp hp : match b with | true => P (compute n) | false => True
  intro k hb
  simp [hb] at hp
  exact ⟨hp, hR k⟩

/- Even a trivial postcondition must preserve the output and leave final quantifiers alone. -/
example (f : Result Nat) (R : Nat → Prop) (hR : ∀ k, R k)
    (h : f ⦃ _ => True ∧ True ⦄) :
    (do let n ← f; ok n) ⦃ _ => ∀ k : Nat, R k ⦄ := by
  step with h as ⟨n⟩
  guard_hyp n : Nat
  intro k
  exact hR k

example (f : Bool → Result Bool) (P : Prop)
    (h : ∀ valid, f valid ⦃ b => b = true ↔ valid = true ∧ P ⦄div) :
    (do let b ← f true; ok b) ⦃ b => b = true ↔ P ⦄div := by
  step with h as ⟨b, hb⟩
  guard_hyp hb : b = true ↔ P
  simpa only [WP.dspec_ok] using hb

/- Normalization must preserve even unused outputs and simplifiable final postconditions.
Also check native implications, as used by custom WPs. -/
abbrev normalizationFinalGoal (n : Nat) : Prop := (True ∧ True) → ∀ k : Nat, k = n

run_cmd Lean.Elab.Command.liftTermElabM do
  let cases ← #[
    (← `(∀ n : Nat, (True ∧ True) → (∀ k : Nat, True ∧ k = n)),
     ← `(∀ n : Nat, True → (∀ k : Nat, True ∧ k = n))),
    (← `(∀ _ : Nat, (False ∧ True) → (∀ _ : Nat, True ∧ True)),
     ← `(∀ _ : Nat, False → (∀ _ : Nat, True ∧ True))),
    (← `(∀ n : Nat, (True ∧ n = 0) → (∀ k : Nat, True ∧ k = n)),
     ← `(∀ n : Nat, n = 0 → (∀ k : Nat, True ∧ k = n))),
    (← `(∀ n : Nat, normalizationFinalGoal n),
     ← `(∀ n : Nat, normalizationFinalGoal n)),
    (← `(∀ h : True ∧ True, h.1 = h.2),
     ← `(∀ h : True ∧ True, h.1 = h.2))
  ].mapM fun (input, expected) => do
    return (← Lean.Elab.Term.elabTerm input none, ← Lean.Elab.Term.elabTerm expected none)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  for (input, expected) in cases do
    let input ← Lean.instantiateMVars input
    let expected ← Lean.instantiateMVars expected
    let target ← Aeneas.Step.simpOutputPost input
    unless target == expected do
      throwError "Unexpected normalized output target:\n{target}\nExpected:\n{expected}"

def dup (n : Nat) : Result (Nat × Nat) := ok (n, n)

def id' (n : Nat) : Result Nat := ok n

@[local step]
theorem id'_spec (n : Nat) : id' n ⦃ r => r = n ⦄ := by simp [id']

def bundled (compute : Nat → Nat × Nat) (n : Nat) : Result (Nat × Nat) :=
  ok (compute n)

@[local step]
theorem bundled_spec (compute : Nat → Nat × Nat) (n : Nat) :
    bundled compute n ⦃ a b =>
      let (x, y) := compute n
      a = x ∧ b = y ⦄ := by
  simp [bundled, Aeneas.Std.WP.uncurry']

example (compute : Nat → Nat × Nat) (n : Nat) :
    (do let (a, b) ← bundled compute n; ok (a, b)) ⦃ out => out = compute n ⦄ := by
  step as ⟨a, b, h⟩
  guard_hyp h : a = (compute n).1 ∧ b = (compute n).2
  obtain ⟨ha, hb⟩ := h
  exact Prod.ext ha hb

/- Facts which become trivial after instantiation are kept. -/
def conditional (bound : U32) : Result Bool := ok (bound.val = bound.val)

@[local step]
theorem conditional_spec (bound : U32) :
    conditional bound ⦃ result => bound.val = 0 → result = true ⦄ := by
  simp [conditional]

example : conditional 0#u32 ⦃ result => result = true ⦄ := by
  step as ⟨result, h⟩
  guard_hyp h : True → result = true
  exact h trivial

/-! ### Leading existentials of a postcondition come after the outputs -/

theorem dup_witness_spec (n : Nat) :
    dup n ⦃ a b => ∃ (w : Bool) (k : Nat), a = n + k ∧ b = n ∧ w = (k == 0) ⦄ := by
  simp [dup, Aeneas.Std.WP.uncurry']

example (n : Nat) :
    (do let (a, b) ← dup n; ok (a, b)) ⦃ _ b => b = n ⦄ := by
  step with dup_witness_spec as ⟨a, b, w, k, ha, hb, hw⟩
  guard_hyp a : Nat
  guard_hyp b : Nat
  guard_hyp w : Bool
  guard_hyp k : Nat
  guard_hyp ha : a = n + k
  guard_hyp hb : b = n
  guard_hyp hw : w = (k == 0)
  exact hb

example (f : Result (Nat × Nat × Nat))
    (h : f ⦃ p =>
      ∃ witness : Bool × Nat, p.1 = witness.1.toNat ∧ p.2.1 = witness.2 ∧ p.2.1 = p.2.2 ⦄) :
    (do let (a, b, c) ← f; ok (a, b, c)) ⦃ _ b c => b = c ⦄ := by
  let* ⟨a, b, c, witness, ha, hb, hbc⟩ ← h
  guard_hyp witness : Bool × Nat
  guard_hyp ha : a = witness.1.toNat
  guard_hyp hb : b = witness.2
  exact hbc

example (f : Result Unit) (h : f ⦃ _ => ∃ witness : Nat, witness > 0 ⦄) :
    f ⦃ _ => ∃ witness : Nat, witness > 0 ⦄ := by
  let* ⟨witness, hw⟩ ← h
  guard_hyp witness : Nat
  guard_hyp hw : witness > 0
  exact ⟨witness, hw⟩

example (f : Result (Nat × Nat))
    (h : f ⦃ p => ∃ witness : Bool, p.1 = witness.toNat ∧ p.1 = p.2 ⦄div) :
    (do let (a, b) ← f; ok (a, b)) ⦃ a b => a = b ⦄div := by
  let* ⟨a, b, witness, hw, hab⟩ ← h
  guard_hyp witness : Bool
  guard_hyp hw : a = witness.toNat
  simpa using hab

example (f : Result (List Nat)) (n : Nat)
    (h : f ⦃ result => ∃ hlen : result.length = n, n = result.length ∧ hlen = hlen ⦄) :
    f ⦃ result => result.length = n ⦄ := by
  step with h as ⟨result, hlen, hlen'⟩
  guard_hyp result : List Nat
  guard_hyp hlen : result.length = n
  guard_hyp hlen' : n = result.length
  exact hlen

/-! ### Facts about existential witnesses are named after the binder

The facts about the witness of `∃ s, …` are named `s_post`, `s_post1`, ... -/

theorem dup_nested_spec (n : Nat) :
    dup n ⦃ a b => a = n ∧ ∃ s, s ≥ a ∧ s = a + b ∧ b = n ⦄ := by
  simp [dup, Aeneas.Std.WP.uncurry']

example (n : Nat) :
    (do let (a, b) ← dup n; ok (a + b)) ⦃ r => r = n + n ⦄ := by
  step with dup_nested_spec
  guard_hyp s : Nat
  guard_hyp s_post : s ≥ a
  guard_hyp s_post1 : s = a + b
  guard_hyp b_post : b = n
  simp [a_post, b_post]

/-! ### The facts and the postcondition of the goal are normalized

Conjunctive and existential premises are curried, and `True` premises are dropped. -/

theorem id'_curried_spec (n : Nat) : id' n ⦃ r => ∀ j, (_h : j ≤ r ∧ r ≤ j) → j = n ⦄ := by
  simp only [id', WP.spec_ok]
  intro j h
  agrind

example (n : Nat) : (do let r ← id' n; ok r) ⦃ r => r = n ⦄ := by
  step with id'_curried_spec as ⟨r, h⟩
  exact h r (Nat.le_refl r) (Nat.le_refl r)

example (n : Nat) :
    (do let r ← id' n; id' r)
      ⦃ r => True → ∀ j, (_h : j ≤ r ∧ r ≤ j) → (∃ k, k + j = r) → j = n ⦄ := by
  step
  apply WP.spec_mono (id'_spec r)
  intro r' hr' j h1 h2 k hk
  guard_hyp h1 : j ≤ r'
  guard_hyp h2 : r' ≤ j
  guard_hyp hk : k + j = r'
  agrind

example (r : core.result.Result Never Nat) (e : Nat) (hr : r = .Err e) :
    (do
      let out ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame Nat) r
      ok (out, ()))
      ⦃ status state =>
        match status with
        | .Ok _ => False
        | .Err error => error = e ∧ state = () ⦄ := by
  step*
