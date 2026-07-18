import Aeneas.Do
import Aeneas.Std.Slice
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.TupleDestruct

private def twoNats : Result (Nat × Nat) :=
  ok (1, 2)

private def threeNats : Result (Nat × Nat × Nat) :=
  ok (1, 2, 3)

@[local step]
private theorem twoNats_spec : twoNats ⦃ a b => a = 1 ∧ b = 2⦄ := by unfold twoNats; step*

@[local step]
private def threeNats_spec : threeNats ⦃ a b c => a = 1 ∧ b = 2 ∧ c = 3⦄ := by unfold threeNats; step*

private def fourNats : Result ((Nat × Nat) × (Nat × Nat)) :=
  ok ((3, 4), (5, 6))

@[local step]
private theorem fourNats_spec : fourNats ⦃ (a, b) (c,d) => a = 3 ∧ b = 4 ∧ c = 5 ∧ d = 6⦄ := by
  unfold fourNats; step*

private def sixNats : Result (((Nat × Nat) × Nat) × ((Nat × Nat) × Nat)) :=
  ok (((3, 4), 5), ((6, 7), 8))

@[local step]
private theorem sixNats_spec : sixNats ⦃ ((a, b), c) ((d, e), f) => a = 3 ∧ b = 4 ∧ c = 5 ∧ d = 6 ∧ e = 7 ∧ f = 8⦄ := by
  unfold sixNats; step*

/--
warning: Variable name `a` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `b` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `c` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `d` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `b` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `c` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `e` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `h` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
private def testTuples : Result Nat := do
  let (a, b) ← twoNats
  let (c, d) ← twoNats
  let ((a, b), (c, d)) ← fourNats
  let ((e, f), (g, h)) ← fourNats
  ok (a + f + g + d)

/--
info: Try this:

  [apply]     let* ⟨ a, b, a_post1, a_post2 ⟩ ← twoNats_spec
    let* ⟨ c, d, c_post1, c_post2 ⟩ ← twoNats_spec
    let* ⟨ a, b, c, d, a_post1, a_post2, a_post3, a_post4 ⟩ ← fourNats_spec
    let* ⟨ e, f, g, h, e_post1, e_post2, e_post3, e_post4 ⟩ ← fourNats_spec
    agrind
-/
#guard_msgs in
example : testTuples ⦃ res => res = 18⦄ := by
  unfold testTuples
  step*?

private def testTuples1 : Result Nat := do
  let (a, b, c) ← threeNats
  let (e, f, g) ← threeNats
  ok (a + b + c + e + f + g)

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, a_post1, a_post2, a_post3 ⟩ ← threeNats_spec
    let* ⟨ e, f, g, e_post1, e_post2, e_post3 ⟩ ← threeNats_spec
    agrind
-/
#guard_msgs in
example : testTuples1 ⦃ res => res = 12⦄ := by
  unfold testTuples1
  step*?

private def testTuples2 : Result Nat := do
  let (((a, b), c), ((d, e), f)) ← sixNats
  ok (a + b + c + d + e + f)

/--
info: Try this:

  [apply]     let* ⟨ a, b, c, d, e, f, a_post1, a_post2, a_post3, a_post4, a_post5, a_post6 ⟩ ← sixNats_spec
    agrind
-/
#guard_msgs in
example : testTuples2 ⦃ res => res = 33⦄ := by
  unfold testTuples2
  step*?

/-! ## Grouped binders in postconditions

Several names sharing one type ascription — `(a b c : Nat)` — expand to one
product component per name, exactly as if the binders were written separately.
Arity is irrelevant, and tuple *pattern* binders `(⟨…⟩ : T)` are unaffected. -/

private def fiveNats : Result (Nat × Nat × Nat × Nat × Nat) :=
  ok (1, 2, 3, 4, 5)

/-- A single grouped binder covering every component. -/
example :
    fiveNats ⦃ (a b c d e : Nat) => a = 1 ∧ b = 2 ∧ c = 3 ∧ d = 4 ∧ e = 5 ⦄ := by
  unfold fiveNats; step*

/-- A grouped binder mixed with a bare binder and a smaller group. -/
example :
    fiveNats ⦃ a (b c : Nat) d e => a = 1 ∧ b = 2 ∧ c = 3 ∧ d = 4 ∧ e = 5 ⦄ := by
  unfold fiveNats; step*

/-- Grouping is independent of arity. -/
example :
    threeNats ⦃ (a b c : Nat) => a = 1 ∧ b = 2 ∧ c = 3 ⦄ := by
  unfold threeNats; step*

/-- Regression guard: a tuple *pattern* binder `(⟨…⟩ : T)` is NOT a grouped
binder — its names destructure a single component, not one component each. -/
example :
    fiveNats ⦃ (⟨a, b, c, d, e⟩ : Nat × Nat × Nat × Nat × Nat) =>
      a = 1 ∧ b = 2 ∧ c = 3 ∧ d = 4 ∧ e = 5 ⦄ := by
  unfold fiveNats; step*

private def natsAndBools : Result (Nat × Nat × Bool × Bool) :=
  ok (1, 2, true, false)

/-- A single grouped binder covering every component. -/
@[local step]
example :
    natsAndBools ⦃ (a b : Nat) (c d : Bool) => a = 1 ∧ b = 2 ∧ c = true ∧ d = false ⦄ := by
  unfold natsAndBools; step*

end Aeneas.Tactic.Step.Tests.TupleDestruct
