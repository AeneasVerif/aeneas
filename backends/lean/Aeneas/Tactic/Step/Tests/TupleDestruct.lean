import Aeneas.Do
import Aeneas.Std.Slice
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace step_tuple_destruct

def twoNats : Result (Nat × Nat) :=
  ok (1, 2)

def threeNats : Result (Nat × Nat × Nat) :=
  ok (1, 2, 3)

@[step]
theorem twoNats_spec : twoNats ⦃ a b => a = 1 ∧ b = 2⦄ := by unfold twoNats; step*

@[step]
def threeNats_spec : threeNats ⦃ a b c => a = 1 ∧ b = 2 ∧ c = 3⦄ := by unfold threeNats; step*

def fourNats : Result ((Nat × Nat) × (Nat × Nat)) :=
  ok ((3, 4), (5, 6))

@[step]
theorem fourNats_spec : fourNats ⦃ (a, b) (c,d) => a = 3 ∧ b = 4 ∧ c = 5 ∧ d = 6⦄ := by
  unfold fourNats; step*

def sixNats : Result (((Nat × Nat) × Nat) × ((Nat × Nat) × Nat)) :=
  ok (((3, 4), 5), ((6, 7), 8))

@[step]
theorem sixNats_spec : sixNats ⦃ ((a, b), c) ((d, e), f) => a = 3 ∧ b = 4 ∧ c = 5 ∧ d = 6 ∧ e = 7 ∧ f = 8⦄ := by
  unfold sixNats; step*

def testTuples : Result Nat := do
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

def testTuples1 : Result Nat := do
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

def testTuples2 : Result Nat := do
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

end step_tuple_destruct
