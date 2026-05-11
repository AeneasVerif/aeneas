import Aeneas.Do
import Aeneas.Std.Slice
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace step_tuple_destruct

def twoNats : Result (Nat × Nat) :=
  ok (1, 2)

@[step]
theorem twoNats_spec : twoNats ⦃ a b => a = 1 ∧ b = 2⦄ := by unfold twoNats; step*

def fourNats : Result ((Nat × Nat) × (Nat × Nat)) :=
  ok ((3, 4), (5, 6))

@[step]
theorem fourNats_spec : fourNats ⦃ (a, b) (c,d) => a = 3 ∧ b = 4 ∧ c = 5 ∧ d = 6⦄ := by
  unfold fourNats; step*

def testTuples : Result Nat := do
  let (a, b) ← twoNats
  let (c, d) ← twoNats
  let ((a, b), (c, d)) ← fourNats
  let ((e, f), (g, h)) ← fourNats
  ok (a + f + g + d)

/--
info: Try this:

  [apply]     let* ⟨ a, b, a_post, b_post ⟩ ← twoNats_spec
    let* ⟨ c, d, c_post, d_post ⟩ ← twoNats_spec
    let* ⟨ a, b, c, d, a_post, b_post, c_post, d_post ⟩ ← fourNats_spec
    let* ⟨ e, f, g, h, e_post, f_post, g_post, h_post ⟩ ← fourNats_spec
    agrind
-/
#guard_msgs in
example : testTuples ⦃ res => res = 18⦄ := by
  unfold testTuples
  step*?

end step_tuple_destruct
