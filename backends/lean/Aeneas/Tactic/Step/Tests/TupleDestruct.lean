import Aeneas.Do
import Aeneas.Std.Slice
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace step_tuple_destruct

/- A function that returns a pair, then destructures it -/
def getPairAndUse (x : U32) : Result U32 := do
  let pair ← do
    let a ← x + 1#u32
    ok (a, x)
  let (a, _b) := pair
  a + 1#u32

@[step]
theorem getPairAndUse_step (x : U32) (h : x.val + 2 ≤ U32.max) :
    getPairAndUse x ⦃ r => r.val = x.val + 2 ⦄ := by
  unfold getPairAndUse
  step*

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

  [apply]     simp only [step_simps]
    let* ⟨ a, b, a_post1, a_post2 ⟩ ← twoNats_spec
    let* ⟨ c, d, c_post1, c_post2 ⟩ ← twoNats_spec
    let* ⟨ a, c, a_post ⟩ ← fourNats_spec
    let* ⟨ e, g, e_post ⟩ ← fourNats_spec
    agrind
-/
#guard_msgs in
example : testTuples ⦃ res => res = 18⦄ := by
  unfold testTuples
  step*?

end step_tuple_destruct
