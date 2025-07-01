import Aeneas.Progress.Async

-- This is: `x * y < bound ∧ x * y < bound + 1 ∧ ...` (there are `count` conjuncts)
def goal (x y bound count : Nat) : Prop :=
  if count = 0 then True
  else x * y < bound ∧ goal x y (bound + 1) (count - 1)

/- Note that when measuring time the variance is quite big -/
--set_option trace.profiler true in
set_option maxRecDepth 2048 in
def test (x y : Nat) (h : x < 10) (h : y < 20) : goal x y 200 200
  := by
  simp [goal]
  sync_solve -- 3.072428s
  --async_solve -- 1.720408s
