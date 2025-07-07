import AeneasMeta.Async.TestTactics

namespace Aeneas.Async.Test

open Lean Elab Tactic Utils

-- This is: `x * y < bound ∧ x * y < bound + 1 ∧ ...` (there are `count` conjuncts)
def goal1 (x y bound count : Nat) : Prop :=
  if count = 0 then True
  else x + y < bound ∧ goal1 x y (bound + 1) (count - 1)

/- Note that when measuring time the variance is quite big -/
--set_option trace.profiler true in
set_option maxRecDepth 2048 in
def test1 (x y : Nat) (h : x < 10) (h : y < 20) : goal1 x y 200 200
  := by
  simp only [goal1, Nat.add_one_ne_zero, ↓reduceIte, Nat.reduceAdd, Nat.add_one_sub_one,
    Nat.sub_self, and_true]
  --sync_solve_omega -- 3.072428s (scalar_tac) -- 0.53 (omega)
  async_solve_omega -- 1.18s (scalar_tac) -- 0.67s (omega) -- 0.23s (no replaceLevel) -- 0.19s (no auxiliary lemma)

--set_option trace.profiler true in
set_option maxRecDepth 2048 in
example : (List.replicate 600 0).length = 600 := by
  simp only [List.reduceReplicate, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] -- 0.32s

def goal2 (length count : Nat) : Prop :=
  if count = 0 then True else (List.replicate length 0).length = length ∧ goal2 length (count - 1)

--set_option trace.profiler true in
set_option maxRecDepth 2048 in
def test2 : goal2 600 20
  := by
  simp only [goal2, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_one_sub_one, Nat.sub_self, and_true]
  --split_conjs <;> simp -- 4.9s for 16 goals, 6.11s for 20 goals
  async_solve_simp -- 1.34s for 16 goals, 1.6s for 20 goals


namespace Aeneas.Async.Test
