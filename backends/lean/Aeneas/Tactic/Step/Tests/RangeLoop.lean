import Aeneas.Std
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result ControlFlow WP

namespace range_loop_test

/-- Regression for `IteratorRange.next_StepUsize_spec`: a range-`for` loop
    (`for _ in r {}`, the `loop` + `next` shape Aeneas extracts) is total, proven
    by `step` auto-applying the `@[step]` `next` spec — no hand-written `next`
    lemma. Aeneas extracts range loops but the suite otherwise proves none. -/
example (r : core.ops.range.Range Usize) :
    loop (fun iter => do
      let (o, iter') ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok (ControlFlow.done ())
      | some _ => ok (ControlFlow.cont iter')) r
    ⦃ (_ : Unit) => True ⦄ := by
  apply loop.spec_decr_nat (measure := fun s => s.«end».val - s.start.val) (inv := fun _ => True)
  · intro s _
    step as ⟨o, iter2, hpost⟩
    by_cases h : s.start.val < s.«end».val
    · obtain ⟨ho, hstart, hend⟩ := by simpa only [h, if_true] using hpost
      simp only [ho, WP.spec_ok, hstart, hend]
      scalar_tac
    · obtain ⟨ho, -⟩ := by simpa only [h, if_false] using hpost
      simp only [ho, WP.spec_ok]
  · trivial

end range_loop_test
