module
import Aeneas.Std
import Aeneas.Tactic.Step

namespace Aeneas.Tactic.Step.Tests.RangeLoop

open Aeneas.Std Result ControlFlow WP

/-- Count the visits of the `loop`/`next` shape generated for a range-for loop. -/
def count (r : core.ops.range.Range Usize) : Result Nat :=
  loop (fun (state : core.ops.range.Range Usize × Nat) => do
    let (item, r') ← core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1
    match item with
    | none => ok (done state.2)
    | some _ => ok (cont (r', state.2 + 1))) (r, 0)

/-- `step` applies the library spec; the loop terminates with the exact visit count. -/
theorem count_spec (r : core.ops.range.Range Usize) :
    count r ⦃ n => n = r.«end».val - r.start.val ⦄ := by
  unfold count
  apply loop.spec_decr_nat
    (measure := fun s => s.1.«end».val - s.1.start.val)
    (inv := fun s => s.2 + (s.1.«end».val - s.1.start.val)
      = r.«end».val - r.start.val)
  · intro state hinv
    step as ⟨item, r', hpost, hstop⟩
    by_cases h : state.1.start.val < state.1.«end».val
    · obtain ⟨hitem, hstart⟩ := by simpa only [h, ite_true] using hpost
      simp only [hitem, WP.spec_ok]
      constructor <;> simp only [hstart, hstop] <;> omega
    · obtain ⟨hitem, _⟩ := by simpa only [h, ite_false] using hpost
      simp only [hitem, WP.spec_ok]
      omega
  · simp

example : count { start := 0#usize, «end» := 0#usize } ⦃ n => n = 0 ⦄ := by
  simpa using count_spec { start := 0#usize, «end» := 0#usize }

example : count { start := 3#usize, «end» := 1#usize } ⦃ n => n = 0 ⦄ := by
  simpa using count_spec { start := 3#usize, «end» := 1#usize }

example : count { start := 1#usize, «end» := 4#usize } ⦃ n => n = 3 ⦄ := by
  simpa using count_spec { start := 1#usize, «end» := 4#usize }

/-- The last inhabited range increments to `usize::MAX`, without wrapping. -/
example : count
    { start := Usize.ofNatCore (Usize.max - 1) (by scalar_tac),
      «end» := Usize.ofNatCore Usize.max (by scalar_tac) } ⦃ n => n = 1 ⦄ := by
  apply WP.spec_mono (count_spec _)
  intro n hn
  change n = Usize.max - (Usize.max - 1) at hn
  scalar_tac

end Aeneas.Tactic.Step.Tests.RangeLoop
