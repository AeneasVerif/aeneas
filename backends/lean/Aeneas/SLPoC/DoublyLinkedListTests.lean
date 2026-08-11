import Aeneas.SLPoC.DoublyLinkedListSpec

/-!
# Doubly-linked list: tactic regression tests

Tests that exercise `step` and `sl_frame` on the doubly-linked list.  They check
the tactics, not the list, so they are kept out of
`Aeneas.SLPoC.DoublyLinkedListSpec`: that module is what the LOC comparison of
`Aeneas/SLPoC/README.md` measures against the Verus development.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace FrameInferenceTest

open DoublyLinkedList

/-- Frame inference works when the callee's precondition is an abstract
representation predicate defined as an existential. -/
def twoPushes (s : DoublyLinkedList Nat) : St (DoublyLinkedList Nat) := do
  let s ← pushBack s 1
  pushBack s 2

example (s : DoublyLinkedList Nat) (vs : List Nat) :
    ⦃ isList s vs ⦄ twoPushes s ⦃⇓ s' => isList s' (vs ++ [1] ++ [2])⦄ := by
  unfold twoPushes
  apply triple_step_bind (pushBack s 1) _ (pushBack.isList_spec s vs 1)
  case hPre => sl_frame
  case hNext =>
    intro s1 _
    -- The terminal call goes through the ramified frame rule: a single goal,
    -- with no frame metavariable to guess.
    exact triple_step_mono (pushBack s1 2) _ (pushBack.isList_spec s1 (vs ++ [1]) 2)
      (by sl_frame)

end FrameInferenceTest

end Aeneas.SLPoC
