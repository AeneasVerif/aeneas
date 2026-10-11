module
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.HaveValues

def readAt (l : List Nat) (i : Nat) : Result Nat := ok (l.getD i 0)

theorem readAt.spec (l : List Nat) (i x : Nat) (h : l[i]? = some x) :
    readAt l i ⦃ r => r = x ⦄ := by
  simp [readAt, List.getD_eq_getElem?_getD, h]

/- The values of the `have`s introduced by tactics may mention variables which `subst` eliminated
since then: `step with` must not inline them when normalizing the specification. -/

-- A proof (here, the proof of `h0` uses `hn`)
example (l : List Nat) (n : Nat) (hn : n = l.length) (hpos : 0 < n) :
    (do let a ← readAt l 0; ok a) ⦃ r => r = l[0]'(by omega) ⦄ := by
  have h0 : 0 < l.length := by omega
  subst hn
  step with readAt.spec l 0 (l[0]'h0) (by simp)
  simp [*]

-- Data (the type of the theorem mentions `k`, whose value mentions `n`)
theorem readAt.spec' (l : List Nat) (i : Nat) : readAt l i ⦃ r => r = l.getD i 0 ⦄ := by
  simp [readAt]

example (l : List Nat) (n : Nat) (hn : n = l.length) : True := by
  have k : Nat := n - n
  subst hn
  have : (do let a ← readAt l k; ok a) ⦃ r => r = l.getD k 0 ⦄ := by
    step with readAt.spec' l k
    simp [*]
  trivial

end Aeneas.Tactic.Step.Tests.HaveValues
