import Aeneas
open Aeneas Aeneas.Std Result

namespace IterFoldSpec

def descendingNext (n : Nat) : Result (Option Nat × Nat) :=
  if n = 0 then ok (none, n) else ok (some n, n - 1)

def descendingPost (n : Nat) (r : Option Nat × Nat) : Prop :=
  if n = 0 then r = (none, n) else r = (some n, n - 1)

@[step]
theorem descendingNext.spec (n : Nat) :
    descendingNext n ⦃ descendingPost n ⦄ := by
  by_cases h : n = 0 <;> simp [descendingNext, descendingPost, h, WP.spec_ok]

def countStep : core.ops.function.FnMut Unit (Nat × Nat) Nat := {
  FnOnceInst := { call_once := fun _ (acc, _) => ok (acc + 1) }
  call_mut := fun _ (acc, _) => ok (acc + 1, ())
}

def descendingInst : core.iter.traits.iterator.Iterator Nat Nat := {
  next := descendingNext
}

theorem fold_countdown (n acc target : Nat) (h : acc + n = target) :
    descendingInst.fold countStep n acc () ⦃ r => r = target ⦄ := by
  change core.iter.traits.iterator.Iterator.fold.trait_default
    descendingInst countStep n acc () ⦃ r => r = target ⦄
  apply core.iter.traits.iterator.Iterator.fold.trait_default.spec_decr_nat
    descendingInst countStep n acc ()
    (fun s => s.1)
    (fun s => s.2.1 + s.1 = target)
    (fun r => r = target)
  · intro s hs
    rcases s with ⟨n, acc, ⟨⟩⟩
    have hn : descendingInst.next n ⦃ descendingPost n ⦄ := descendingNext.spec n
    have hc : ∀ x n1, descendingPost n (some x, n1) →
        countStep.call_mut () (acc, x) ⦃ r => r = (acc + 1, ()) ⦄ := by
      intro x n1 _
      simp [countStep, WP.spec_ok]
    have hb := core.iter.traits.iterator.Iterator.fold.default.body.spec
      descendingInst.next countStep n acc ()
      (descendingPost n) (fun _ r => r = (acc + 1, ())) hn hc
    apply WP.spec_mono hb
    intro r hr
    rcases hr with ⟨o, n1, hn1, hr⟩
    cases n with
    | zero =>
      simp [descendingPost] at hn1
      rcases hn1 with ⟨ho, hn1⟩
      subst o
      subst n1
      simp at hr
      cases hr
      simpa using hs
    | succ k =>
      simp [descendingPost] at hn1
      rcases hn1 with ⟨ho, hn1⟩
      subst o
      subst n1
      simp at hr
      rcases hr with ⟨f1, hresult⟩
      cases hresult
      simp at hs ⊢
      omega
  · exact h

end IterFoldSpec
