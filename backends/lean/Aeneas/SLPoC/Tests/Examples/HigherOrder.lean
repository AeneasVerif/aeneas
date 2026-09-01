import Aeneas.SLPoC.RustHeap

/-!
# Higher-order callback specification

This example verifies a higher-order function without unfolding its callback.
The callback's specification describes how it transforms an owned cell, and
`applyTwice` uses that specification at each call site.
-/

namespace Aeneas.SLPoC


namespace HigherOrder

def CallbackSpec (callback : Ptr Nat → St Unit) (transform : Nat → Nat) : Prop :=
  ∀ pointer value,
    ⦃ pointer ↦ value ⦄ callback pointer
      ⦃⇓ pointer ↦ transform value⦄

def applyTwice (callback : Ptr Nat → St Unit) (pointer : Ptr Nat) : St Unit := do
  callback pointer
  callback pointer

@[step]
theorem applyTwice.spec (callback : Ptr Nat → St Unit) (transform : Nat → Nat)
    (pointer : Ptr Nat) (value : Nat)
    (callbackSpec : CallbackSpec callback transform) :
    ⦃ pointer ↦ value ⦄ applyTwice callback pointer
      ⦃⇓ pointer ↦ transform (transform value)⦄ := by
  unfold applyTwice
  step with callbackSpec pointer value
  exact callbackSpec pointer (transform value)

def increment (pointer : Ptr Nat) : St Unit := do
  let value ← read pointer
  update pointer (value + 1)

theorem increment.spec : CallbackSpec increment (fun value => value + 1) := by
  unfold CallbackSpec
  intro pointer value
  unfold increment
  step*

def incrementTwice (pointer : Ptr Nat) : St Unit :=
  applyTwice increment pointer

theorem incrementTwice.spec (pointer : Ptr Nat) (value : Nat) :
    ⦃ pointer ↦ value ⦄ incrementTwice pointer
      ⦃⇓ pointer ↦ (value + 1) + 1⦄ := by
  unfold incrementTwice
  exact applyTwice.spec increment (fun current => current + 1)
    pointer value increment.spec

/-! ## Result-style higher-order specifications

These examples mirror the three core cases in
`Aeneas.Tactic.Step.Tests.HigherOrder`. The `fail_if_success` checks record that,
unlike for `Std.Result`, `step* +inferPost` does not infer predicate parameters
for SLPoC triples. Supplying those predicates explicitly lets `step` use the
registered specifications and prove the callback premises.
-/

namespace ResultStyle

def applyF (f : Nat → St Nat) (x : Nat) : St Nat :=
  f x

@[step]
theorem applyF.spec (f : Nat → St Nat) (x : Nat) (post : Nat → Prop)
    (hf : (f x) ⦃⇓ y => post y⦄) :
    (applyF f x) ⦃⇓ y => post y⦄ := by
  simpa [applyF] using hf

example (x : Nat) :
    (applyF (fun y => pure (y + 1)) x) ⦃⇓ y => y = x + 1⦄ := by
  fail_if_success
    step* +inferPost
    done
  step with applyF.spec (fun y => pure (y + 1)) x (fun y => y = x + 1)
  case hf => step*
  case hRamified => simp [Entails, Aeneas.SLPoC.emp, ipure]

def callPair (f g : Nat → St Nat) (xy : Nat × Nat) : St (Nat × Nat) := do
  let a ← f xy.1
  let b ← g xy.2
  pure (a, b)

@[step]
theorem callPair.spec (f g : Nat → St Nat) (xy : Nat × Nat)
    (postF postG : Nat → Prop)
    (hf : (f xy.1) ⦃⇓ a => postF a⦄)
    (hg : (g xy.2) ⦃⇓ b => postG b⦄) :
    (callPair f g xy) ⦃⇓ result => postF result.1 ∧ postG result.2⦄ := by
  unfold callPair
  step*

example (x y : Nat) :
    (callPair (fun a => pure (a + 1)) (fun b => pure (b + 2)) (x, y))
      ⦃⇓ result => result.1 = x + 1 ∧ result.2 = y + 2⦄ := by
  fail_if_success
    step* +inferPost
    done
  step with callPair.spec
    (fun a => pure (a + 1)) (fun b => pure (b + 2)) (x, y)
    (fun a => a = x + 1) (fun b => b = y + 2)
  case hf => step*
  case hg => step*
  case hRamified =>
    apply postWand_intro
    intro result
    iframe

def callFThenG (f g : Nat → St Nat) (x : Nat) : St Nat := do
  let y ← f x
  g y

@[step]
theorem callFThenG.spec (f g : Nat → St Nat) (x : Nat)
    (mid post : Nat → Prop)
    (hf : (f x) ⦃⇓ y => mid y⦄)
    (hg : ∀ y, mid y → (g y) ⦃⇓ z => post z⦄) :
    (callFThenG f g x) ⦃⇓ z => post z⦄ := by
  unfold callFThenG
  step*

example (x : Nat) :
    (callFThenG (fun y => pure (y + 1)) (fun y => pure (y + 1)) x)
      ⦃⇓ result => result = x + 2⦄ := by
  fail_if_success
    step* +inferPost
    done
  step with callFThenG.spec
    (fun y => pure (y + 1)) (fun y => pure (y + 1)) x
    (fun y => y = x + 1) (fun result => result = x + 2)
  case hf => step*
  case hg =>
    intro y hy
    step*
  case hRamified => simp [Entails, Aeneas.SLPoC.emp, ipure]

end ResultStyle

end HigherOrder

end Aeneas.SLPoC
