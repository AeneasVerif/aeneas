import Aeneas.Std.Scalar
import Aeneas.Std.Array
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result Std.Do
set_option mvcgen.warning false

/-!
# Tests: mvcgen spec generation from @[step]

For every @[step] theorem, the attribute handler also generates an `mvcgen` spec.
-/

example {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
    ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ ⇓ z => ⌜ z.val = x.val + y.val ⌝ ⦄ := by
  mvcgen; scalar_tac

example {x y : U8} :
    ⦃ ⌜ True ⌝ ⦄
      (do
        if x < 10#u8
        then x * 2#u8
        else pure y)
    ⦃ ⇓ z => ⌜ z.val ≠ y → z.val < 20 ⌝ ⦄ := by
  mvcgen <;> scalar_tac

example (arr : Array U8 25#usize) (i : Usize) (a : U8) (hi : i < arr.length) :
    ⦃ ⌜ True ⌝ ⦄
      Array.update arr i a
    ⦃ ⇓ r => ⌜ r.get? i = some a ⌝ ⦄ := by
  mvcgen; grind

namespace Aeneas.Std.WP.MvcgenTests

open Aeneas.Data.Coinductive
open StateTest (StateEffect get put increment)

section PureResult

example : WPMonad Result .pure := inferInstance

example {α : Type u} (x : Result α) :
    (fun Q : Post α => (wp⟦x⟧ (⇓ value => ⌜Q value⌝)).down) = (spec x : Wp α) :=
  rfl

private theorem resultTriple_iff {α : Type u} (x : Result α) (P : Prop) (Q : Post α) :
    (⦃ ⌜P⌝ ⦄ x ⦃ ⇓ value => ⌜Q value⌝ ⦄) ↔ (P → spec x Q) :=
  Iff.rfl

example {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
    (x + y) ⦃ z => z.val = x.val + y.val ⦄ := by
  have h : ⦃ ⌜True⌝ ⦄ (x + y) ⦃ ⇓ z => ⌜z.val = x.val + y.val⌝ ⦄ := by
    mvcgen; scalar_tac
  exact h True.intro

example (x : Nat) :
    (do
      let value ← (pure x : Result Nat)
      pure (value + 1)) = .ok (x + 1) := by
  apply Result.of_wp (fun result => result = .ok (x + 1))
  mvcgen

example (e : Error) :
    ¬ (⦃ ⌜True⌝ ⦄ (Result.fail e : Result Nat) ⦃ ⇓ _ => ⌜True⌝ ⦄) := by
  simp [resultTriple_iff]

example :
    ¬ (⦃ ⌜True⌝ ⦄ (Result.div : Result Nat) ⦃ ⇓ _ => ⌜True⌝ ⦄) := by
  simp [resultTriple_iff]

def maybeDiv (n : Nat) : Result Nat :=
  if n = 0 then .div else .ok n

@[local step]
theorem maybeDiv_dspec (n : Nat) : maybeDiv n ⦃ value => value = n ⦄div := by
  unfold maybeDiv
  split
  · simp only [dspec_div]
  · simp only [dspec_ok]

example (n : Nat) :
    ⦃ ⌜maybeDiv n ≠ .div⌝ ⦄ maybeDiv n ⦃ ⇓ value => ⌜value = n⌝ ⦄ :=
  maybeDiv_dspec.mvcgen_spec n

example (n : Nat) (h : n ≠ 0) :
    ⦃ ⌜True⌝ ⦄ maybeDiv n ⦃ ⇓ value => ⌜value = n⌝ ⦄ := by
  mvcgen
  simp [maybeDiv, h]

end PureResult

section Total

local instance : WPMonad (ITree StateEffect) (.arg Nat .pure) :=
  totalWPMonad StateTest.handler StateTest.handler_conjunctive

@[local spec]
theorem get_total (state : Nat) :
    ⦃ fun s => ⌜s = state⌝ ⦄ get
    ⦃ ⇓ value s => ⌜value = state ∧ s = state⌝ ⦄ := by
  apply (totalTriple_iff StateTest.handler StateTest.handler_conjunctive).mpr
  rintro _ rfl
  exact TotalSpec.vis (TotalSpec.ret ⟨rfl, rfl⟩)

@[local spec]
theorem put_total (value : Nat) :
    ⦃ ⌜True⌝ ⦄ put value ⦃ ⇓ _ s => ⌜s = value⌝ ⦄ := by
  apply (totalTriple_iff StateTest.handler StateTest.handler_conjunctive).mpr
  intro _ _
  exact TotalSpec.vis (TotalSpec.ret rfl)

@[local spec]
theorem choose_total (α : Type) [Nonempty α] (state : Nat) :
    ⦃ fun s => ⌜s = state⌝ ⦄ StateTest.choose α
    ⦃ ⇓ _ s => ⌜s = state⌝ ⦄ := by
  apply (totalTriple_iff StateTest.handler StateTest.handler_conjunctive).mpr
  rintro _ rfl
  exact TotalSpec.vis ⟨inferInstance, fun _ => TotalSpec.ret rfl⟩

theorem increment_total (state : Nat) :
    ⦃ fun s => ⌜s = state⌝ ⦄ increment
    ⦃ ⇓ value s => ⌜value = state ∧ s = state + 1⌝ ⦄ := by
  mvcgen [increment]; grind

example (state : Nat) :
    ⦃ fun s => ⌜s = state⌝ ⦄ StateTest.flip
    ⦃ ⇓ value s => ⌜(value = 0 ∨ value = 1) ∧ s = state⌝ ⦄ := by
  mvcgen [StateTest.flip]; grind

example :
    ¬ (⦃ ⌜True⌝ ⦄ (ITree.div : ITree StateEffect Nat)
        ⦃ ⇓ _ _ => ⌜True⌝ ⦄) := by
  intro h
  exact TotalSpec.div_false
    ((totalTriple_iff StateTest.handler StateTest.handler_conjunctive).mp h 0 True.intro)

example :
    ¬ (⦃ ⌜True⌝ ⦄ StateTest.failure ⦃ ⇓ _ _ => ⌜True⌝ ⦄) := by
  intro h
  have hSpec := (totalTriple_iff StateTest.handler StateTest.handler_conjunctive).mp h 0 True.intro
  simp only [StateTest.failure, StateTest.fail, Bind.bind, itree_vis_bind] at hSpec
  exact hSpec.vis_view

example :
    ¬ (⦃ ⌜True⌝ ⦄ StateTest.choose Empty ⦃ ⇓ _ _ => ⌜True⌝ ⦄) := by
  intro h
  have hSpec := (totalTriple_iff StateTest.handler StateTest.handler_conjunctive).mp h 0 True.intro
  obtain ⟨value⟩ := hSpec.vis_view.1
  exact value.elim

end Total

section Partial

local instance : WPMonad (ITree StateEffect) (.arg Nat .pure) :=
  partialWPMonad StateTest.handler StateTest.handler_conjunctive

@[local spec]
theorem increment_partial (state : Nat) :
    ⦃ fun s => ⌜s = state⌝ ⦄ increment
    ⦃ ⇓ value s => ⌜value = state ∧ s = state + 1⌝ ⦄ := by
  apply (partialTriple_iff StateTest.handler StateTest.handler_conjunctive).mpr
  intro s h
  exact TotalSpec.toPartial
    ((totalTriple_iff StateTest.handler StateTest.handler_conjunctive).mp
      (increment_total state) s h)

@[local spec]
theorem div_partial :
    ⦃ ⌜True⌝ ⦄ (ITree.div : ITree StateEffect Nat)
    ⦃ ⇓ _ _ => ⌜False⌝ ⦄ := by
  apply (partialTriple_iff StateTest.handler StateTest.handler_conjunctive).mpr
  intro _ _
  exact PartialSpec.div

example (state : Nat) :
    ⦃ fun s => ⌜s = state⌝ ⦄
      (do
        let _ ← increment
        increment)
    ⦃ ⇓ value s => ⌜value = state + 1 ∧ s = state + 2⌝ ⦄ := by
  mvcgen; grind

example :
    ⦃ ⌜True⌝ ⦄
      (do
        let value ← (ITree.div : ITree StateEffect Nat)
        pure (value + 1))
    ⦃ ⇓ _ _ => ⌜False⌝ ⦄ := by
  mvcgen

example :
    ¬ (⦃ ⌜True⌝ ⦄ StateTest.failure ⦃ ⇓ _ _ => ⌜True⌝ ⦄) := by
  intro h
  have hSpec := (partialTriple_iff StateTest.handler StateTest.handler_conjunctive).mp h 0 True.intro
  simp only [StateTest.failure, StateTest.fail, Bind.bind, itree_vis_bind] at hSpec
  exact hSpec.vis_view

example :
    ¬ (⦃ ⌜True⌝ ⦄ StateTest.choose Empty ⦃ ⇓ _ _ => ⌜True⌝ ⦄) := by
  intro h
  have hSpec := (partialTriple_iff StateTest.handler StateTest.handler_conjunctive).mp h 0 True.intro
  obtain ⟨value⟩ := hSpec.vis_view.1
  exact value.elim

end Partial

end Aeneas.Std.WP.MvcgenTests
