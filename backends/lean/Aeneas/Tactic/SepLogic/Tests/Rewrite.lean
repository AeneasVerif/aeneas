module
public import Aeneas.Tactic.SepLogic.Rewrite
public section

/-!
# Regression tests for `irewrite`
-/

namespace Aeneas.Tactic.SepLogic.Tests.Rewrite

open Aeneas.SepLogic

private def wrappedEntails (P Q : IProp) : Prop := P ⊢ Q

/-- Rewriting all resources must not introduce an empty frame. -/
example (P Q : IProp) (h : P ⊢ Q) : P ⊢ Q := by
  irewrite h
  guard_target = (Q ⊢ Q)
  iframe

example (P Q : IProp) (h : P = Q) : P ⊢ Q := by
  irewrite h
  guard_target = (Q ⊢ Q)
  iframe

example (P Q R : IProp) (h : P ∗ R ⊢ Q) : R ∗ P ⊢ Q := by
  irewrite h
  guard_target = (Q ⊢ Q)
  iframe

/-- Pure-fact extraction preserves both the wrapper and the exact resources. -/
example (P : IProp) (p : Prop) (h : P ⊢ ⌜p⌝ ∗ P) :
    wrappedEntails P (⌜p⌝ ∗ P) := by
  irewrite h
  guard_target = wrappedEntails (⌜p⌝ ∗ P) (⌜p⌝ ∗ P)
  unfold wrappedEntails
  iframe

example (P Q R : IProp) (h : P ⊢ Q) : P ∗ R ⊢ Q ∗ R := by
  irewrite h
  iframe

/-- The rule accepts an equality as well as an entailment. -/
example (P Q R : IProp) (h : P = Q) : P ∗ R ⊢ Q ∗ R := by
  irewrite h
  iframe

/-- The rewritten atom need not occur first: `irewrite` reorders up to
associativity and commutativity. -/
example (P Q R : IProp) (h : P ⊢ Q) : R ∗ P ⊢ Q ∗ R := by
  irewrite h
  iframe

/-- Packaging a wand: the cancellation happens under `wand_intro`. -/
example (P Q : IProp) : emp ⊢ (P ∗ (P -∗ Q)) -∗ Q := by
  apply wand_intro
  irewrite (wand_cancel P Q)
  iframe

/-- Rewriting works through arbitrary reducible wrappers and preserves them. -/
example (P Q R : IProp) (h : P ⊢ Q) :
    wrappedEntails (P ∗ R) (Q ∗ R) := by
  irewrite h
  guard_target = wrappedEntails (Q ∗ R) (Q ∗ R)
  unfold wrappedEntails
  iframe

end Aeneas.Tactic.SepLogic.Tests.Rewrite
