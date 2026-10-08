module
public import Aeneas.SepLogic.Tactic.IRewrite
public section

namespace Aeneas.SepLogic.Tactic.Tests.IRewrite

open Aeneas.SepLogic

private def wrappedEntails (P Q : IProp) : Prop := P ⊢ Q

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

example (P : IProp) (p : Prop) (h : P ⊢ ⌜p⌝ ∗ P) :
    wrappedEntails P (⌜p⌝ ∗ P) := by
  irewrite h
  guard_target = wrappedEntails (⌜p⌝ ∗ P) (⌜p⌝ ∗ P)
  unfold wrappedEntails
  iframe

example (P Q R : IProp) (h : P ⊢ Q) : P ∗ R ⊢ Q ∗ R := by
  irewrite h
  iframe

example (P Q R : IProp) (h : P = Q) : P ∗ R ⊢ Q ∗ R := by
  irewrite h
  iframe

example (P Q R : IProp) (h : P ⊢ Q) : R ∗ P ⊢ Q ∗ R := by
  irewrite h
  iframe

example (P Q : IProp) : emp ⊢ (P ∗ (P -∗ Q)) -∗ Q := by
  apply wand_intro
  irewrite wand_cancel
  iframe

example (P Q R : IProp) (h : P ⊢ Q) :
    wrappedEntails (P ∗ R) (Q ∗ R) := by
  irewrite h
  guard_target = wrappedEntails (Q ∗ R) (Q ∗ R)
  unfold wrappedEntails
  iframe

example (Q : Nat → IProp) (H R : IProp) (v : Nat) (h : H ⊢ R) :
    postSep Q H v ⊢ R ∗ Q v := by
  irewrite h
  iframe

example (P Q R : IProp) (h : Q = P) : R ∗ P ⊢ Q ∗ R := by
  irewrite ← h
  guard_target = (Q ∗ R ⊢ Q ∗ R)
  iframe

end Aeneas.SepLogic.Tactic.Tests.IRewrite
