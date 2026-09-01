import Aeneas.SLPoC.WP

namespace Aeneas.SLPoC.Tests.WP

example (P Q : IProp) : P ∗ Q ⊢ Q ∗ P := by
  iframe

example (P Q : IProp) : (P ∗ Q) ⊣⊢ (Q ∗ P) := by
  exact sep_comm P Q

example (P : IProp) : emp ∗ P ⊢ P := by
  isimp
  iframe

example {α : Type} (P : α → IProp) :
    iprop(∃ x, P x) ⊢ iprop(∃ x, P x) := by
  iframe

example {α : Type} (P : α → IProp) :
    iprop(∀ x, P x) ⊢ iprop(∀ x, P x) := by
  iframe

example (P Q : IProp) : P ∗ (P -∗ Q) ⊢ Q :=
  wand_cancel P Q

example (P Q R : IProp) (h : P ⊢ Q) : P ∗ R ⊢ Q ∗ R := by
  irewrite h
  iframe

example {α : Type} (r : Aeneas.SLPoC.Ref α) (value : α) :
    r ↦ value ⊢ r ↦ value := by
  iframe

example {α : Type} (w : Wp α) : w.wp = Wp.wp w :=
  rfl

end Aeneas.SLPoC.Tests.WP
