module
public import Aeneas.SepLogic.Basic
public section

/-!
# Regression tests for the separation logic itself

The lemmas of the assertion language, proved without the proof mode.  The
tactic tests are in `Aeneas.Tactic.SepLogic.Tests`.
-/

namespace Aeneas.SepLogic.Tests

/-! ## Pretty-printing -/

/-- error: unsolved goals
P Q : IProp
⊢ P ⊢ Q -/
#guard_msgs in
example (P Q : IProp) : Entails P Q := by done

/-- error: unsolved goals
P : Prop
⊢ emp ⊢ ⌜P⌝ -/
#guard_msgs in
example (P : Prop) : Entails emp (ipure P) := by done

example (P : IProp) : iprop(P) = P :=
  rfl

/-- error: unsolved goals
P Q : IProp
⊢ P ⊢ iprop(P ∧ Q) -/
#guard_msgs in
example (P Q : IProp) : Entails P (iand P Q) := by done

example (P Q R : IProp) : iprop(P ∗ (Q ∧ R)) = (P ∗ iand Q R) :=
  rfl

example (P Q R : IProp) : iprop((P ∧ Q) -∗ R) = (iand P Q -∗ R) :=
  rfl

example (J : Nat → IProp) (P : IProp) :
    iprop(∃ x, J x ∧ P) = iexists (fun x => iand (J x) P) :=
  rfl

example (J : Nat → IProp) (P : IProp) :
    iprop(∀ x, J x ∧ P) = iforall (fun x => iand (J x) P) :=
  rfl

example (H P Q : IProp) (hP : H ⊢ P) (hQ : H ⊢ Q) : H ⊢ iprop(P ∧ Q) :=
  iand_intro hP hQ

example (P Q R : IProp) : iprop((P ∧ Q) ∧ R) ⊣⊢ iprop(P ∧ (Q ∧ R)) :=
  iand_assoc P Q R

example (P Q : Prop) : iprop(⌜P⌝ ∧ ⌜Q⌝) = ⌜P ∧ Q⌝ := by
  simp

example {α : Type} (r : Aeneas.Std.Ref α) (value : α) :
    iprop((r ↦ value) ∧ (r ↦ value)) = (r ↦ value) := by
  simp

example (P Q : IProp) (frame : Aeneas.Std.Heap) :
    iprop((P ∗ owns frame) ∧ (Q ∗ owns frame)) ⊢ iprop(P ∧ Q) ∗ owns frame :=
  (sep_iand_owns P Q frame).mpr

example (P Q : IProp) : (P ∗ Q) ⊣⊢ (Q ∗ P) :=
  sep_comm P Q

example (P : IProp) : (emp ∗ P) = P := by
  simp

example (P : IProp) : (⌜True⌝ ∗ P) = P := by
  simp

example (P Q : IProp) : P ∗ (P -∗ Q) ⊢ Q :=
  wand_cancel P Q

example (Q₁ Q₂ : IPost Nat) : Q₁ ∗+ (Q₁ -∗+ Q₂) ⊢+ Q₂ :=
  postWand_cancel Q₁ Q₂

/-- A slot cannot be owned twice: separation is still separation. -/
example {α : Type} (r : Aeneas.Std.Ref α) (x y : α) : r ↦ x ∗ r ↦ y ⊢ ⌜False⌝ :=
  Ref.pointsTo_exclusive r x y

end Aeneas.SepLogic.Tests
