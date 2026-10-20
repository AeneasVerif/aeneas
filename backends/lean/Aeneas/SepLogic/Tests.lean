module
public import Aeneas.SepLogic.Lemmas
public import Aeneas.SepLogic.Delab
public import Aeneas.Std.Core.Ptr
public section

namespace Aeneas.SepLogic.Tests

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

-- a partial application is printed as is
/-- info: iand emp : IProp → IProp -/
#guard_msgs in
#check iand emp

/-- error: unsolved goals
cell : ℕ → IProp
⊢ emp ⊢ iprop(∃ v, ⌜0 < v⌝ ∗ cell v) -/
#guard_msgs in
example (cell : Nat → IProp) : emp ⊢ iprop(∃ v, ⌜0 < v⌝ ∗ cell v) := by done

/-- error: unsolved goals
cell : ℕ → IProp
⊢ emp ⊢ iprop(∀ v, cell v) -/
#guard_msgs in
example (cell : Nat → IProp) : emp ⊢ iprop(∀ v, cell v) := by done

/-- error: unsolved goals
J : ℕ → ℕ → IProp
⊢ emp ⊢ iprop(∃ a b, J a b) -/
#guard_msgs in
example (J : Nat → Nat → IProp) : emp ⊢ iprop(∃ a b, J a b) := by done

/-- error: unsolved goals
J : ℕ → ℕ → IProp
⊢ emp ⊢ iprop(∀ a b, J a b) -/
#guard_msgs in
example (J : Nat → Nat → IProp) : emp ⊢ iprop(∀ a b, J a b) := by done

/-- error: unsolved goals
cell : ℕ → IProp
⊢ emp ⊢ iexists cell -/
#guard_msgs in
example (cell : Nat → IProp) : emp ⊢ iexists cell := by done

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

example (J : Nat → Nat → IProp) :
    iprop(∃ a b, J a b) = iexists (fun a => iexists (fun b => J a b)) :=
  rfl

example (J : Nat → Nat → Nat → IProp) :
    iprop(∀ a b c : Nat, J a b c) =
      iforall (fun a : Nat => iforall (fun b : Nat => iforall (fun c : Nat => J a b c))) :=
  rfl

example (H P Q : IProp) (hP : H ⊢ P) (hQ : H ⊢ Q) : H ⊢ iprop(P ∧ Q) :=
  iand_intro hP hQ

example (P Q R : IProp) : iprop((P ∧ Q) ∧ R) = iprop(P ∧ (Q ∧ R)) :=
  iand_assoc P Q R

example (P Q : Prop) : iprop(⌜P⌝ ∧ ⌜Q⌝) = ⌜P ∧ Q⌝ := by
  simp

example {α : Type} (r : Aeneas.Std.MutRawPtr α) (value : α) :
    iprop((r ↦ value) ∧ (r ↦ value)) = (r ↦ value) := by
  simp

example (P Q : IProp) (frame : Aeneas.Std.Heap) :
    iprop((P ∗ owns frame) ∧ (Q ∗ owns frame)) ⊢ iprop(P ∧ Q) ∗ owns frame :=
  entails_of_eq (sep_iand_owns P Q frame).symm

example (P Q : IProp) : (P ∗ Q) = (Q ∗ P) :=
  sep_comm_eq P Q

example (P : IProp) : (emp ∗ P) = P := by
  simp

example (P : IProp) : (⌜True⌝ ∗ P) = P := by
  simp

example (P : IProp) : (P ∗ emp) = P := by
  simp

example (P Q : IProp) : P ∗ (P -∗ Q) ⊢ Q :=
  wand_cancel P Q

example (Q₁ Q₂ : IPost Nat) : Q₁ ∗+ (Q₁ -∗+ Q₂) ⊢+ Q₂ :=
  postWand_cancel Q₁ Q₂

example (q : Aeneas.Std.MutRawPtr α) (x y : α) (kind : Aeneas.Std.AllocKind) (len : Nat)
    (hOffset : q.offset < len) :
    owns (Aeneas.Std.Heap.singleton q x kind len) ∗ owns (Aeneas.Std.Heap.singleton q y kind len)
      ⊢ ⌜False⌝ :=
  owns_singleton_exclusive q x y hOffset hOffset

end Aeneas.SepLogic.Tests
