import Lean

/-- Small helper

    We used to use this for the list definitions, as some definitions like `index` used to
    manipulate integers and not natural numbers.

    We cover a set of cases which might imply inequality, to make sure that using
    this as the precondition of a `simp` lemma will allow the lemma to get correctly
    triggered. -/
@[simp]
abbrev Nat.not_eq (i j : Nat) : Prop :=
  i ≠ j ∨ j ≠ i ∨ i < j ∨ j < i

theorem Nat.not_eq_imp_not_eq {i j} : Nat.not_eq i j → i ≠ j := by
  intro h g
  simp_all
