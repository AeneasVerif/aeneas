import Lean

/-- Small helper

    We used to use this for the list definitions, as some definitions like `index` used to
    manipulate integers and not natural numbers.

    We cover a set of cases which might imply inequality, to make sure that using
    this as the precondition of a `simp` lemma will allow the lemma to get correctly
    triggered. -/
@[simp]
abbrev Int.not_eq (i j : Int) : Prop :=
  i ≠ j ∨ j ≠ i ∨ i < j ∨ j < i

theorem Int.not_eq_imp_not_eq {i j} : Int.not_eq i j → i ≠ j := by
  intro h g
  simp_all
