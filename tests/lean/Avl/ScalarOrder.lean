import Avl.OrderSpec

namespace avl

open Primitives

instance ScalarU32DecidableLE : DecidableRel (· ≤ · : U32 -> U32 -> Prop) := by
  simp [instLEScalar]
  -- Lift this to the decidability of the Int version.
  infer_instance

instance : LinearOrder (Scalar .U32) where
  le_antisymm := fun a b Hab Hba => by
    apply (Scalar.eq_equiv a b).2; exact (Int.le_antisymm ((Scalar.le_equiv _ _).1 Hab) ((Scalar.le_equiv _ _).1 Hba))
  le_total := fun a b => by
    rcases (Int.le_total a b) with H | H
    left; exact (Scalar.le_equiv _ _).2 H
    right; exact (Scalar.le_equiv _ _).2 H
  decidableLE := ScalarU32DecidableLE

instance : OrdSpecLinearOrderEq OrdUsize where
  infallible := fun a b => by
    unfold Ord.cmp
    unfold OrdUsize
    unfold OrdUsize.cmp
    rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    if hlt : a < b then
      use .Less
      simp [*]
      intros; scalar_tac -- Contradiction
    else
      if heq: a = b
      then
        use .Equal
        simp [hlt, *]
      else
        use .Greater
        simp [hlt, heq]
        scalar_tac
  symmetry := fun a b => by
    simp [Ordering.toDualOrdering, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    rw [compare, Ord.opposite]
    simp [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    split_ifs with hab hba hba' hab' hba'' _ hba₃ _ <;> tauto
    exact lt_irrefl _ (lt_trans hab hba)
    rw [hba'] at hab; exact lt_irrefl _ hab
    rw [hab'] at hba''; exact lt_irrefl _ hba''
    -- The order is total, therefore, we have at least one case where we are comparing something.
    cases (lt_trichotomy a b) <;> tauto
  equivalence := fun a b => by
    unfold Ord.cmp
    unfold OrdUsize
    unfold OrdUsize.cmp
    simp only []
    split_ifs <;> simp only [Result.ok.injEq, not_false_eq_true, neq_imp, IsEmpty.forall_iff]; tauto; try assumption

end avl
