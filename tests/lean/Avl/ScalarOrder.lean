import Avl.OrderSpec

namespace avl

open Primitives

-- TODO: move
instance ScalarDecidableLE {ty} : DecidableRel (· ≤ · : Scalar ty -> Scalar ty -> Prop) := by
  simp [instLEScalar]
  -- Lift this to the decidability of the Int version.
  infer_instance

-- TODO: move
instance {ty} : LinearOrder (Scalar ty) where
  le_antisymm := fun a b Hab Hba => by
    apply (Scalar.eq_equiv a b).2; exact (Int.le_antisymm ((Scalar.le_equiv _ _).1 Hab) ((Scalar.le_equiv _ _).1 Hba))
  le_total := fun a b => by
    rcases (Int.le_total a b) with H | H
    left; exact (Scalar.le_equiv _ _).2 H
    right; exact (Scalar.le_equiv _ _).2 H
  decidableLE := ScalarDecidableLE

instance : OrdSpecLinearOrderEq OrdI32 where
  infallible := fun a b => by
    unfold Ord.cmp
    unfold OrdI32
    unfold OrdI32.cmp
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
    unfold OrdI32
    unfold OrdI32.cmp
    simp only []
    split_ifs <;> simp only [Result.ok.injEq, not_false_eq_true, neq_imp, IsEmpty.forall_iff]; tauto; try assumption

end avl
