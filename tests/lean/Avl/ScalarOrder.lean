import Avl.OrderSpec

namespace avl

open Aeneas.Std

-- TODO: move
instance UScalarDecidableLE {ty} : DecidableRel (· ≤ · : UScalar ty -> UScalar ty -> Prop) := by
  simp [instLEUScalar]
  -- Lift this to the decidability of the Int version.
  infer_instance

-- TODO: move
instance {ty} : LinearOrder (UScalar ty) where
  le_antisymm := fun a b Hab Hba => by scalar_tac
  le_total := fun a b => by scalar_tac
  toDecidableLE := UScalarDecidableLE

instance : OrdSpecLinearOrderEq OrdI32 where
  infallible := fun a b => by
    unfold Ord.cmp OrdI32 OrdI32.cmp
    simp only
    split <;> simp
    . scalar_tac
    . split <;> simp <;> scalar_tac
  symmetry := fun a b => by
    simp [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    rw [compare, Ord.opposite]
    simp [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    grind [IScalar.neq_to_neq_val]
  equivalence := fun a b => by
    unfold Ord.cmp
    unfold OrdI32
    unfold OrdI32.cmp
    grind [IScalar.neq_to_neq_val]

end avl
