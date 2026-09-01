import Aeneas.SLPoC.MutableData.Ptr

namespace Aeneas.SLPoC


namespace Examples

/-- Two views of memory that are either the same or separated: the ghost state
of a `src`/`dst` pair. -/
inductive EqOrDisj (α : Type) where
  | equal (value : α)
  | disjoint (leftValue rightValue : α)

/-- What the read view holds. -/
def EqOrDisj.read {α : Type} (relation : EqOrDisj α) : α :=
  match relation with
  | .equal value => value
  | .disjoint leftValue _ => leftValue

/-- What the write view holds. -/
def EqOrDisj.written {α : Type} (relation : EqOrDisj α) : α :=
  match relation with
  | .equal value => value
  | .disjoint _ rightValue => rightValue

/-- Give the write view the contents `value`. -/
def EqOrDisj.write {α : Type} (relation : EqOrDisj α)
    (value : α) : EqOrDisj α :=
  match relation with
  | .equal _ => .equal value
  | .disjoint leftValue _ => .disjoint leftValue value

@[simp] theorem EqOrDisj.written_write {α : Type} (relation : EqOrDisj α)
    (value : α) : (relation.write value).written = value := by
  cases relation <;> rfl

/-- Writing is visible to the reader exactly when the two views are the same:
this single pair of equations is the whole pattern. -/
@[simp] theorem EqOrDisj.read_write_equal {α : Type} (old value : α) :
    ((EqOrDisj.equal old).write value).read = value := rfl

@[simp] theorem EqOrDisj.read_write_disjoint {α : Type}
    (leftValue rightValue value : α) :
    ((EqOrDisj.disjoint leftValue rightValue).write value).read =
      leftValue := rfl

end Examples

end Aeneas.SLPoC
