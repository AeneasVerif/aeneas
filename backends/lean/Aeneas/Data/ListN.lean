namespace Aeneas.Data.ListN

inductive ListN.{u} (α : Type u) : Nat → Type u where
| nil : ListN α 0
| cons {n} : α → ListN α n → ListN α n.succ
deriving BEq, ReflBEq, LawfulBEq, DecidableEq

def ListN.toList {a n} (l : ListN a n) : List a :=
  match l with
  | .nil => .nil
  | .cons a l' => .cons a l'.toList

def ListN.fromList {a} (l : List a) : ListN a l.length :=
  match l with
  | .nil => .nil
  | .cons a l' => .cons a (ListN.fromList l')

theorem ListN.from_to_inverse {α} {l : List α}: (ListN.fromList l).toList = l := by
  induction l <;> grind [toList, fromList]

theorem ListN_length {α n} (l : ListN α n) : l.toList.length = n := by
  induction l <;> grind [ListN.toList]

theorem ListN.to_from_inverse {α n} {l : ListN α n}
  : ListN.fromList l.toList ≍ l := by
  induction l <;> simp [toList, fromList]
  rename_i n a l ih
  congr
  apply ListN_length

theorem ListN.toList_inj {α n} (l1 l2 : ListN α n) (h : l1.toList = l2.toList) : l1 = l2 := by
  induction l1 <;> cases l2 <;> grind [ListN.toList]

end Aeneas.Data.ListN
