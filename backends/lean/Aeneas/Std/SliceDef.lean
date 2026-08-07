import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

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
  -- generalize hval : fromList l.toList = val at ih
  congr -- TODO: how does this tactic work here?
  apply ListN_length

theorem ListN.toList_inj {α n} (l1 l2 : ListN α n) (h : l1.toList = l2.toList) : l1 = l2 := by
  induction l1 <;> cases l2 <;> grind [ListN.toList]

-- TODO: clean this
-- def Slice (α : Type u) := { l : List α // l.length ≤ Usize.max }

-- This unusual definition using ListN is necessary due to positivity issues.
-- See the test at the end of this file.
structure Slice (α : Type u) where
  leng : Nat
  list : ListN α leng
  bound : leng ≤ Usize.max
deriving BEq, ReflBEq, LawfulBEq, DecidableEq

def Slice.val {α} (s : Slice α) : List α := s.list.toList

@[simp, grind ., grind! .]
theorem Slice.property {α} (s : Slice α) : s.val.length ≤ Usize.max := by
  simp [Slice.val, ListN_length]
  apply s.bound

def Slice.from {α} (l : List α) (h : l.length ≤ Usize.max) : Slice α :=
  {
    leng := l.length
    list := .fromList l
    bound := by assumption
  }

@[simp, grind! ., grind .]
theorem Slice.from_val {α} (l : List α) (h : l.length ≤ Usize.max)
  : (Slice.from l h).val = l := by
  simp [Slice.from, Slice.val, ListN.from_to_inverse]

@[simp, grind! ., grind .]
theorem Slice.val_from {α} (s : Slice α) h
  : Slice.from s.val h = s := by
  cases s
  simp [val, Slice.from] at *
  simp [ListN_length]
  apply ListN.to_from_inverse

namespace Aeneas.Std.Test
-- We need to be able to use Slice in positive positions in inductive definitions.
-- A simple definition with subtypes doesn't work here:
-- (See: https://github.com/AeneasVerif/aeneas/issues/1138)
inductive E where
| V : Slice E → E
end Aeneas.Std.Test

end Aeneas.Std
