import Aeneas.Std.Scalar.Core
import Aeneas.Data.ListN

namespace Aeneas.Std
open Aeneas.Data.ListN

-- This unusual definition using ListN is necessary due to positivity issues.
-- See the test at the end of this file.
structure Slice (α : Type u) where
  leng : Nat
  list : ListN α leng
  bound : leng ≤ Usize.max
deriving BEq, ReflBEq, LawfulBEq, DecidableEq

@[coe]
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

@[scalar_tac_simps, simp, grind! ., grind .]
theorem Slice.from_val {α} (l : List α) (h : l.length ≤ Usize.max)
  : (Slice.from l h).val = l := by
  simp [Slice.from, Slice.val, ListN.from_to_inverse]

@[scalar_tac_simps, simp, grind! ., grind .]
theorem Slice.val_from {α} (s : Slice α) h
  : Slice.from s.val h = s := by
  cases s
  simp [val, Slice.from] at *
  simp [ListN_length]
  apply ListN.to_from_inverse

theorem Slice.eq_iff {α} (s0 s1 : Slice α) : s0 = s1 ↔ s0.val = s1.val := by
  constructor
  · grind
  · intros p
    simp [val] at p
    have : s1.list ≍ s0.list := by
      have := ListN.to_from_inverse (l:=s0.list)
      have := ListN.to_from_inverse (l:=s1.list)
      grind
    cases s0; cases s1
    simp at *
    constructor <;> try grind [ListN_length]

namespace Aeneas.Std.Test
-- We need to be able to use Slice in positive positions in inductive definitions.
-- A simple definition with subtypes doesn't work here.
-- (See: https://github.com/AeneasVerif/aeneas/issues/1138)
-- There are two constraints that the definition of Slice must satisfy to make lean happy:
-- It must not use any defs, and recursive references passed as an argument to another inductive
-- must not then be passed to a third inductive, see example below
inductive E where
| V : Slice E → E

structure Slice2 (X : Type) where
  l : List X
  lent : l.length ≤ Usize.max

/--
error: (kernel) application type mismatch
  List.length l
argument has type
  _nested.List_2
but function has type
  List E2 → ℕ
-/
#guard_msgs in
inductive E2 where
| d : Slice2 E2 → E2

end Aeneas.Std.Test

end Aeneas.Std
