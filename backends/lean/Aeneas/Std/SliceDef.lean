import Aeneas.Std.Scalar.Core
import Aeneas.Data.ListN

namespace Aeneas.Std
open Aeneas.Data.ListN

-- Note that we can't define `Slice` as a subtype of `List` (that is:
-- `{ l : List α // l.length ≤ Usize.max }`): Lean would then reject the inductive
-- definitions which use `Slice` in a positive position.
-- See the explanations in `Aeneas/Data/ListN.lean`, as well as the corresponding
-- github issue: https://github.com/AeneasVerif/aeneas/issues/1138.
structure Slice (α : Type u) where
  leng : Nat
  list : ListN α leng
  bound : leng ≤ Usize.max
deriving BEq, ReflBEq, LawfulBEq, DecidableEq

@[coe]
def Slice.val {α} (s : Slice α) : List α := s.list.toList

@[simp, scalar_tac s.val]
theorem Slice.property {α} (s : Slice α) : s.val.length ≤ Usize.max := by
  simp [Slice.val, ListN_length]
  apply s.bound

grind_pattern Slice.property => s.val
grind_pattern [agrind] Slice.property => s.val

def Slice.from {α} (l : List α) (h : l.length ≤ Usize.max) : Slice α :=
  {
    leng := l.length
    list := .fromList l
    bound := by assumption
  }

@[simp, simp_lists_safe, grind =, agrind =]
theorem Slice.from_val {α} (l : List α) (h : l.length ≤ Usize.max)
  : (Slice.from l h).val = l := by
  simp [Slice.from, Slice.val, ListN.from_to_inverse]

@[simp, simp_lists_safe, grind =, agrind =]
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

@[ext, grind ext, agrind ext]
theorem Slice.ext {α} (s0 s1 : Slice α) (h : s0.val = s1.val) : s0 = s1 :=
  (Slice.eq_iff s0 s1).mpr h

end Aeneas.Std
