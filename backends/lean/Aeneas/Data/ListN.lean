/-!
# `ListN`: length-indexed lists

`ListN α n` is the type of the lists of elements of type `α` whose length is exactly `n`.

## Why do we need this?

We use `ListN` to define `Slice`, `Array` and `Vec` (see `Aeneas/Std/SliceDef.lean`,
`Aeneas/Std/Array/Array.lean` and `Aeneas/Std/Vec.lean`).

The reason is that we need to be able to use those types in *positive* positions of
inductive definitions, i.e., we want definitions such as:
```
inductive Tree where
| node : Slice Tree → Tree
```
to be accepted by Lean.

The natural definition of `Slice` - a subtype of `List` - is rejected in this
situation because of a positivity issue(see the `Test` namespace at the end of
this file for a concrete example of the error Lean reports).

There are two constraints that the definition of `Slice` must satisfy for Lean to accept
such recursive occurrences:
- it must not go through any `def` (which is why `Slice` is a `structure` and not an
  abbreviation for a subtype);
- a recursive occurrence which is passed as an argument to another inductive must not
  then be passed to a third inductive.

The `ListN` solutions satisfies both: the bound is stated about the length, not
the list itself.

See: https://github.com/AeneasVerif/aeneas/issues/1138
-/

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

/-!
## Positivity test

The following checks that the `ListN`-based encoding indeed makes recursive occurrences
legal, and that the naive encoding does not.
-/
namespace Test

/-- A `Slice`-like structure, defined the way `Aeneas.Std.Slice` is: the length is a
    *field*, the list is indexed by it, and the bound only mentions that field. -/
structure GoodSlice (α : Type) where
  len : Nat
  list : ListN α len
  bound : leng ≤ 2 ^ 64 - 1

/- This is accepted. -/
inductive E where
| V : GoodSlice E → E

/-- The naive encoding, where the bound mentions `l.length`. -/
structure BadSlice (α : Type) where
  l : List α
  bound : l.length ≤ 2 ^ 64 - 1

/- This is rejected by the kernel. -/
/--
error: (kernel) application type mismatch
  List.length l
argument has type
  _nested.List_2
but function has type
  List E2 → Nat
-/
#guard_msgs in
inductive E2 where
| d : BadSlice E2 → E2

/-- An *alias* for a legal type is not enough either: the kernel does not unfold the
    `def` when checking positivity (an `abbrev` doesn't work any better).
    This is why `Aeneas.Std.alloc.vec.Vec` is a `structure` wrapping a `Slice`, and not
    `def Vec (α : Type u) := Slice α`. -/
def GoodSliceAlias (α : Type) := GoodSlice α

/--
error: (kernel) arg #1 of 'Aeneas.Data.ListN.Test.E3.V' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive E3 where
| V : GoodSliceAlias E3 → E3

end Test

end Aeneas.Data.ListN
