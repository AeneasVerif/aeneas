namespace Aeneas.SLPoC

/-!
# Partial commutative monoids

Lean's standard library and mathlib do not currently provide a partial
commutative monoid typeclass.  This version represents the partial operation by
a total union together with a compatibility relation.  The value of the union
outside that relation is irrelevant.
-/

/-- A partial commutative monoid (PCM), represented by a total union operation
whose meaningful inputs are selected by `Compatible`. -/
class PartialCommMonoid (α : Type u) [EmptyCollection α] [Union α] where
  Compatible : α → α → Prop
  compatible_comm {a b : α} : Compatible a b → Compatible b a
  compatible_empty_left (a : α) : Compatible ∅ a
  compatible_assoc (a b c : α) :
    Compatible a b ∧ Compatible (a ∪ b) c ↔
      Compatible b c ∧ Compatible a (b ∪ c)
  union_assoc {a b c : α} :
    Compatible a b → Compatible (a ∪ b) c →
      a ∪ b ∪ c = a ∪ (b ∪ c)
  empty_union (a : α) : ∅ ∪ a = a
  union_empty (a : α) : a ∪ ∅ = a
  union_comm_of_compatible {a b : α} :
    Compatible a b → a ∪ b = b ∪ a

end Aeneas.SLPoC
