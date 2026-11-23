module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Logic.Relation

/-!
# Strongly connected components and the condensation of a relation

The strongly connected components of a relation `s` are the classes of
`AntisymmRel (ReflTransGen s)`: `x` and `y` are in the same component when each reaches the other.
The quotient by this relation is Mathlib's `Antisymmetrization V (ReflTransGen s)`, which is
partially ordered; here we stay on `V` and work with representatives instead.

## Main definitions

* `Relation.CondensationAdj s r`: an `r`-edge between two different components of `s`.

## Main statements

* `Relation.antisymmRel_reflTransGen_iff`: being in the same component, in terms of `TransGen`.
* `Relation.condensationAdj_acyclic`: the edges between components have no cycle.
-/

@[expose] public section

namespace Relation

variable {V : Type*} {s r : V → V → Prop}

theorem equivalence_antisymmRel_reflTransGen (s : V → V → Prop) :
    Equivalence (AntisymmRel (ReflTransGen s)) :=
  (AntisymmRel.setoid V (ReflTransGen s)).iseqv

/-- Two vertices are in the same strongly connected component when they are equal, or when each
reaches the other in one or more steps. -/
theorem antisymmRel_reflTransGen_iff {a b : V} :
    AntisymmRel (ReflTransGen s) a b ↔ a = b ∨ (TransGen s a b ∧ TransGen s b a) := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases reflTransGen_iff_eq_or_transGen.1 h1 with rfl | h1
    · exact Or.inl rfl
    rcases reflTransGen_iff_eq_or_transGen.1 h2 with rfl | h2
    · exact Or.inl rfl
    exact Or.inr ⟨h1, h2⟩
  · rintro (rfl | ⟨h1, h2⟩)
    · exact AntisymmRel.refl _ _
    · exact ⟨h1.to_reflTransGen, h2.to_reflTransGen⟩

variable (s r) in
/-- An edge of the condensation of `s`: the component of `x` has an `r`-edge to the different
component of `y`. Usually `r = s`; a smaller `r` gives fewer edges between the same components. -/
def CondensationAdj (x y : V) : Prop :=
  ¬ AntisymmRel (ReflTransGen s) x y ∧
    ∃ i j, AntisymmRel (ReflTransGen s) x i ∧ AntisymmRel (ReflTransGen s) y j ∧ r i j

instance [Fintype V] [DecidableEq V] [DecidableRel (ReflTransGen s)] [DecidableRel r] :
    DecidableRel (CondensationAdj s r) := fun x y => by
  unfold CondensationAdj; infer_instance

theorem CondensationAdj.transGen (hrs : r ≤ s) {x y : V} (h : CondensationAdj s r x y) :
    TransGen s x y := by
  obtain ⟨-, i, j, hxi, hyj, hij⟩ := h
  exact (TransGen.tail' hxi.1 (hrs i j hij)).trans_left hyj.2

/-- The condensation has no cycle. -/
theorem condensationAdj_acyclic (hrs : r ≤ s) (x : V) : ¬ TransGen (CondensationAdj s r) x x := by
  intro h
  obtain ⟨y, hxy, hyx⟩ := TransGen.head'_iff.1 h
  refine hxy.1 ⟨(hxy.transGen hrs).to_reflTransGen, ?_⟩
  exact reflTransGen_closed (fun a b hab => (hab.transGen hrs).to_reflTransGen) y x hyx

end Relation
