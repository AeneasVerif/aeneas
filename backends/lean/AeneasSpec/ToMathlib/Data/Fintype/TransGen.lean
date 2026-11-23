module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Logic.Relation

/-!
# Decidability of reachability on a finite type

For a decidable relation `r` on a finite type, `Relation.reachFrom r x` computes the set of
vertices reachable from `x` in one or more steps, by repeatedly adding successors until nothing
changes.

## Main statements

* `Relation.mem_reachFrom`: `y ∈ reachFrom r x ↔ TransGen r x y`.
* Instances deciding `Relation.TransGen r` and `Relation.ReflTransGen r`.
-/

@[expose] public section

namespace Relation

variable {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop) [DecidableRel r]

/-- The vertices reachable from `x` in one step. -/
def succFinset (x : V) : Finset V :=
  Finset.univ.filter (r x)

/-- One round of closing `S` under `r`: add the successors of every vertex of `S`. -/
def closeStep (S : Finset V) : Finset V :=
  S ∪ S.biUnion (succFinset r)

theorem subset_closeStep (S : Finset V) : S ⊆ closeStep r S :=
  Finset.subset_union_left

/-- Close `S` under `r`: repeat `closeStep` until nothing changes. -/
def closeFinset (S : Finset V) : Finset V :=
  if _h : closeStep r S ⊆ S then S else closeFinset (closeStep r S)
termination_by Fintype.card V - S.card
decreasing_by
  have hss : S ⊂ closeStep r S :=
    Finset.ssubset_iff_subset_ne.2 ⟨subset_closeStep r S, fun e => _h (e ▸ Finset.Subset.refl _)⟩
  have h1 := Finset.card_lt_card hss
  have h2 := Finset.card_le_univ (closeStep r S)
  omega

/-- The vertices reachable from `x` in one or more steps. -/
def reachFrom (x : V) : Finset V :=
  closeFinset r (succFinset r x)

theorem subset_closeFinset (S : Finset V) : S ⊆ closeFinset r S := by
  induction S using closeFinset.induct r with
  | case1 S h => rw [closeFinset]; simp only [h, ↓reduceDIte]; exact Finset.Subset.refl _
  | case2 S h ih =>
    rw [closeFinset]; simp only [h, ↓reduceDIte]
    exact (subset_closeStep r S).trans ih

/-- The closure is closed under taking successors. -/
theorem succFinset_subset_closeFinset (S : Finset V) :
    ∀ y ∈ closeFinset r S, succFinset r y ⊆ closeFinset r S := by
  induction S using closeFinset.induct r with
  | case1 S h =>
    rw [closeFinset]; simp only [h, ↓reduceDIte]
    intro y hy z hz
    exact h (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨y, hy, hz⟩))
  | case2 S h ih =>
    rw [closeFinset]; simp only [h, ↓reduceDIte]
    exact ih

/-- Every vertex of the closure of `S` satisfies any property that holds on `S` and is preserved
by `r`. -/
theorem closeFinset_induction (P : V → Prop) (S : Finset V) (hS : ∀ y ∈ S, P y)
    (hr : ∀ y z, P y → r y z → P z) : ∀ y ∈ closeFinset r S, P y := by
  induction S using closeFinset.induct r with
  | case1 S h =>
    rw [closeFinset]; simp only [h, ↓reduceDIte]
    exact hS
  | case2 S h ih =>
    rw [closeFinset]; simp only [h, ↓reduceDIte]
    apply ih
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact hS y hy
    · obtain ⟨x, hx, hxy⟩ := Finset.mem_biUnion.1 hy
      exact hr x y (hS x hx) (Finset.mem_filter.1 hxy).2

theorem mem_reachFrom {x y : V} : y ∈ reachFrom r x ↔ TransGen r x y := by
  constructor
  · intro hy
    refine closeFinset_induction r (TransGen r x) (succFinset r x) ?_ ?_ y hy
    · intro z hz
      exact TransGen.single (Finset.mem_filter.1 hz).2
    · intro z w hz hzw
      exact hz.tail hzw
  · intro h
    induction h with
    | single hxy =>
      exact subset_closeFinset r _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxy⟩)
    | tail _ hbc ih =>
      exact succFinset_subset_closeFinset r _ _ ih (Finset.mem_filter.2 ⟨Finset.mem_univ _, hbc⟩)

instance TransGen.decidableRel : DecidableRel (TransGen r) := fun x y =>
  decidable_of_iff (y ∈ reachFrom r x) (mem_reachFrom r)

instance ReflTransGen.decidableRel : DecidableRel (ReflTransGen r) := fun x y =>
  decidable_of_iff (y = x ∨ TransGen r x y) reflTransGen_iff_eq_or_transGen.symm

end Relation
