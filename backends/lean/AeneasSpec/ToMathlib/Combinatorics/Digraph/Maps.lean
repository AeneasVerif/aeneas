module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation

/-!
# The image of a digraph under a map

`Digraph.map f G` has an edge from `f a` to `f b` for every edge from `a` to `b` in `G`, as
`SimpleGraph.map` does for simple graphs. Unlike `SimpleGraph.map`, it keeps the self loops that
arise when `f a = f b`.
-/

@[expose] public section

namespace Digraph

variable {V W : Type*}

/-- The image of `G` under `f`: `a` is adjacent to `b` when they are the images of adjacent
vertices of `G`. -/
protected def map (f : V → W) (G : Digraph V) : Digraph W where
  Adj := Relation.Map G.Adj f f

@[simp]
theorem map_adj {f : V → W} {G : Digraph V} {a b : W} :
    (G.map f).Adj a b ↔ ∃ u v, G.Adj u v ∧ f u = a ∧ f v = b :=
  Iff.rfl

theorem map_adj_apply {f : V → W} {G : Digraph V} {u v : V} (h : G.Adj u v) :
    (G.map f).Adj (f u) (f v) :=
  ⟨u, v, h, rfl, rfl⟩

instance {f : V → W} {G : Digraph V} {a b : W} [Decidable (Relation.Map G.Adj f f a b)] :
    Decidable ((G.map f).Adj a b) :=
  ‹Decidable _›

end Digraph
