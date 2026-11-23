module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Relation

/-!
# Ordering by source position, pulling dependencies forward

`List.pullOrder L d` orders the elements of `L` (given in source order) so that dependencies come
first. It goes through `L` in order; before writing an element it first writes, recursively, each
of its dependencies not yet written (taken in the order of `L`). So an element keeps its source
position unless some earlier element needs it, in which case it is moved forward to just before
the first element that needs it.

This is a depth-first topological sort, visiting the elements and their dependencies in the order
of `L`. Mathlib has no topological sort on lists.

## Main statements

* `List.pullOrder_spec`: if `d` has no cycle, the result is a reordering of `L` in which every
  element comes after its dependencies.
-/

@[expose] public section

namespace List.PullOrder

variable {U : Type*} [DecidableEq U] (L : List U) (d : U → U → Prop) [DecidableRel d]

/-- The elements of `L` not on the current path. Decreases with each nested visit. -/
def unvisited (stack : List U) : Nat :=
  (L.filter (· ∉ stack)).length

theorem unvisited_lt {stack : List U} {u : U} (hu : u ∈ L) (hs : u ∉ stack) :
    unvisited L (u :: stack) < unvisited L stack := by
  unfold unvisited
  have : L.filter (· ∉ u :: stack) = (L.filter (· ∉ stack)).filter (· ≠ u) := by
    rw [List.filter_filter]
    congr 1
    funext x
    simp
  rw [this, List.length_filter_lt_length_iff_exists]
  exact ⟨u, List.mem_filter.2 ⟨hu, by simpa using hs⟩, by simp⟩

mutual
/-- Visit `u`: unless it is already written, on the current path `stack`, or not in `L`, first
visit its dependencies (in the order of `L`), then write `u`. -/
def visit (stack : List U) (u : U) (done : List U) : List U :=
  if _h : u ∈ L ∧ u ∉ stack ∧ u ∉ done then
    visitList (u :: stack) (L.filter (d u)) done ++ [u]
  else done
termination_by (unvisited L stack, 0)
decreasing_by exact Prod.Lex.left _ _ (unvisited_lt L _h.1 _h.2.1)

/-- Visit each element of a list in turn. -/
def visitList (stack : List U) : List U → List U → List U
  | [], done => done
  | v :: vs, done => visitList stack vs (visit stack v done)
termination_by vs => (unvisited L stack, vs.length + 1)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.right _ (by simp)
end


/-- A valid partial output: no duplicates, only elements of `L`, and every element comes after its
dependencies in `L`. -/
def Valid (done : List U) : Prop :=
  done.Nodup ∧ (∀ x ∈ done, x ∈ L) ∧
    ∀ x ∈ done, ∀ y ∈ L, d x y → y ∈ done ∧ done.idxOf y < done.idxOf x

omit [DecidableRel d] in
theorem valid_nil : Valid L d [] := by simp [Valid]

omit [DecidableRel d] in
/-- Appending an element whose dependencies are all already written keeps the output valid. -/
theorem valid_append {done : List U} {u : U} (hv : Valid L d done) (huL : u ∈ L)
    (hud : u ∉ done) (hdeps : ∀ y ∈ L, d u y → y ∈ done) : Valid L d (done ++ [u]) := by
  obtain ⟨hnd, hsub, hbefore⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b hb
    simp at hb
    rintro rfl
    exact hud (hb ▸ ha)
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hsub x hx
    · simp at hx; exact hx ▸ huL
  · intro x hx y hy hxy
    have hyd : y ∈ done → (done ++ [u]).idxOf y = done.idxOf y := fun h =>
      List.idxOf_append_of_mem h
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨hyd', hlt⟩ := hbefore x hx y hy hxy
      exact ⟨List.mem_append_left _ hyd', by
        rw [hyd hyd', List.idxOf_append_of_mem hx]; exact hlt⟩
    · simp at hx; subst hx
      have hyd' := hdeps y hy hxy
      refine ⟨List.mem_append_left _ hyd', ?_⟩
      rw [hyd hyd', List.idxOf_append_of_notMem hud]
      simp [List.idxOf_lt_length_of_mem hyd']

omit [DecidableRel d] in
/-- A valid partial output is closed under dependencies in `L`. -/
theorem Valid.mem_of_reflTransGen {done : List U} (hv : Valid L d done) {a b : U} (ha : a ∈ done)
    (hab : Relation.ReflTransGen (fun u v => d u v ∧ v ∈ L) a b) : b ∈ done := by
  induction hab with
  | refl => exact ha
  | tail _ hbc ih => exact (hv.2.2 _ ih _ hbc.2 hbc.1).1

/-- `res` extends `done` with elements not on the path `stack`. -/
def Extends (stack done res : List U) : Prop :=
  ∃ e, res = done ++ e ∧ ∀ x ∈ e, x ∉ stack

variable {L d}

/-- The correctness invariants of `visit` and `visitList`, by induction on the number of elements
not on the path. -/
theorem visit_spec (hacyc : ∀ x, ¬ Relation.TransGen d x x) :
    ∀ n stack, unvisited L stack = n →
      (∀ u done, Valid L d done → (∀ s ∈ stack, Relation.TransGen d s u) →
        Valid L d (visit L d stack u done) ∧ Extends stack done (visit L d stack u done) ∧
        (u ∈ L → u ∈ visit L d stack u done ∨ u ∈ stack) ∧
        (∀ x ∈ visit L d stack u done,
          x ∈ done ∨ Relation.ReflTransGen (fun u v => d u v ∧ v ∈ L) u x)) ∧
      (∀ vs done, Valid L d done → (∀ v ∈ vs, ∀ s ∈ stack, Relation.TransGen d s v) →
        Valid L d (visitList L d stack vs done) ∧ Extends stack done (visitList L d stack vs done) ∧
        (∀ v ∈ vs, v ∈ L → v ∈ visitList L d stack vs done ∨ v ∈ stack) ∧
        (∀ x ∈ visitList L d stack vs done,
          x ∈ done ∨ ∃ v ∈ vs, Relation.ReflTransGen (fun u v => d u v ∧ v ∈ L) v x)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro stack hn
  -- First the statement about `visit`, using the induction hypothesis for the longer path.
  have hvisit : ∀ u done, Valid L d done → (∀ s ∈ stack, Relation.TransGen d s u) →
      Valid L d (visit L d stack u done) ∧ Extends stack done (visit L d stack u done) ∧
      (u ∈ L → u ∈ visit L d stack u done ∨ u ∈ stack) ∧
      (∀ x ∈ visit L d stack u done,
        x ∈ done ∨ Relation.ReflTransGen (fun u v => d u v ∧ v ∈ L) u x) := by
    intro u done hv hpath
    rw [visit]
    split
    · rename_i h
      obtain ⟨huL, hus, hud⟩ := h
      have hlt := unvisited_lt L huL hus
      obtain ⟨-, hlist⟩ := ih _ (hn ▸ hlt) (u :: stack) rfl
      have hpath' : ∀ v ∈ L.filter (d u), ∀ s ∈ u :: stack, Relation.TransGen d s v := by
        intro v hv s hs
        have hduv := (List.mem_filter.1 hv).2
        simp only [decide_eq_true_eq] at hduv
        rcases List.mem_cons.1 hs with rfl | hs
        · exact Relation.TransGen.single hduv
        · exact (hpath s hs).tail hduv
      obtain ⟨hv', ⟨e, he, hens⟩, hcov, hreach⟩ := hlist _ done hv hpath'
      set done' := visitList L d (u :: stack) (L.filter (d u)) done
      have hud' : u ∉ done' := by
        rw [he]
        intro hu
        rcases List.mem_append.1 hu with hu | hu
        · exact hud hu
        · exact hens u hu (List.mem_cons_self)
      have hdeps : ∀ y ∈ L, d u y → y ∈ done' := by
        intro y hy hduy
        rcases hcov y (List.mem_filter.2 ⟨hy, by simpa using hduy⟩) hy with h | h
        · exact h
        · rcases List.mem_cons.1 h with rfl | h
          · exact absurd (Relation.TransGen.single hduy) (hacyc y)
          · exact absurd ((hpath y h).tail hduy) (hacyc y)
      refine ⟨valid_append L d hv' huL hud' hdeps, ⟨e ++ [u], by rw [he, List.append_assoc], ?_⟩,
        fun _ => Or.inl (by simp), ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact fun hxs => hens x hx (List.mem_cons_of_mem _ hxs)
        · simp at hx; exact hx ▸ hus
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · rcases hreach x hx with h | ⟨v, hv, hvx⟩
          · exact Or.inl h
          · have hv := List.mem_filter.1 hv
            exact Or.inr (Relation.ReflTransGen.head ⟨by simpa using hv.2, hv.1⟩ hvx)
        · simp at hx; exact Or.inr (hx ▸ .refl)
    · rename_i h
      refine ⟨hv, ⟨[], by simp, by simp⟩, fun huL => ?_, fun x hx => Or.inl hx⟩
      by_cases hus : u ∈ stack
      · exact Or.inr hus
      · exact Or.inl (by by_contra hud; exact h ⟨huL, hus, hud⟩)
  refine ⟨hvisit, ?_⟩
  -- Then the statement about `visitList`, by induction on the list.
  intro vs
  induction vs with
  | nil =>
    intro done hv _
    rw [visitList]
    exact ⟨hv, ⟨[], by simp, by simp⟩, by simp, fun x hx => Or.inl hx⟩
  | cons v vs ihvs =>
    intro done hv hpath
    rw [visitList]
    obtain ⟨hv1, ⟨e1, he1, hens1⟩, hcov1, hreach1⟩ :=
      hvisit v done hv (hpath v List.mem_cons_self)
    obtain ⟨hv2, ⟨e2, he2, hens2⟩, hcov2, hreach2⟩ :=
      ihvs _ hv1 (fun w hw => hpath w (List.mem_cons_of_mem _ hw))
    refine ⟨hv2, ⟨e1 ++ e2, by rw [he2, he1, List.append_assoc], ?_⟩, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hens1 x hx
      · exact hens2 x hx
    · intro w hw hwL
      rcases List.mem_cons.1 hw with rfl | hw
      · rcases hcov1 hwL with h | h
        · exact Or.inl (he2 ▸ List.mem_append_left _ h)
        · exact Or.inr h
      · exact hcov2 w hw hwL
    · intro x hx
      rcases hreach2 x hx with h | ⟨w, hw, hwx⟩
      · rcases hreach1 x h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨v, List.mem_cons_self, h⟩
      · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hwx⟩

theorem visitList_append (stack a b done : List U) :
    visitList L d stack (a ++ b) done = visitList L d stack b (visitList L d stack a done) := by
  induction a generalizing done with
  | nil => rw [List.nil_append, visitList.eq_1]
  | cons x xs ih => rw [List.cons_append, visitList.eq_2, visitList.eq_2, ih]

end List.PullOrder

namespace List

open PullOrder

variable {U : Type*} [DecidableEq U] (L : List U) (d : U → U → Prop) [DecidableRel d]

/-- The elements of `L`, ordered by source position with dependencies pulled forward. -/
def pullOrder : List U :=
  visitList L d [] L []

variable {L d}

/-- If `d` has no cycle, `pullOrder L d` contains exactly the elements of `L`, once each, and every
element comes after its dependencies. -/
theorem pullOrder_spec (hacyc : ∀ x, ¬ Relation.TransGen d x x) :
    (pullOrder L d).Nodup ∧ (∀ x, x ∈ pullOrder L d ↔ x ∈ L) ∧
      ∀ (a b : Nat) (ha : a < (pullOrder L d).length) (hb : b < (pullOrder L d).length),
        d (pullOrder L d)[a] (pullOrder L d)[b] → b < a := by
  unfold pullOrder
  obtain ⟨-, hlist⟩ := visit_spec hacyc _ [] rfl
  obtain ⟨⟨hnd, hsub, hbefore⟩, -, hcov, -⟩ := hlist L [] (valid_nil L d) (by simp)
  refine ⟨hnd, fun x => ⟨hsub x, fun hx => ?_⟩, ?_⟩
  · rcases hcov x hx hx with h | h
    · exact h
    · simp at h
  · intro a b ha hb hab
    have hx := List.getElem_mem ha
    obtain ⟨-, hlt⟩ := hbefore _ hx _ (hsub _ (List.getElem_mem hb)) hab
    rwa [hnd.idxOf_getElem, hnd.idxOf_getElem] at hlt

/-- Elements are ordered by their first user: if some `r` needs `x` (or is `x`) and comes, by `pos`,
before everything that needs `y` (or is `y`), then `x` comes before `y`. Here `L` is in increasing
order of `pos`, and "needs" means depending on, directly or not, through elements of `L`. -/
theorem pullOrder_idxOf_lt (hacyc : ∀ x, ¬ Relation.TransGen d x x) (pos : U → ℕ)
    (hL : L.Pairwise (fun a b => pos a < pos b)) {r x y : U} (hr : r ∈ L)
    (hrx : Relation.ReflTransGen (fun u v => d u v ∧ v ∈ L) r x)
    (hry : ∀ v ∈ L, Relation.ReflTransGen (fun u v => d u v ∧ v ∈ L) v y → pos r < pos v) :
    (pullOrder L d).idxOf x < (pullOrder L d).idxOf y := by
  obtain ⟨p, q, hpq⟩ := List.append_of_mem hr
  obtain ⟨hvisit, hlist⟩ := visit_spec (L := L) hacyc _ [] rfl
  -- Split the run into the elements before `r`, `r` itself, and the elements after `r`.
  obtain ⟨hv1, -, -, hreach1⟩ := hlist p [] (valid_nil L d) (by simp)
  obtain ⟨hv2, -, hcov2, hreach2⟩ := hvisit r (visitList L d [] p []) hv1 (by simp)
  set D := visit L d [] r (visitList L d [] p [])
  obtain ⟨-, ⟨e, he, -⟩, -, -⟩ := hlist q D hv2 (by simp)
  have hfinal : pullOrder L d = D ++ e := by
    have : pullOrder L d = visitList L d [] (p ++ r :: q) [] := by
      unfold pullOrder; rw [← hpq]
    rw [this, visitList_append, visitList.eq_2, ← he]
  -- After visiting `r`, everything `r` needs is written, but not `y`.
  have hxD : x ∈ D :=
    Valid.mem_of_reflTransGen L d hv2 ((hcov2 hr).resolve_right List.not_mem_nil) hrx
  have hyD : y ∉ D := by
    intro hyD
    rcases hreach2 y hyD with h | h
    · rcases hreach1 y h with h | ⟨v, hv, hvy⟩
      · simp at h
      · have h1 := hry v (by rw [hpq]; exact List.mem_append_left _ hv) hvy
        have h2 := (List.pairwise_append.1 (hpq ▸ hL)).2.2 v hv r List.mem_cons_self
        omega
    · exact absurd (hry r hr h) (Nat.lt_irrefl _)
  rw [hfinal, List.idxOf_append_of_mem hxD, List.idxOf_append_of_notMem hyD]
  exact Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem hxD) (Nat.le_add_right _ _)

end List
