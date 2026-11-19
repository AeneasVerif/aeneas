module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Flatten

/-!
# Splitting a list into equivalence classes

For an equivalence relation `e`, `List.classReps e l` picks one representative per class of `l`:
the first element of each class, in the order of `l`. `List.classOf e l r` is the class of `r`: the
elements of `l` equivalent to `r`, in the order of `l`.

Mathlib's `List.pwFilter (fun x y => ¬ e x y)` also picks one element per class, but the last one
rather than the first.
-/

@[expose] public section

namespace List

variable {α : Type*} (e : α → α → Prop) [DecidableRel e]

/-- The first element of each equivalence class of `l`, in the order of `l`. The head of the list
represents its own class, replacing the representative of that class in the tail. -/
def classReps : List α → List α
  | [] => []
  | x :: xs => x :: (classReps xs).filter (fun r => ¬ e x r)

/-- The elements of `l` equivalent to `r`, in the order of `l`. -/
def classOf (l : List α) (r : α) : List α :=
  l.filter (e r)

variable {e}

theorem mem_classOf {l : List α} {r y : α} : y ∈ classOf e l r ↔ y ∈ l ∧ e r y := by
  simp [classOf]

theorem mem_of_mem_classReps {l : List α} {x : α} (h : x ∈ classReps e l) : x ∈ l := by
  induction l with
  | nil => simp [classReps] at h
  | cons y ys ih =>
    rw [classReps, List.mem_cons, List.mem_filter] at h
    rcases h with rfl | ⟨h, _⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

variable (he : Equivalence e)
include he

/-- Every element of `l` is equivalent to a representative. -/
theorem exists_mem_classReps {l : List α} {x : α} (h : x ∈ l) : ∃ r ∈ classReps e l, e r x := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    by_cases hyx : e y x
    · exact ⟨y, by simp [classReps], hyx⟩
    · have hx : x ∈ ys := by
        rcases List.mem_cons.1 h with rfl | h
        · exact absurd (he.refl _) hyx
        · exact h
      obtain ⟨r, hr, hrx⟩ := ih hx
      refine ⟨r, ?_, hrx⟩
      rw [classReps, List.mem_cons, List.mem_filter]
      exact Or.inr ⟨hr, by simpa using fun hyr => hyx (he.trans hyr hrx)⟩

/-- Equivalent representatives are equal. -/
theorem eq_of_mem_classReps {l : List α} {r s : α} (hr : r ∈ classReps e l)
    (hs : s ∈ classReps e l) (hrs : e r s) : r = s := by
  induction l with
  | nil => simp [classReps] at hr
  | cons y ys ih =>
    rw [classReps, List.mem_cons, List.mem_filter] at hr hs
    rcases hr with rfl | ⟨hr, hyr⟩ <;> rcases hs with rfl | ⟨hs, hys⟩
    · rfl
    · simp at hys; exact absurd hrs hys
    · simp at hyr; exact absurd (he.symm hrs) hyr
    · exact ih hr hs

theorem nodup_classReps (l : List α) : (classReps e l).Nodup := by
  induction l with
  | nil => simp [classReps]
  | cons y ys ih =>
    rw [classReps]
    refine List.nodup_cons.2 ⟨fun hy => ?_, ih.filter _⟩
    simp [he.refl y] at hy

omit he in
theorem classReps_sublist (l : List α) : classReps e l <+ l := by
  induction l with
  | nil => simp [classReps]
  | cons y ys ih =>
    rw [classReps]
    exact (List.filter_sublist.trans ih).cons_cons y

/-- In a list ordered by a reflexive `R`, a representative is related to the members of its
class: it is the first of them. -/
theorem Pairwise.rel_of_mem_classReps {R : α → α → Prop} (hR : ∀ a, R a a) {l : List α}
    (hl : l.Pairwise R) {r x : α} (hr : r ∈ classReps e l) (hx : x ∈ l) (hrx : e r x) : R r x := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.pairwise_cons] at hl
    rw [classReps, List.mem_cons, List.mem_filter] at hr
    rcases hr with rfl | ⟨hr, hyr⟩ <;> rcases List.mem_cons.1 hx with rfl | hx
    · exact hR _
    · exact hl.1 x hx
    · simp at hyr; exact absurd (he.symm hrx) hyr
    · exact ih hl.2 hr hx

omit he in
/-- For a list `rs` covering `l`, the classes of `rs` together contain exactly the elements of
`l`. -/
theorem mem_flatten_map_classOf {l rs : List α} (hcover : ∀ x ∈ l, ∃ r ∈ rs, e r x)
    {y : α} :
    y ∈ (rs.map (classOf e l)).flatten ↔ y ∈ l := by
  simp only [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨_, ⟨r, _, rfl⟩, hy⟩
    exact (mem_classOf.1 hy).1
  · intro hy
    obtain ⟨r, hr, hry⟩ := hcover y hy
    exact ⟨_, ⟨r, hr, rfl⟩, mem_classOf.2 ⟨hy, hry⟩⟩

/-- Classes of pairwise inequivalent elements are disjoint, so together they have no duplicates. -/
theorem nodup_flatten_map_classOf {l rs : List α} (hl : l.Nodup) (hrs : rs.Nodup)
    (hinj : ∀ r ∈ rs, ∀ s ∈ rs, e r s → r = s) :
    (rs.map (classOf e l)).flatten.Nodup := by
  rw [List.nodup_flatten]
  refine ⟨fun c hc => ?_, ?_⟩
  · obtain ⟨r, _, rfl⟩ := List.mem_map.1 hc
    exact hl.filter _
  · rw [List.pairwise_map]
    refine hrs.imp_of_mem fun {r s} hr hs hne => ?_
    intro y hyr hys
    have hr' := (mem_classOf.1 hyr).2
    have hs' := (mem_classOf.1 hys).2
    exact hne (hinj r hr s hs (he.trans hr' (he.symm hs')))

end List
