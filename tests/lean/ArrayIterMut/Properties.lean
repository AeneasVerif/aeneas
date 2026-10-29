module
public import Aeneas
public import ArrayIterMut.ArrayIterMut
public section

open Aeneas Aeneas.Std Result core.slice.iter

/-! Proofs about the extracted `tests/src/array-iter-mut.rs`, using the specification theorems of
the models of `IntoIterator for &mut [T; N]` and `IterMut::next` through `step`.

The loop over `&mut [i32; N]` is extracted in backward style: each iteration returns the advanced
iterator and a back function which accumulates the writes done so far. The invariant `Inv` says
that the iterator ranges over the original slice, and that the back function adds `2` to the
elements already visited and leaves the others as they are. -/

namespace array_iter_mut

/-- The loop invariant, for the original slice `a`. -/
def Inv (a : Slice Std.I32) (it : IterMut Std.I32) (back : IterMut Std.I32 → IterMut Std.I32) :
    Prop :=
  it.slice = a ∧ it.i ≤ a.length ∧
  ∀ it' : IterMut Std.I32, it'.slice.length = a.length →
    (back it').slice.length = a.length ∧
    ∀ j < a.length, ((back it').slice.val[j]!).val =
      if j < it.i then (a.val[j]!).val + 2 else (it'.slice.val[j]!).val

/-- The loop adds `2` to every element of the slice. -/
theorem add_two_loop.spec (a : Slice Std.I32) (it : IterMut Std.I32)
    (back : IterMut Std.I32 → IterMut Std.I32)
    (hbound : ∀ j < a.length, (a.val[j]!).val + 2 ≤ Std.I32.max)
    (hinv : Inv a it back) :
    add_two_loop it back ⦃ res => res.slice.length = a.length ∧
      ∀ j < a.length, (res.slice.val[j]!).val = (a.val[j]!).val + 2 ⦄ := by
  unfold add_two_loop
  step with loop.spec_decr_nat
    (fun (p : IterMut Std.I32 × (IterMut Std.I32 → IterMut Std.I32)) => a.length - p.1.i)
    (fun p => Inv a p.1 p.2)
    (fun (res : IterMut Std.I32) => res.slice.length = a.length ∧
      ∀ j < a.length, (res.slice.val[j]!).val = (a.val[j]!).val + 2)
  · rintro ⟨it, back⟩ ⟨hs, hi, hb⟩
    dsimp only at hs hi hb
    unfold add_two_loop.body
    step*
    · -- `none`: the iterator is at the end, every element has been visited
      rename_i ho
      rw [ho] at o_post
      have hge : a.length ≤ it.i := by
        simpa [hs] using List.getElem?_eq_none_iff.mp o_post.symm
      have hl : iter1.slice.length = a.length := by simp [o_post1, hs]
      obtain ⟨h1, h2⟩ := hb iter1 hl
      rw [o_post3]
      refine ⟨h1, fun j hj => ?_⟩
      rw [h2 j hj]
      simp [show j < it.i by agrind]
    · -- `some elem`: the addition doesn't overflow
      rename_i ho
      rw [ho] at o_post
      obtain ⟨hlt, helem⟩ := List.getElem?_eq_some_iff.mp o_post.symm
      have := hbound it.i (by simpa [hs] using hlt)
      have : a.val[it.i]! = elem := by rw [← hs, getElem!_pos it.slice.val it.i hlt]; exact helem
      agrind
    · -- `some elem`: the invariant holds for the next iteration
      rename_i ho
      rw [ho] at o_post
      obtain ⟨hlt, helem⟩ := List.getElem?_eq_some_iff.mp o_post.symm
      have hlt' : it.i < a.length := by simpa [hs] using hlt
      have helem' : a.val[it.i]! = elem := by
        rw [← hs, getElem!_pos it.slice.val it.i hlt]; exact helem
      have hi1 : iter1.i = it.i + 1 := by simp [o_post2, hlt]
      refine ⟨⟨by simp [o_post1, hs], by agrind, fun it' hl => ?_⟩, by agrind⟩
      simp only [o_post4 hlt]
      obtain ⟨h1, h2⟩ := hb { slice := it'.slice.setAtNat it.i elem1, i := it'.i } (by simp [hl])
      refine ⟨h1, fun j hj => ?_⟩
      rw [h2 j hj, hi1]
      by_cases hji : j < it.i
      · simp [hji, show j < it.i + 1 by agrind]
      · by_cases hje : j = it.i
        · subst hje
          simp only [hji, show it.i < it.i + 1 by agrind, ↓reduceIte]
          rw [Slice.getElem!_Nat_setAtNat_eq _ _ _ (by simpa [hl] using hlt'), helem']
          agrind
        · simp [hji, show ¬ j < it.i + 1 by agrind,
            Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm hje)]
  · solve_by_elim

/-- `add_two` adds `2` to every element of the array (when this doesn't overflow): the
    documentation example `[1, 2, 4]` becomes `[3, 4, 6]`. -/
theorem add_two_spec {N : Std.Usize} (x : Array Std.I32 N)
    (h : ∀ j < N.val, (x.val[j]!).val + 2 ≤ Std.I32.max) :
    add_two x ⦃ y => ∀ j < N.val, (y.val[j]!).val = (x.val[j]!).val + 2 ⦄ := by
  unfold add_two
  step
  step with add_two_loop.spec iter.slice
  · -- the invariant holds initially: nothing visited, `back` is the identity
    exact ⟨rfl, by simp [iter_post1], fun it' hl => ⟨hl, fun j hj => by simp [iter_post1]⟩⟩
  · intro j hj
    have hl : back.slice.length = iter.slice.length := back_post
    have hn : iter.slice.length = N.val := by simp [Slice.length, iter_post]
    rw [iter_post2 back (by rw [hl, hn]), back_post1 j (by rw [hn]; exact hj), iter_post]

end array_iter_mut
