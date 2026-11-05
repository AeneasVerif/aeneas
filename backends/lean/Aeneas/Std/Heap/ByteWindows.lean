module

public import Aeneas.Std.Heap.Ranges
import all Aeneas.Std.Heap.Resources

@[expose] public section

namespace Aeneas.Std.HeapWP

open SepLogic

/-- Focus a byte window for an arbitrary computation and put its neighbors back.
    In particular, sequential windows may overlap; separation is only used
    between one window and its neighbors during that computation. -/
theorem replace_window.spec (p q : RawPtr U8) (base : BasePtr)
    (old new : List Cell) (start width : Nat)
    (bound : start + width ≤ old.length) (length : new.length = width)
    (prov : q.provenance = p.provenance)
    (address : q.address.val = p.address.val + start)
    (c : Result α)
    (run : Triple (block Repr.u8 q base ((old.drop start).take width)) c
      (fun _ => block Repr.u8 q base new)) :
    Triple (block Repr.u8 p base old) c
      (fun _ => block Repr.u8 p base (old.take start ++ new ++ old.drop (start + width))) := by
  intro h F s hp hd hm hi
  have split := block_append Repr.u8 p q base (old.take start) (old.drop start) prov
    (by simpa [List.length_take, Nat.min_eq_left (show start ≤ old.length by agrind)] using address)
    (by simp [Repr.u8]) h
  rw [List.take_append_drop] at split
  obtain ⟨front, rest, apart, joined, prefixCells, lower, aligned, restEq⟩ := split.mp hp
  let chunk := (old.drop start).take width
  let tail := old.drop (start + width)
  have chunkLen : chunk.length = width := by simp [chunk]; agrind
  have restList : old.drop start = chunk ++ tail := by
    simpa [chunk, tail, List.drop_drop] using
      (List.take_append_drop width (old.drop start)).symm
  let suffix : Assertion := fun h =>
    h = cellsHeap base q.provenance (q.offsetFrom base + width) tail
  have focused : sep (block Repr.u8 q base chunk) suffix rest := by
    refine ⟨cellsHeap base q.provenance (q.offsetFrom base) chunk,
      cellsHeap base q.provenance (q.offsetFrom base + width) tail, ?_, ?_,
      ⟨lower, aligned, rfl⟩, rfl⟩
    · simpa [chunkLen] using disjoint_cellsHeap_append base q.provenance (q.offsetFrom base) chunk tail
    · rw [restEq, restList, cellsHeap_append, chunkLen]
  have restFrame : rest.Disjoint (front ∪ F) :=
    Fragment.disjoint_union_right.mpr
      ⟨apart.symm, (Fragment.disjoint_union_left.mp (joined ▸ hd)).2⟩
  have restMatch : Fragment.Matches s (rest ∪ (front ∪ F)) := by
    simp only [joined, Fragment.matches_union] at hm ⊢
    tauto
  apply Spec.mono (frame (R := suffix) run rest (front ∪ F) s focused restFrame restMatch hi)
  rintro result s₁ ⟨rest₁, disjoint, matching, inv, a, b, _, rfl, point, rfl⟩
  have offset : q.offsetFrom base = p.offsetFrom base + start := by
    have := hp.1
    simp only [RawPtr.offsetFrom]
    agrind
  refine ⟨front ∪ (a ∪ cellsHeap base q.provenance (q.offsetFrom base + width) tail),
    ?_, ?_, inv, hp.1, hp.2.1, ?_⟩
  · exact Fragment.disjoint_union_left.mpr
      ⟨(Fragment.disjoint_union_left.mp (joined ▸ hd)).1,
        (Fragment.disjoint_union_right.mp disjoint).2⟩
  · simp only [Fragment.matches_union] at matching ⊢
    tauto
  · rw [cellsHeap_append, cellsHeap_append, prefixCells.2.2, point.2.2]
    simp [prov, offset, length, List.length_take,
      Nat.min_eq_left (show start ≤ old.length by agrind), Fragment.union_assoc, Nat.add_assoc, tail]

end Aeneas.Std.HeapWP
