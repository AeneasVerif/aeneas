module

public import RawRyuMwe.Storage
import all Aeneas.Std.Heap.Resources

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace scalar_mwe

/-- Focus one byte window while retaining another explicit footprint (for example
    the other endpoint of a copy); preserve both neighboring byte ranges. -/
theorem window_frame.spec (p q : RawPtr U8) (base : BasePtr)
    (old new : List Cell) (start width : Nat) (R S : Assertion)
    (post : α → Prop) (bound : start + width ≤ old.length) (length : new.length = width)
    (prov : q.provenance = p.provenance)
    (address : q.address.val = p.address.val + start) (c : Result α)
    (run : HeapWP.Triple (block Repr.u8 q base ((old.drop start).take width) ∗ R) c
      (fun result h => post result ∧ (block Repr.u8 q base new ∗ S) h)) :
    HeapWP.Triple (block Repr.u8 p base old ∗ R) c
      (fun result h => post result ∧
        (block Repr.u8 p base (old.take start ++ new ++ old.drop (start + width)) ∗ S) h) := by
  intro h F s₀ ⟨whole, other, apart, joined, hp, hr⟩ hd hm hi
  let front := old.take start
  let chunk := (old.drop start).take width
  let tail := old.drop (start + width)
  have frontLen : front.length = start := by simp [front]; agrind
  have chunkLen : chunk.length = width := by simp [chunk]; agrind
  have listEq : old = front ++ chunk ++ tail := by
    simp only [front, chunk, tail, ← List.drop_drop]
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  obtain ⟨lower, aligned, cells⟩ := hp
  have offset : q.offsetFrom base = p.offsetFrom base + start := by
    simp only [RawPtr.offsetFrom]
    agrind
  let a := cellsHeap base p.provenance (p.offsetFrom base) front
  let b := cellsHeap base p.provenance (p.offsetFrom base + start) chunk
  let d := cellsHeap base p.provenance (p.offsetFrom base + start + width) tail
  have split : whole = a ∪ b ∪ d := by
    rw [cells, listEq, cellsHeap_append, cellsHeap_append]
    simp [a, b, d, frontLen, chunkLen, Nat.add_assoc]
  have ab := disjoint_cellsHeap_append base p.provenance (p.offsetFrom base) front chunk
  have abd := disjoint_cellsHeap_append base p.provenance (p.offsetFrom base) (front ++ chunk) tail
  have disjoint : (b ∪ other).Disjoint (a ∪ d ∪ F) := by
    have ab' : a.Disjoint b := by simpa [a, b, frontLen] using ab
    have adbd : a.Disjoint d ∧ b.Disjoint d := by
      simpa [a, b, d, frontLen, chunkLen, cellsHeap_append, Nat.add_assoc,
        Fragment.disjoint_union_left] using abd
    have wo := split ▸ apart
    have all := split ▸ (joined ▸ hd)
    simp only [Fragment.disjoint_union_left] at wo all
    have ba := ab'.symm
    have oa := wo.1.1.symm
    have od := wo.2.symm
    simp only [Fragment.disjoint_union_left, Fragment.disjoint_union_right]
    tauto
  have matching : Fragment.Matches s₀ ((b ∪ other) ∪ (a ∪ d ∪ F)) := by
    simp only [joined, split, Fragment.matches_union] at hm ⊢
    tauto
  have focus : (block Repr.u8 q base chunk ∗ R) (b ∪ other) := by
    refine ⟨b, other, ?_, rfl, ⟨by agrind, by simp [Repr.u8], ?_⟩, hr⟩
    · have wo := split ▸ apart
      exact (Fragment.disjoint_union_left.mp (Fragment.disjoint_union_left.mp wo).1).2
    · simp [b, offset, prov]
  apply HeapWP.Spec.mono (run (b ∪ other) (a ∪ d ∪ F) s₀ focus disjoint matching hi)
  rintro result s₁ ⟨h₁, hd₁, hm₁, hi₁, resultPost, b₁, other₁, bo, eq, point, hs⟩
  have bd := (Fragment.disjoint_union_right.mp hd₁)
  have o1ad : other₁.Disjoint (a ∪ d) :=
    (Fragment.disjoint_union_left.mp (eq ▸ bd.1)).2
  let whole₁ := a ∪ b₁ ∪ d
  refine ⟨whole₁ ∪ other₁, ?_, ?_, hi₁, resultPost, whole₁, other₁, ?_, rfl, ?_, hs⟩
  · have oldF := split ▸ (joined ▸ hd)
    simp only [whole₁, Fragment.disjoint_union_left] at oldF ⊢
    have newF := Fragment.disjoint_union_left.mp (eq ▸ bd.2)
    exact ⟨⟨⟨oldF.1.1.1, newF.1⟩, oldF.1.2⟩, newF.2⟩
  · simp only [whole₁, eq, Fragment.matches_union] at hm₁ ⊢
    tauto
  · simp only [whole₁, Fragment.disjoint_union_left]
    have oa := Fragment.disjoint_union_right.mp o1ad
    exact ⟨⟨oa.1.symm, bo⟩, oa.2.symm⟩
  · refine ⟨lower, aligned, ?_⟩
    dsimp only [whole₁]
    rw [cellsHeap_append, cellsHeap_append, point.2.2]
    simp [a, d, front, frontLen, prov, offset, length, Nat.add_assoc, tail]

end scalar_mwe
