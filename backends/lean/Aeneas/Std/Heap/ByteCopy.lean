module

public import Aeneas.Std.Heap.Copy
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Separation

@[expose] public section

namespace Aeneas.Std

/-- Byte-specialized copy: unlike `copyBytes`, overlapping ranges are rejected.
    No compiler mapping is registered; the heap adapter supplies the byte count. -/
def RawPtr.copy_nonoverlapping_bytes (source destination : RawPtr U8) (count : Nat) :
    Result Unit :=
  Result.checkedModify fun s₀ (_ : Unit) s₁ =>
    (source.address.val + count ≤ destination.address.val ∨
      destination.address.val + count ≤ source.address.val) ∧
    Heap.copyBytes source destination count s₀ = some s₁

namespace HeapWP

open SepLogic

/-- A byte copy preserves the exact source representation, not a decoded/re-encoded
    approximation. Unique encodings let this reuse the existing framed write rule. -/
theorem copy_bytes.spec (repr : Repr T) (source destination : RawPtr U8)
    (sourceBase destinationBase : BasePtr) (value : T)
    (old : Vector Byte repr.size) (depth : Nat)
    (positive : 0 < repr.size) (noPointers : ∀ q, ¬ repr.Carries value q)
    (unique : ∀ a b, repr.encode value a → repr.encode value b → a = b)
    (apart : source.address.val + repr.size ≤ destination.address.val ∨
      destination.address.val + repr.size ≤ source.address.val) :
    Triple (sep
      (block repr (destination.cast T) destinationBase (old.map (Cell.shared 0)).toList)
      (pointsTo repr (source.cast T) sourceBase value depth))
      (RawPtr.copy_nonoverlapping_bytes source destination repr.size)
      (fun _ => sep (pointsTo repr (destination.cast T) destinationBase value)
        (pointsTo repr (source.cast T) sourceBase value depth)) := by
  intro h F s hp disjoint matched invariant
  have write := SepLogic.frame
    (SepLogic.write.spec repr (destination.cast T) destinationBase old value noPointers positive)
    h F s hp disjoint matched invariant
  obtain ⟨a, b, _, hh, dest, src⟩ := hp
  have parts := (Fragment.matches_union _ _ _).mp matched |>.1
  rw [hh, Fragment.matches_union] at parts
  obtain ⟨sourceBytes, sourceEncoding, lowerS, _, sourceCells⟩ := src
  obtain ⟨lowerD, alignD, destCells⟩ := dest
  obtain ⟨src, boundS, hs, ls, baseS, selectedS⟩ :=
    bytes_of_matches positive (sourceCells ▸ parts.2)
  obtain ⟨dst, boundD, hd, ld, baseD, selectedD⟩ :=
    bytes_of_matches positive (destCells ▸ parts.1)
  subst sourceBase
  subst destinationBase
  have copy (bytes : Vector Byte repr.size) (encoded : repr.encode value bytes) :
      Heap.copyBytes source destination repr.size s =
        Heap.write repr (destination.cast T) value bytes encoded s := by
    have same := unique bytes sourceBytes encoded sourceEncoding
    subst bytes
    exact Heap.copyBytes_eq_write repr (source.cast T) (destination.cast T)
      value sourceBytes sourceEncoding old depth s src dst hs hd ls ld lowerS lowerD
      alignD boundS boundD selectedS selectedD positive
  apply Spec.checkedModify.mpr
  constructor
  · obtain ⟨_, next, bytes, encoded, run⟩ := write.1
    exact ⟨(), next, apart, by rw [copy bytes encoded]; exact run⟩
  · rintro _ next ⟨_, run⟩
    exact write.2 () next
      ⟨sourceBytes, sourceEncoding, by rw [← copy sourceBytes sourceEncoding]; exact run⟩

end HeapWP
end Aeneas.Std
