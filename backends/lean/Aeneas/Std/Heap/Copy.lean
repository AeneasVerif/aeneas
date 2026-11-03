module

public import Aeneas.Std.Heap.Ranges
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Lemmas
import all Aeneas.Std.Heap.Specs
import all Aeneas.Std.Heap.Resources

@[expose] public section

namespace Aeneas.Std

theorem Heap.copyBytes_eq_write (repr : Repr T) (source destination : RawPtr T)
    (value : T) (data : Vector Byte repr.size) (encoded : repr.encode value data)
    (old : Vector Byte repr.size) (depth : Nat) (s : Heap) (src dst : Block)
    (hs : s.allocations source.provenance = some src)
    (hd : s.allocations destination.provenance = some dst)
    (ls : s.live src = true) (ld : s.live dst = true)
    (lowerS : src.bptr.val ≤ source.address.val) (lowerD : dst.bptr.val ≤ destination.address.val)
    (alignD : repr.align.val ∣ destination.address.val)
    (boundS : source.offsetFrom src.bptr + repr.size ≤ src.repr.length)
    (boundD : destination.offsetFrom dst.bptr + repr.size ≤ dst.repr.length)
    (selectedS : repr.select src.bytes (source.offsetFrom src.bptr) boundS =
      data.map (Cell.shared depth))
    (selectedD : repr.select dst.bytes (destination.offsetFrom dst.bptr) boundD =
      old.map (Cell.shared 0))
    (size : 0 < repr.size) :
    Heap.copyBytes source destination repr.size s =
      Heap.write repr destination value data encoded s := by
  have read : (List.range repr.size).mapM (fun i =>
      (src.repr[source.offsetFrom src.bptr + i]?).bind fun cell => match cell with
      | .shared _ byte => some byte
      | .borrowed => none) = some data.toList := by
    have each : ∀ i (bound : i < data.toList.length),
        ((src.repr[source.offsetFrom src.bptr + i]?).bind fun cell => match cell with
          | .shared _ byte => some byte
          | .borrowed => none) = some data.toList[i] := by
      intro i bound
      have index : i < repr.size := by simpa using bound
      have cell := Repr.select_getElem? repr src.bytes (source.offsetFrom src.bptr) boundS i index
      rw [selectedS] at cell
      have lookup : src.repr[source.offsetFrom src.bptr + i]? = some (.shared depth data[i]) := by
        simpa [Block.bytes, index] using cell.symm
      simp [lookup]
    simpa only [Vector.length_toList, List.range_eq_range'] using
      mapM_range'_some data.toList 0 (by simpa using each)
  have writable : ((dst.repr.drop (destination.offsetFrom dst.bptr)).take repr.size).all
      (fun cell => cell.depth == some 0) = true := by
    have selection := congrArg Vector.toList selectedD
    simp only [Repr.select_toList, Block.bytes, Vector.toList_mk] at selection
    rw [selection]
    simp
  have upperS : source.address.val + repr.size ≤ src.bptr.val + src.repr.length := by
    simp only [RawPtr.offsetFrom] at boundS
    agrind
  have upperD : destination.address.val + repr.size ≤ dst.bptr.val + dst.repr.length := by
    simp only [RawPtr.offsetFrom] at boundD
    agrind
  have writing : Repr.write repr dst.bytes (destination.offsetFrom dst.bptr) value data encoded =
      some (repr.update dst.bytes (destination.offsetFrom dst.bptr) boundD (data.map (Cell.shared 0))) := by
    simp [Repr.write, size, boundD, selectedD, Repr.writeBytes_shared]
  simp only [Heap.copyBytes, hs, hd, Bind.bind, Option.bind, ls, ld, lowerS, lowerD,
    upperS, upperD, decide_true, Bool.true_and, ↓reduceIte,
    Heap.write, Heap.modify, alignD]
  simp only [Option.bind] at read
  erw [read, writing]
  simp only [writable, ↓reduceIte, Repr.update_toList,
    Block.bytes, Vector.toList_mk, Cell.full, Vector.toList_map, List.append_assoc]

namespace SepLogic

/-- A stored pointer itself supports copying its provenance, even after its
    pointee view has been retired. No permission to dereference it is implied. -/
theorem supportsValue_pointer_slot (slot : RawPtr (RawPtr T)) (base : BasePtr)
    (target : RawPtr T) (depth : Nat) {h : Fragment}
    (hp : pointsTo (Repr.pointer T) slot base target depth h) :
    SupportsValue (Repr.pointer T) target h := by
  obtain ⟨data, encoded, _, _, cells⟩ := hp
  change data = Repr.pointerEncoding target at encoded
  subst data
  intro q carried
  have eq := (Repr.pointer_carries target q).mp carried
  subst q
  refine .inr ⟨slot.provenance, slot.offsetFrom base, base, depth, target.cast Unit, 0, ?_, rfl⟩
  rw [cells]
  refine ⟨0, by simp [Repr.pointer], ?_⟩
  simp only [Nat.add_zero, Vector.getElem_toList]
  apply congrArg (Resource.cell slot.provenance (slot.offsetFrom base) base)
  change Cell.shared depth (.pointer (target.cast Unit) 0) =
    ((Repr.pointerEncoding target).map (Cell.shared depth))[0]
  simp [Repr.pointerEncoding]

end SepLogic

namespace HeapWP

open SepLogic

def copy_pointer (source destination : RawPtr (RawPtr T)) : Result Unit :=
  Result.checkedModify (fun s₀ _ s₁ => Heap.copyBytes source destination pointerWidth s₀ = some s₁)

/-- Actual untyped byte copying preserves all symbolic pointer lanes. The
    source slot supplies provenance support; the pointee need not be live. -/
theorem copy_pointer_writable.spec (source destination : RawPtr (RawPtr T))
    (sourceBase destinationBase : BasePtr) (target : RawPtr T)
    (old : Vector Byte (Repr.pointer T).size) (depth : Nat) :
    Triple (sep (block (Repr.pointer T) destination destinationBase (old.map (Cell.shared 0)).toList)
      (pointsTo (Repr.pointer T) source sourceBase target depth))
      (copy_pointer source destination)
      (fun _ => sep (pointsTo (Repr.pointer T) destination destinationBase target)
        (pointsTo (Repr.pointer T) source sourceBase target depth)) := by
  intro h F s hp disjoint matched invariant
  have write := SepLogic.write_supported.spec (Repr.pointer T)
    destination destinationBase old target (pointsTo (Repr.pointer T) source sourceBase target depth)
    (fun _ hs => supportsValue_pointer_slot source sourceBase target depth hs) (by change 0 < 8; decide)
    h F s hp disjoint matched invariant
  obtain ⟨a, b, hab, hh, dest, src⟩ := hp
  have parts := (Fragment.matches_union _ _ _).mp matched |>.1
  rw [hh, Fragment.matches_union] at parts
  obtain ⟨sourceBytes, sourceEncoding, lowerS, _, sourceCells⟩ := src
  change sourceBytes = Repr.pointerEncoding target at sourceEncoding
  obtain ⟨lowerD, alignD, destCells⟩ := dest
  have sourceMatch := sourceCells ▸ parts.2
  have destMatch := destCells ▸ parts.1
  obtain ⟨src, boundS, hs, ls, baseS, selectedS⟩ :=
    bytes_of_matches (by change 0 < 8; decide) sourceMatch
  obtain ⟨dst, boundD, hd, ld, baseD, selectedD⟩ :=
    bytes_of_matches (by change 0 < 8; decide) destMatch
  subst sourceBase
  subst destinationBase
  have copy (bytes : Vector Byte (Repr.pointer T).size)
      (encoded : (Repr.pointer T).encode target bytes) :
      Heap.copyBytes source destination pointerWidth s =
        Heap.write (Repr.pointer T) destination target bytes encoded s := by
    have same : bytes = sourceBytes := encoded.trans sourceEncoding.symm
    subst bytes
    have copied := Heap.copyBytes_eq_write (Repr.pointer T) source destination target sourceBytes
      sourceEncoding old depth s src dst hs hd ls ld lowerS lowerD alignD boundS boundD
      selectedS selectedD (by change 0 < 8; decide)
    change Heap.copyBytes source destination pointerWidth s =
      Heap.write (Repr.pointer T) destination target sourceBytes sourceEncoding s at copied
    simpa only [sourceEncoding] using copied
  apply Spec.checkedModify.mpr
  constructor
  · obtain ⟨_, next, bytes, encoded, run⟩ := write.1
    exact ⟨(), next, by rw [copy bytes encoded]; exact run⟩
  · intro _ next run
    exact write.2 () next ⟨sourceBytes, sourceEncoding, by rw [← copy sourceBytes sourceEncoding]; exact run⟩

theorem copy_pointer.spec (source destination : RawPtr (RawPtr T))
    (sourceBase destinationBase : BasePtr) (target old : RawPtr T) (depth : Nat) :
    Triple (sep (pointsTo (Repr.pointer T) destination destinationBase old)
      (pointsTo (Repr.pointer T) source sourceBase target depth))
      (copy_pointer source destination)
      (fun _ => sep (pointsTo (Repr.pointer T) destination destinationBase target)
        (pointsTo (Repr.pointer T) source sourceBase target depth)) := by
  rintro h F s ⟨a, b, hab, hh, destinationPoint, sourceCells⟩ hd hm hi
  obtain ⟨bytes, _, destinationCells⟩ := destinationPoint
  exact copy_pointer_writable.spec source destination sourceBase destinationBase target bytes depth
    h F s ⟨a, b, hab, hh, destinationCells, sourceCells⟩ hd hm hi

end HeapWP

end Aeneas.Std
