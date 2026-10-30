module

public import Aeneas.Std.Heap.Effects
public import Aeneas.Std.Heap.Borrowing
public import Aeneas.Std.Alloc.Boxed
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Alloc.Boxed

/-! Contracts for actual Rust-effect computations. Allocation is stated at its
input state, with a capacity hypothesis; local access and cleanup retain framed
separation triples. -/

@[expose] public section

namespace Aeneas.Std.HeapWP

open SepLogic

theorem read.spec (repr : Repr T) (p : RawPtr T) (value : T) (depth : Nat)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value depth) (RawPtr.read repr p)
      (fun x h => x = value ∧ pointsTo repr p value depth h) :=
  Triple.guardedModify (SepLogic.read.spec repr p value depth hsize)

theorem write.spec (repr : Repr T) (p : RawPtr T) (old value : T)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p old) (MutRawPtr.write repr p value)
      (fun _ => pointsTo repr p value) := by
  unfold MutRawPtr.write
  apply Triple.bind (Triple.choose (pointsTo repr p old) repr value)
  intro data
  exact Triple.guardedModify
    (SepLogic.write_encoding.spec repr p old value data.val data.property hsize)

theorem readRange_single.spec (repr : Repr T) (p : RawPtr T) (value : T) (depth : Nat)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value depth) (RawPtr.readRange repr p 1)
      (fun values h => values = [value] ∧ pointsTo repr p value depth h) := by
  apply Triple.guardedModify
  intro h F s hp hd hm hi
  have hr : Heap.readRange repr p 1 s = some [value] := by
    rw [Heap.readRange_single, read_of_pointsTo hsize hp ((Fragment.matches_union _ _ _).mp hm).1]
    rfl
  refine ⟨⟨[value], s, hr, rfl⟩, ?_⟩
  rintro values s' ⟨hv, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hv.symm.trans hr), hp⟩

private theorem read_transfer_single.spec (repr : Repr T) (p : RawPtr T) (value : T)
    (depth : Nat) (change : Heap → Option Heap) (Q : Assertion) (hsize : 0 < repr.size)
    (ht : SepLogic.Triple (pointsTo repr p value depth)
      (fun s (_ : Unit) s' => change s = some s') (fun _ => Q)) :
    SepLogic.Triple (pointsTo repr p value depth)
      (fun s values s' => Heap.readRange repr p 1 s = some values ∧ change s = some s')
      (fun values h => values = [value] ∧ Q h) := by
  intro h F s hp hd hm hi
  have hr : Heap.readRange repr p 1 s = some [value] := by
    rw [Heap.readRange_single, read_of_pointsTo hsize hp ((Fragment.matches_union _ _ _).mp hm).1]
    rfl
  obtain ⟨⟨_, s₁, hc⟩, hpost⟩ := ht h F s hp hd hm hi
  refine ⟨⟨[value], s₁, hr, hc⟩, ?_⟩
  rintro values s₁ ⟨hv, hc⟩
  obtain ⟨h₁, hd₁, hm₁, hi₁, hq⟩ := hpost () s₁ hc
  exact ⟨h₁, hd₁, hm₁, hi₁, Option.some.inj (hv.symm.trans hr), hq⟩

theorem borrowRange_single.spec (repr : Repr T) (p : RawPtr T) (value : T)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value) (RawPtr.borrowRange repr p 1)
      (fun values h => values = [value] ∧
        block repr p (Vector.replicate repr.size .borrowed).toList h) := by
  apply Triple.guardedModify
  unfold State.borrowRange
  simp only [Heap.borrowRange_single]
  exact read_transfer_single.spec repr p value 0 (Heap.borrow repr p) _ hsize
    (SepLogic.borrow_pointsTo.spec repr p value hsize)

theorem borrow.spec (repr : Repr T) (p : RawPtr T) (value : T) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value) (RawPtr.borrow repr p)
      (fun result h => result = value ∧
        block repr p (Vector.replicate repr.size .borrowed).toList h) := by
  unfold RawPtr.borrow
  apply Triple.bind (borrowRange_single.spec repr p value hsize)
  intro values
  apply Triple.pure_pre
  intro hv
  subst values
  exact Triple.pure _ value

theorem shareRange_single.spec (repr : Repr T) (p : RawPtr T) (value : T) (depth : Nat)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value depth) (RawPtr.shareRange repr p 1)
      (fun values h => values = [value] ∧ pointsTo repr p value (depth + 1) h) := by
  apply Triple.guardedModify
  unfold State.shareRange
  simp only [Heap.shareRange_single]
  exact read_transfer_single.spec repr p value depth (Heap.share repr p) _ hsize
    (SepLogic.share_pointsTo.spec repr p value depth hsize)

theorem endShareRange_single.spec (repr : Repr T) (p : RawPtr T) (value : T) (depth : Nat)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value (depth + 1)) (RawPtr.endShareRange repr p [value])
      (fun _ => pointsTo repr p value depth) := by
  apply Triple.guardedModify
  intro h F s hp hd hm hi
  have hr : Heap.readRange repr p 1 s = some [value] := by
    rw [Heap.readRange_single, read_of_pointsTo hsize hp ((Fragment.matches_union _ _ _).mp hm).1]
    rfl
  obtain ⟨⟨_, s₁, hc⟩, hpost⟩ := SepLogic.endShare_pointsTo.spec repr p value depth hsize
    h F s hp hd hm hi
  refine ⟨⟨(), s₁, hr, ?_⟩, ?_⟩
  · simpa only [List.length_singleton, Heap.endShareRange_single] using hc
  · rintro _ s₁ ⟨_, hc⟩
    exact hpost () s₁ (by simpa only [List.length_singleton, Heap.endShareRange_single] using hc)

theorem endBorrowRange_single.spec (repr : Repr T) (p : RawPtr T) (value : T)
    (hsize : 0 < repr.size) :
    Triple (block repr p (Vector.replicate repr.size .borrowed).toList)
      (RawPtr.endBorrowRange repr p [value]) (fun _ => pointsTo repr p value) := by
  unfold RawPtr.endBorrowRange
  apply Triple.bind (Triple.chooseList _ repr [value])
  rintro ⟨encodings, hd⟩
  have he : ∃ encoding, encodings = [encoding] ∧ repr.decode encoding = some value := by
    cases encodings
    · simp at hd
    · rename_i encoding tail
      have h := List.cons.inj hd
      have ht : tail = [] := by simpa using h.2
      exact ⟨encoding, by simp [ht], h.1⟩
  obtain ⟨encoding, rfl, decoded⟩ := he
  apply Triple.guardedModify
  simpa only [Heap.endBorrowRange_single repr p encoding value decoded] using
    SepLogic.endBorrow.spec repr p encoding value decoded hsize

theorem endBorrow.spec (repr : Repr T) (p : RawPtr T) (value : T) (hsize : 0 < repr.size) :
    Triple (block repr p (Vector.replicate repr.size .borrowed).toList)
      (RawPtr.endBorrow repr p value) (fun _ => pointsTo repr p value) :=
  endBorrowRange_single.spec repr p value hsize

theorem offset.spec (repr : Repr T) (p : RawPtr T) (count : Isize) (length : Nat)
    (own : Bool) (hsize : 0 < repr.size) (hstart : p.index.val ≤ length)
    (hlo : 0 ≤ (p.index.val : Int) + count.val)
    (hhi : (p.index.val : Int) + count.val ≤ length)
    (hfit : (p.index.val : Int) + count.val < (2 ^ UScalarTy.numBits .Usize : Nat)) :
    Triple (alloc repr ⟨p.base, ⟨0⟩⟩ length own) (RawPtr.offset repr p count)
      (fun q h => q.base = p.base ∧ (q.index.val : Int) = (p.index.val : Int) + count.val ∧
        alloc repr ⟨p.base, ⟨0⟩⟩ length own h) :=
  Triple.guardedModify (SepLogic.offset.spec repr p count.val length own hsize hstart hlo hhi hfit)

theorem add.spec (repr : Repr T) (p : RawPtr T) (count : Usize) (length : Nat)
    (own : Bool) (hsize : 0 < repr.size) (hstart : p.index.val ≤ length)
    (hhi : p.index.val + count.val ≤ length)
    (hfit : p.index.val + count.val < 2 ^ UScalarTy.numBits .Usize) :
    Triple (alloc repr ⟨p.base, ⟨0⟩⟩ length own) (RawPtr.add repr p count)
      (fun q h => q.base = p.base ∧ q.index.val = p.index.val + count.val ∧
        alloc repr ⟨p.base, ⟨0⟩⟩ length own h) := by
  have hlo : 0 ≤ (p.index.val : Int) + count.val := by agrind
  have hbound : (p.index.val : Int) + count.val ≤ length := by agrind
  have hindex : (p.index.val : Int) + count.val < (2 ^ UScalarTy.numBits .Usize : Nat) := by
    agrind
  apply Triple.conseq (fun _ h => h) ?_
    (Triple.guardedModify (SepLogic.offset.spec repr p count.val length own hsize hstart
      hlo hbound hindex))
  intro q h ⟨hb, hi, hp⟩
  exact ⟨hb, by grind, hp⟩

theorem newBlock.spec (repr : Repr T) (value : T) (own : Bool) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize)
    (hl : repr.size < 2 ^ UScalarTy.numBits .Usize) :
    Spec (RawPtr.newBlock repr [value] own)
      (fun p s' => s'.next.val = s.next.val + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p 1 own) (pointsTo repr p value) h) s := by
  unfold RawPtr.newBlock
  apply Spec.bind (Spec.chooseList repr [value] (fun _ s' => s' = s) s |>.mpr
    (fun _ _ => rfl))
  rintro ⟨encodings, hd⟩ s₀ hs₀
  subst s₀
  have he : ∃ encoding, encodings = [encoding] ∧ repr.decode encoding = some value := by
    cases encodings
    · simp at hd
    · rename_i encoding tail
      have h := List.cons.inj hd
      have ht : tail = [] := by simpa using h.2
      exact ⟨encoding, by simp [ht], h.1⟩
  obtain ⟨encoding, rfl, decoded⟩ := he
  apply Spec.guardedModify.mpr
  obtain ⟨p, s', hs⟩ := Heap.newBlock.enabled repr [encoding] own s hi hc (by simpa using hl)
  refine ⟨⟨p, s', hs⟩, ?_⟩
  intro p s' hs
  obtain ⟨hb, hoff, hn, hown⟩ := newBlock_single.resources hs
  let a := allocHeap repr p.base 1 own
  let b := cellsHeap repr.align p.base 0 (encoding.map (Cell.shared 0 ∘ some)).toList
  have hfresh : ∀ r, (a ∪ b) r → r.base = s.next := by
    rintro r (rfl | ⟨i, hi, rfl⟩)
    · exact hb
    · exact hb
  have hab : a.Disjoint b := by
    rintro _ rfl _ ⟨i, hi, rfl⟩
    right
    simp [Resource.key]
  exact ⟨hn, a ∪ b, fresh_disjoint hi hm hfresh,
    (Fragment.matches_union _ _ _).mpr ⟨hown, newBlock_single.frame hi hm hs⟩,
    Heap.newBlock.inv hi hs, a, b, hab, rfl, ⟨hoff, rfl⟩,
    encoding, decoded, by simp [block, b, hoff]⟩

theorem intoRaw.spec (repr : Repr T) (value : T) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize)
    (hl : repr.size < 2 ^ UScalarTy.numBits .Usize) :
    Spec (alloc.boxed.Box.into_raw repr value)
      (fun p s' => s'.next.val = s.next.val + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p 1 true) (pointsTo repr p value) h) s :=
  newBlock.spec repr value true s F hi hm hc hl

theorem allocExposure.spec (repr : Repr T) (value : T) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize)
    (hl : repr.size < 2 ^ UScalarTy.numBits .Usize) :
    Spec (RawPtr.allocExposure repr [value])
      (fun p s' => s'.next.val = s.next.val + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p 1 false) (pointsTo repr p value) h) s :=
  newBlock.spec repr value false s F hi hm hc hl

theorem read_free.spec (repr : Repr T) (p : RawPtr T) (value : T)
    (own : Bool) (hsize : 0 < repr.size) :
    Triple (sep (alloc repr p 1 own) (pointsTo repr p value))
      (do let value ← RawPtr.read repr p
          Result.guardedModify (fun s (_ : Unit) s' => Heap.freeBlock repr p 1 own s = some s')
          pure value)
      (fun x h => x = value ∧ emp h) := by
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun x h hp => (sep_and_left (x = value)
      (pointsTo repr p value) (alloc repr p 1 own) h).mp hp)
    (frame (R := alloc repr p 1 own) (read.spec repr p value 0 hsize)))
  intro x
  apply Triple.pure_pre
  intro hx
  subst x
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (Triple.guardedModify (free_pointsTo.spec repr p value own)))
  intro _
  exact Triple.pure emp value

theorem fromRaw.spec (repr : Repr T) (p : RawPtr T) (value : T) (hsize : 0 < repr.size) :
    Triple (sep (alloc repr p 1 true) (pointsTo repr p value)) (alloc.boxed.Box.from_raw repr p)
      (fun x h => x = value ∧ emp h) :=
  read_free.spec repr p value true hsize

theorem end_from_mut.spec (repr : Repr T) (p : RawPtr T) (value : T) (hsize : 0 < repr.size) :
    Triple (sep (alloc repr p 1 false) (pointsTo repr p value)) (core.ptr.end_from_mut repr p)
      (fun x h => x = value ∧ emp h) :=
  read_free.spec repr p value false hsize

end Aeneas.Std.HeapWP
