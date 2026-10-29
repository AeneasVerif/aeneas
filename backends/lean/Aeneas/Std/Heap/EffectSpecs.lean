module

public import Aeneas.Std.Heap.Effects
public import Aeneas.Std.Heap.Borrowing
public import Aeneas.Std.Alloc.Boxed
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Alloc.Boxed

@[expose] public section

namespace Aeneas.Std.HeapWP

open SepLogic

theorem read.spec (p : RawPtr T) (value : T) (depth : Nat) :
    Triple (block p [.shared depth value]) (RawPtr.read p)
      (fun x h => x = value ∧ block p [.shared depth value] h) :=
  Triple.guardedModify (SepLogic.read.spec p value depth)

theorem write.spec (p : RawPtr T) (old : Cell T) (value : T) (hw : old.writable) :
    Triple (block p [old]) (MutRawPtr.write p value) (fun _ => pointsTo p value) :=
  Triple.guardedModify (SepLogic.write.spec p old value hw)

theorem add.spec (p : RawPtr T) (cs : List (Cell T)) (own : Bool)
    (start target : Nat) (count : Usize)
    (hstart : start ≤ cs.length) (htarget : target ≤ cs.length)
    (hcount : (count.val : Int) = (target : Int) - start) :
    Triple (sep (alloc p cs.length own) (block p cs))
      (RawPtr.add (⟨p.base, p.index + start⟩ : RawPtr T) count)
      (fun result h => result = ⟨p.base, p.index + target⟩ ∧
        sep (alloc p cs.length own) (block p cs) h) := by
  simpa [RawPtr.add, State.offset, hcount] using Triple.guardedModify
    (SepLogic.offsetWholeBlock.spec p cs own start target hstart htarget)

theorem offset.spec (p : RawPtr T) (cs : List (Cell T)) (own : Bool)
    (start target : Nat) (count : Isize)
    (hstart : start ≤ cs.length) (htarget : target ≤ cs.length)
    (hcount : count.val = (target : Int) - start) :
    Triple (sep (alloc p cs.length own) (block p cs))
      (RawPtr.offset (⟨p.base, p.index + start⟩ : RawPtr T) count)
      (fun result h => result = ⟨p.base, p.index + target⟩ ∧
        sep (alloc p cs.length own) (block p cs) h) := by
  simpa [RawPtr.offset, State.offset, hcount] using Triple.guardedModify
    (SepLogic.offsetWholeBlock.spec p cs own start target hstart htarget)

theorem intoRaw.spec (value : T) :
    Triple emp (alloc.boxed.Box.into_raw value)
      (fun p => sep (alloc p 1 true) (pointsTo p value)) := by
  simpa [alloc.boxed.Box.into_raw, State.alloc, State.newBlock, Cell.full] using
    Triple.guardedModify (SepLogic.newBlock.spec [value] true)

theorem fromRaw.spec (p : RawPtr T) (value : T) :
    Triple (sep (alloc p 1 true) (pointsTo p value)) (alloc.boxed.Box.from_raw p)
      (fun x h => x = value ∧ emp h) := by
  unfold alloc.boxed.Box.from_raw
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun x h hp => (sep_and_left (x = value)
      (pointsTo p value) (alloc p 1 true) h).mp hp)
    (frame (R := alloc p 1 true) (read.spec p value 0)))
  intro x
  apply Triple.pure_pre
  intro hx
  subst x
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (Triple.guardedModify
      (SepLogic.freeBlock.spec p [.shared 0 value] true (by simp [Cell.writable]))))
  intro _
  exact Triple.pure emp value

theorem borrowRange.spec (p : RawPtr T) (values : List T)
    (hsize : values = [] ∨ 0 < layout.byteLength T) :
    Triple (block p (Cell.full values)) (RawPtr.borrowRange p values.length)
      (fun x h => x = values ∧ block p (List.replicate values.length .borrowed) h) :=
  Triple.guardedModify (SepLogic.borrowRange.spec p values hsize)

theorem endBorrowRange.spec (p : RawPtr T) (values : List T) :
    Triple (block p (List.replicate values.length .borrowed)) (RawPtr.endBorrowRange p values)
      (fun _ => block p (Cell.full values)) :=
  Triple.guardedModify (SepLogic.endBorrowRange.spec p values)

theorem shareRange.spec (p : RawPtr T) (values : List T) (depth : Nat) :
    Triple (block p (values.map (Cell.shared depth))) (RawPtr.shareRange p values.length)
      (fun x h => x = values ∧ block p (values.map (Cell.shared (depth + 1))) h) :=
  Triple.guardedModify (SepLogic.shareRange.spec p values depth)

theorem endShareRange.spec (p : RawPtr T) (values : List T) (depth : Nat) :
    Triple (block p (values.map (Cell.shared (depth + 1))))
      (RawPtr.endShareRange p values)
      (fun _ => block p (values.map (Cell.shared depth))) :=
  Triple.guardedModify (SepLogic.endShareRange.spec p values depth)

end Aeneas.Std.HeapWP
