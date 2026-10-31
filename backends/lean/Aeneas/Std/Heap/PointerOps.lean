module

public import Aeneas.Std.Core.PtrOps
public import Aeneas.Std.Heap.Initialization
import all Aeneas.Std.Core.PtrOps
import all Aeneas.Std.Heap.Separation

@[expose] public section

namespace Aeneas.Std.HeapWP

open SepLogic

theorem pointsTo_separated (repr : Repr T) (p q : RawPtr T) (left right : T) (h : Fragment)
    (hp : sep (pointsTo repr p left) (pointsTo repr q right) h) :
    p.base ≠ q.base ∨ p.byteOffset.val + repr.size ≤ q.byteOffset.val ∨
      q.byteOffset.val + repr.size ≤ p.byteOffset.val := by
  obtain ⟨_, _, hd, _, ⟨a, _, _, rfl⟩, ⟨b, _, _, rfl⟩⟩ := hp
  by_cases hb : p.base = q.base
  · right
    by_contra hover
    have hpa : p.byteOffset.val < q.byteOffset.val + repr.size := by grind
    have hqb : q.byteOffset.val < p.byteOffset.val + repr.size := by grind
    by_cases hoff : p.byteOffset.val ≤ q.byteOffset.val
    · have ha : q.byteOffset.val - p.byteOffset.val < repr.size := by grind
      have hsize : 0 < repr.size := by grind
      have hc := hd _ ⟨q.byteOffset.val - p.byteOffset.val, by simpa using ha, rfl⟩
        _ ⟨0, by simpa using hsize, rfl⟩
      simp [Resource.Compatible, Resource.base, Resource.key, hb,
        show p.byteOffset.val + (q.byteOffset.val - p.byteOffset.val) = q.byteOffset.val by grind] at hc
    · have hqa : p.byteOffset.val - q.byteOffset.val < repr.size := by grind
      have hsize : 0 < repr.size := by grind
      have hc := hd _ ⟨0, by simpa using hsize, rfl⟩
        _ ⟨p.byteOffset.val - q.byteOffset.val, by simpa using hqa, rfl⟩
      simp [Resource.Compatible, Resource.base, Resource.key, hb,
        show q.byteOffset.val + (p.byteOffset.val - q.byteOffset.val) = p.byteOffset.val by grind] at hc
  · exact Or.inl hb

theorem frame_value (ht : Triple P c (fun x h => x = value ∧ Q h)) :
    Triple (sep P R) c (fun x h => x = value ∧ sep Q R h) :=
  Triple.conseq (fun _ h => h) (fun _ _ h => (sep_and_left _ _ _ _).mp h) (frame ht)

/-- Replacement returns the exact old value and installs the requested value. -/
theorem replace.spec (repr : Repr T) (p : RawPtr T) (old value : T)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p old) (RawPtr.replace repr p value)
      (fun result h => result = old ∧ pointsTo repr p value 0 h) := by
  unfold RawPtr.replace
  apply Triple.bind (read.spec repr p old 0 hsize)
  intro result
  apply Triple.pure_pre
  intro he
  subst result
  apply Triple.bind (write.spec repr p old value hsize)
  intro _
  exact Triple.pure _ old

/-- Swapping disjoint footprints exchanges their exact decoded values. -/
theorem swap.spec (repr : Repr T) (p q : RawPtr T) (left right : T)
    (hsize : 0 < repr.size) :
    Triple (sep (pointsTo repr p left) (pointsTo repr q right))
      (RawPtr.swap repr p q)
      (fun _ => sep (pointsTo repr p right) (pointsTo repr q left)) := by
  unfold RawPtr.swap
  apply Triple.conseq
    (P' := fun h =>
      (p.base ≠ q.base ∨ p.byteOffset.val + repr.size ≤ q.byteOffset.val ∨
        q.byteOffset.val + repr.size ≤ p.byteOffset.val) ∧
      sep (pointsTo repr p left) (pointsTo repr q right) h)
    (fun h hp => ⟨pointsTo_separated repr p q left right h hp, hp⟩) (fun _ _ h => h)
  apply Triple.pure_pre
  intro hdisjoint
  rw [ite_eq_left (Or.imp_right (Or.imp_right Or.inl) hdisjoint)]
  apply Triple.bind (frame_value (R := pointsTo repr q right)
    (read.spec repr p left 0 hsize))
  intro x
  apply Triple.pure_pre
  intro hx
  subst x
  have hr : Triple (sep (pointsTo repr p left) (pointsTo repr q right))
      (q.read repr) (fun result h => result = right ∧
        sep (pointsTo repr p left) (pointsTo repr q right) h) :=
    Triple.conseq (fun _ h => (sep_comm _ _ _).mp h)
      (fun _ _ h => ⟨h.1, (sep_comm _ _ _).mp h.2⟩)
      (frame_value (R := pointsTo repr p left) (read.spec repr q right 0 hsize))
  apply Triple.bind hr
  intro y
  apply Triple.pure_pre
  intro hy
  subst y
  apply Triple.bind (frame (R := pointsTo repr q right)
    (write.spec repr p left right hsize))
  intro _
  exact Triple.conseq (fun _ h => (sep_comm _ _ _).mp h)
    (fun _ _ h => (sep_comm _ _ _).mp h)
    (frame (R := pointsTo repr p right) (write.spec repr q right left hsize))

/-- Swapping a footprint with itself preserves its typed contents. -/
theorem swap_same.spec (repr : Repr T) (p : RawPtr T) (value : T)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value) (RawPtr.swap repr p p)
      (fun _ => pointsTo repr p value) := by
  unfold RawPtr.swap
  simp only [ne_eq, not_true_eq_false, or_true, ite_true]
  apply Triple.bind (read.spec repr p value 0 hsize)
  intro x
  apply Triple.pure_pre
  intro hx
  subst x
  apply Triple.bind (read.spec repr p value 0 hsize)
  intro y
  apply Triple.pure_pre
  intro hy
  subst y
  apply Triple.bind (write.spec repr p value value hsize)
  intro _
  exact write.spec repr p value value hsize

/-- Unaligned reads relax alignment only, not validity or read permissions. -/
theorem read_unaligned.spec (repr : Repr T) (p : RawPtr T) (value : T) (depth : Nat)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr.unaligned p value depth) (RawPtr.read_unaligned repr p)
      (fun result h => result = value ∧ pointsTo repr.unaligned p value depth h) :=
  read.spec repr.unaligned p value depth hsize

/-- Unaligned writes also initialize arbitrary writable bytes. -/
theorem write_unaligned.spec (repr : Repr T) (p : RawPtr T)
    (old : Vector (Option U8) repr.size) (value : T) (hsize : 0 < repr.size) :
    Triple (block repr.unaligned p (old.map (Cell.shared 0)).toList)
      (RawPtr.write_unaligned repr p value) (fun _ => pointsTo repr.unaligned p value) :=
  write_writable.spec repr.unaligned p old value hsize

end Aeneas.Std.HeapWP
