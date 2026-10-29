module

public import RawBox
public import Aeneas.Std.Heap.EffectSpecs

public section

open Aeneas.Std
open Aeneas.Std.SepLogic

namespace raw_box

theorem round_trip_tail.spec (repr : Aeneas.Std.Repr U32) (p : MutRawPtr U32)
    (initial replacement : U32) (hsize : 0 < repr.size) :
    HeapWP.Triple (sep (alloc repr p 1 true) (pointsTo repr p initial))
      (do MutRawPtr.write repr p replacement
          let value ← RawPtr.read repr p
          let _ ← alloc.boxed.Box.from_raw repr p
          pure value)
      (fun value h => value = replacement ∧ emp h) := by
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (HeapWP.frame (R := alloc repr p 1 true)
      (HeapWP.write.spec repr p initial replacement hsize)))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun _ h => h)
    (fun value h hp => (sep_and_left (value = replacement)
      (pointsTo repr p replacement) (alloc repr p 1 true) h).mp hp)
    (HeapWP.frame (R := alloc repr p 1 true) (HeapWP.read.spec repr p replacement 0 hsize)))
  intro value
  apply HeapWP.Triple.pure_pre
  intro hv
  subst value
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ hp => hp.2) (HeapWP.fromRaw.spec repr p replacement hsize))
  intro _
  exact HeapWP.Triple.pure emp replacement

/-- The actual lifecycle consumes its allocation and preserves any matching frame.
The capacity hypothesis is necessary because base identifiers are bounded. -/
theorem round_trip.spec (repr : Aeneas.Std.Repr U32) (initial replacement : U32)
    (hsize : 0 < repr.size) (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (round_trip repr initial replacement)
      (fun value s' => value = replacement ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold round_trip
  apply HeapWP.Spec.bind (HeapWP.intoRaw.spec repr initial s F hi hm hc hfit)
  rintro p s' ⟨_, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono (round_trip_tail.spec repr p initial replacement hsize h F s' hp hd hm' hi')
  rintro value s'' ⟨h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

theorem stored_pointer_tail.spec (repr : Aeneas.Std.Repr U32)
    (pointerRepr : Aeneas.Std.Repr (MutRawPtr U32)) (target : MutRawPtr U32)
    (slot : MutRawPtr (MutRawPtr U32))
    (initial replacement : U32) (hsize : 0 < repr.size) (hptr : 0 < pointerRepr.size) :
    HeapWP.Triple
      (sep (sep (alloc pointerRepr slot 1 true) (pointsTo pointerRepr slot target))
        (sep (alloc repr target 1 true) (pointsTo repr target initial)))
      (do let loaded ← RawPtr.read pointerRepr slot
          MutRawPtr.write repr loaded replacement
          let _ ← alloc.boxed.Box.from_raw pointerRepr slot
          alloc.boxed.Box.from_raw repr target)
      (fun value h => value = replacement ∧ emp h) := by
  let targetOwn := sep (alloc repr target 1 true) (pointsTo repr target initial)
  let slotOwn := sep (alloc pointerRepr slot 1 true) (pointsTo pointerRepr slot target)
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun _ h => h)
    (fun loaded h hp => (sep_and_left (loaded = target) slotOwn targetOwn h).mp hp)
    (HeapWP.frame (R := targetOwn)
      (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
        (fun loaded h hp => (sep_and_left (loaded = target)
          (pointsTo pointerRepr slot target) (alloc pointerRepr slot 1 true) h).mp hp |>.imp_right
            ((sep_comm _ _ h).mp))
        (HeapWP.frame (R := alloc pointerRepr slot 1 true)
          (HeapWP.read.spec pointerRepr slot target 0 hptr)))))
  intro loaded
  apply HeapWP.Triple.pure_pre
  intro he
  subst loaded
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h)
    (HeapWP.frame (R := slotOwn)
      (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
        (fun _ _ h => (sep_comm _ _ _).mp h)
        (HeapWP.frame (R := alloc repr target 1 true)
          (HeapWP.write.spec repr target initial replacement hsize)))))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => (sep_emp_left
      (sep (alloc repr target 1 true) (pointsTo repr target replacement)) h).mp
        (sep_mono (fun _ hp => hp.2) (fun _ h => h) hp))
    (HeapWP.frame (R := sep (alloc repr target 1 true) (pointsTo repr target replacement))
      (HeapWP.fromRaw.spec pointerRepr slot target hptr)))
  intro _
  exact HeapWP.fromRaw.spec repr target replacement hsize

/-- A pointer is encoded in the second allocation using its own explicit
representation, not assumed to fit in one machine word. -/
theorem stored_pointer.spec (repr : Aeneas.Std.Repr U32)
    (pointerRepr : Aeneas.Std.Repr (MutRawPtr U32)) (initial replacement : U32)
    (hsize : 0 < repr.size) (hptr : 0 < pointerRepr.size)
    (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (hptrfit : pointerRepr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 2 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (stored_pointer repr pointerRepr initial replacement)
      (fun value s' => value = replacement ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold stored_pointer
  have hc' : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize := by agrind
  apply HeapWP.Spec.bind (HeapWP.intoRaw.spec repr initial s F hi hm hc' hfit)
  rintro target s₁ ⟨hn, a, haF, hm₁, hi₁, hp⟩
  have hc₁ : s₁.next.val + 1 < 2 ^ UScalarTy.numBits .Usize := by agrind
  apply HeapWP.Spec.bind (HeapWP.intoRaw.spec pointerRepr target s₁ (a ∪ F) hi₁ hm₁ hc₁ hptrfit)
  rintro slot s₂ ⟨_, b, hd, hm₂, hi₂, hq⟩
  obtain ⟨hba, hbF⟩ := Fragment.disjoint_union_right.mp hd
  have hown : sep (sep (alloc pointerRepr slot 1 true) (pointsTo pointerRepr slot target))
      (sep (alloc repr target 1 true) (pointsTo repr target initial)) (b ∪ a) :=
    ⟨b, a, hba, rfl, hq, hp⟩
  have hd' := Fragment.disjoint_union_left.mpr ⟨hbF, haF⟩
  have hm' : Fragment.Matches s₂ (b ∪ a ∪ F) := by
    simpa [Fragment.union_assoc] using hm₂
  apply HeapWP.Spec.mono
    (stored_pointer_tail.spec repr pointerRepr target slot initial replacement hsize hptr
      (b ∪ a) F s₂ hown hd' hm' hi₂)
  rintro value s' ⟨h', _, hm', hi', hv, rfl⟩
  exact ⟨hv, by simpa using hm', hi'⟩

end raw_box

/-- info: 'raw_box.round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box.round_trip.spec

/-- info: 'raw_box.stored_pointer.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box.stored_pointer.spec
