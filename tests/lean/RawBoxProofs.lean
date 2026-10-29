module

public import RawBox
public import Aeneas.Std.Heap.EffectSpecs

public section

open Aeneas.Std
open Aeneas.Std.SepLogic

namespace raw_box

/-- The extracted Rust lifecycle returns the replacement and consumes its allocation
resources while preserving every disjoint frame. -/
theorem round_trip.spec (initial replacement : U32) :
    HeapWP.Triple emp (round_trip initial replacement)
      (fun value h => value = replacement ∧ emp h) := by
  unfold round_trip
  apply HeapWP.Triple.bind (HeapWP.intoRaw.spec initial)
  intro p
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (HeapWP.frame (R := alloc p 1 true)
      (HeapWP.write.spec p (.shared 0 (some initial)) replacement rfl)))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun _ h => h)
    (fun value h hp => (sep_and_left (value = replacement)
      (pointsTo p replacement) (alloc p 1 true) h).mp hp)
    (HeapWP.frame (R := alloc p 1 true) (HeapWP.read.spec p replacement 0)))
  intro value
  apply HeapWP.Triple.pure_pre
  intro hv
  subst value
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ hp => hp.2) (HeapWP.fromRaw.spec p replacement))
  intro _
  exact HeapWP.Triple.pure emp replacement

/-- Loading a raw pointer from a second allocation preserves the separately owned
target. Both allocation resources are consumed, with no pointer-equality assumption. -/
theorem stored_pointer.spec (initial replacement : U32) :
    HeapWP.Triple emp (stored_pointer initial replacement)
      (fun value h => value = replacement ∧ emp h) := by
  unfold stored_pointer
  apply HeapWP.Triple.bind (HeapWP.intoRaw.spec initial)
  intro target
  let targetOwn := sep (alloc target 1 true) (pointsTo target initial)
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun h hp => (sep_emp_left targetOwn h).mpr hp) (fun _ _ h => h)
    (HeapWP.frame (R := targetOwn) (HeapWP.intoRaw.spec target)))
  intro slot
  let slotOwn := sep (alloc slot 1 true) (pointsTo slot target)
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun _ h => h)
    (fun loaded h hp => (sep_and_left (loaded = target)
      slotOwn targetOwn h).mp hp)
    (HeapWP.frame (R := targetOwn)
      (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
        (fun loaded h hp => (sep_and_left (loaded = target)
          (pointsTo slot target) (alloc slot 1 true) h).mp hp |>.imp_right
            ((sep_comm _ _ h).mp))
        (HeapWP.frame (R := alloc slot 1 true) (HeapWP.read.spec slot target 0)))))
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
        (HeapWP.frame (R := alloc target 1 true)
          (HeapWP.write.spec target (.shared 0 (some initial)) replacement rfl)))))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => (sep_emp_left
      (sep (alloc target 1 true) (pointsTo target replacement)) h).mp
        (sep_mono (fun _ hp => hp.2) (fun _ h => h) hp))
    (HeapWP.frame (R := sep (alloc target 1 true) (pointsTo target replacement))
      (HeapWP.fromRaw.spec slot target)))
  intro _
  exact HeapWP.fromRaw.spec target replacement

end raw_box

/--
info: 'raw_box.round_trip.spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Block,
 Block.bytes,
 Block.create,
 Block.create_bytes,
 Block.create_exists,
 Block.create_extent,
 Block.create_view,
 Block.extent,
 Block.setCell,
 Block.set_bytes_length,
 Block.set_exists,
 Block.set_extent,
 Block.set_frame,
 Block.set_view,
 Block.view,
 Block.view_bound,
 Block.view_bytes,
 Block.view_unique,
 Heap.repr]
-/
#guard_msgs in
#print axioms raw_box.round_trip.spec

/--
info: 'raw_box.stored_pointer.spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Block,
 Block.bytes,
 Block.create,
 Block.create_bytes,
 Block.create_exists,
 Block.create_extent,
 Block.create_view,
 Block.extent,
 Block.setCell,
 Block.set_bytes_length,
 Block.set_exists,
 Block.set_extent,
 Block.set_frame,
 Block.set_view,
 Block.view,
 Block.view_bound,
 Block.view_bytes,
 Block.view_unique,
 Heap.repr]
-/
#guard_msgs in
#print axioms raw_box.stored_pointer.spec
