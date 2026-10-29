module

public import RawBox
public import RawReadWriteRead
public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Primitives

public section

open Aeneas.Std
open Aeneas.Std.SepLogic

namespace raw_read_write_read

/-- The manually corrected translation observes both the old and new values. -/
theorem read_write_read.spec (repr : Aeneas.Std.Repr U32) (p : MutRawPtr U32) (initial : U32)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr p initial) (read_write_read repr p)
      (fun result h => result = (initial, 1#u32) ∧ pointsTo repr p 1#u32 0 h) := by
  unfold read_write_read
  apply HeapWP.Triple.bind (HeapWP.read.spec repr p initial 0 hsize)
  intro before
  apply HeapWP.Triple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.Triple.bind (HeapWP.write.spec repr p initial 1#u32 hsize)
  intro _
  apply HeapWP.Triple.bind (HeapWP.read.spec repr p 1#u32 0 hsize)
  intro after
  apply HeapWP.Triple.pure_pre
  intro hafter
  subst after
  exact HeapWP.Triple.pure (pointsTo repr p 1#u32) (initial, 1#u32)

/-- Discarding the first read does not permit reusing it after a write. -/
theorem discarded_read.spec (repr : Aeneas.Std.Repr U32) (p : MutRawPtr U32) (initial : U32)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr p initial) (discarded_read repr p)
      (fun result h => result = 1#u32 ∧ pointsTo repr p 1#u32 0 h) := by
  unfold discarded_read
  apply HeapWP.Triple.bind (HeapWP.read.spec repr p initial 0 hsize)
  intro _
  apply HeapWP.Triple.pure_pre
  intro _
  apply HeapWP.Triple.bind (HeapWP.write.spec repr p initial 1#u32 hsize)
  intro _
  exact HeapWP.read.spec repr p 1#u32 0 hsize

end raw_read_write_read

namespace raw_box

theorem alias_write_tail.spec (repr : Aeneas.Std.Repr U32) (p : MutRawPtr U32)
    (initial replacement : U32) (hsize : 0 < repr.size) :
    HeapWP.Triple (sep (alloc repr p 1 true) (pointsTo repr p initial))
      (do let before ← RawPtr.read repr p
          MutRawPtr.write repr p replacement
          let after ← RawPtr.read repr p
          let _ ← alloc.boxed.Box.from_raw repr p
          pure (before, after))
      (fun result h => result = (initial, replacement) ∧ emp h) := by
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun value h hp => (sep_and_left (value = initial)
      (pointsTo repr p initial) (alloc repr p 1 true) h).mp hp)
    (HeapWP.frame (R := alloc repr p 1 true) (HeapWP.read.spec repr p initial 0 hsize)))
  intro before
  apply HeapWP.Triple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.Triple.bind (HeapWP.frame (R := alloc repr p 1 true)
    (HeapWP.write.spec repr p initial replacement hsize))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun _ h => h)
    (fun value h hp => (sep_and_left (value = replacement)
      (pointsTo repr p replacement) (alloc repr p 1 true) h).mp hp)
    (HeapWP.frame (R := alloc repr p 1 true) (HeapWP.read.spec repr p replacement 0 hsize)))
  intro after
  apply HeapWP.Triple.pure_pre
  intro hafter
  subst after
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ hp => hp.2) (HeapWP.fromRaw.spec repr p replacement hsize))
  intro _
  exact HeapWP.Triple.pure emp (initial, replacement)

/-- The corrected alias example observes the write and releases its allocation. -/
theorem alias_write.spec (repr : Aeneas.Std.Repr U32) (initial replacement : U32)
    (hsize : 0 < repr.size) (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (alias_write repr initial replacement)
      (fun result s' => result = (initial, replacement) ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold alias_write
  apply HeapWP.Spec.bind (HeapWP.intoRaw.spec repr initial s F hi hm hc hfit)
  rintro p s' ⟨_, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono (alias_write_tail.spec repr p initial replacement hsize h F s' hp hd hm' hi')
  rintro result s'' ⟨h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

end raw_box

namespace raw_box_manual

/- A handwritten borrowed-Box prototype, not Rust's consuming Box conversion.
The safe place is unavailable until the matching callback returns its updated
value. Removing the exposure does not deallocate the Rust Box. -/
def into_raw (repr : Aeneas.Std.Repr T) (b : T) : Result (MutRawPtr T × (Unit → Result T)) :=
  Aeneas.Std.bind (RawPtr.allocExposure repr [b]) fun p =>
    Result.ok (p, fun (_ : Unit) => core.ptr.end_from_mut repr p)

def borrowed_box (repr : Aeneas.Std.Repr U32) (initial replacement : U32) : Result (U32 × U32) :=
  Aeneas.Std.bind (into_raw repr initial) fun (p, end_borrow) => do
    let before ← RawPtr.read repr p
    MutRawPtr.write repr p replacement
    let b ← end_borrow ()
    pure (before, alloc.boxed.Box.deref b)

/-- The callback recovers any subsequently written value, not just the initial one. -/
theorem into_raw.spec (repr : Aeneas.Std.Repr T) (value : T)
    (hsize : 0 < repr.size) (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (into_raw repr value)
      (fun (p, back) s' =>
        (∀ updated, HeapWP.Triple (sep (alloc repr p 1 false) (pointsTo repr p updated))
          (back ()) (fun result h => result = updated ∧ emp h)) ∧
        s'.next.val = s.next.val + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p 1 false) (pointsTo repr p value) h) s := by
  unfold into_raw
  apply HeapWP.Spec.bind (HeapWP.allocExposure.spec repr value s F hi hm hc hfit)
  intro p s' hp
  apply HeapWP.Spec.pure _ _ _ |>.mpr
  exact ⟨fun updated => HeapWP.end_from_mut.spec repr p updated hsize, hp⟩

theorem borrowed_box_tail.spec (repr : Aeneas.Std.Repr U32) (p : MutRawPtr U32)
    (back : Unit → Result U32) (initial replacement : U32) (hsize : 0 < repr.size)
    (hback : ∀ updated, HeapWP.Triple (sep (alloc repr p 1 false) (pointsTo repr p updated))
      (back ()) (fun result h => result = updated ∧ emp h)) :
    HeapWP.Triple (sep (alloc repr p 1 false) (pointsTo repr p initial))
      (do let before ← RawPtr.read repr p
          MutRawPtr.write repr p replacement
          let b ← back ()
          pure (before, alloc.boxed.Box.deref b))
      (fun result h => result = (initial, replacement) ∧ emp h) := by
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun value h hp => (sep_and_left (value = initial)
      (pointsTo repr p initial) (alloc repr p 1 false) h).mp hp)
    (HeapWP.frame (R := alloc repr p 1 false) (HeapWP.read.spec repr p initial 0 hsize)))
  intro before
  apply HeapWP.Triple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.Triple.bind (HeapWP.frame (R := alloc repr p 1 false)
    (HeapWP.write.spec repr p initial replacement hsize))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (hback replacement))
  intro b
  apply HeapWP.Triple.pure_pre
  intro hb
  subst b
  exact HeapWP.Triple.pure emp (initial, replacement)

/-- Raw writes reach the safe Box through the matching callback, leaving no exposure. -/
theorem borrowed_box.spec (repr : Aeneas.Std.Repr U32) (initial replacement : U32)
    (hsize : 0 < repr.size) (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (borrowed_box repr initial replacement)
      (fun result s' => result = (initial, replacement) ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold borrowed_box
  apply HeapWP.Spec.bind (into_raw.spec repr initial hsize hfit s F hi hm hc)
  rintro ⟨p, back⟩ s' ⟨hback, _, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono
    (borrowed_box_tail.spec repr p back initial replacement hsize hback h F s' hp hd hm' hi')
  rintro result s'' ⟨h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

end raw_box_manual

/-- info: 'raw_read_write_read.read_write_read.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_read_write_read.read_write_read.spec

/-- info: 'raw_read_write_read.discarded_read.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_read_write_read.discarded_read.spec

/-- info: 'raw_box.alias_write.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box.alias_write.spec

/-- info: 'raw_box_manual.into_raw.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box_manual.into_raw.spec

/-- info: 'raw_box_manual.borrowed_box.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box_manual.borrowed_box.spec
