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

/- Manually adapted translations of `raw_box.rs`'s borrowed-Box examples.
`to_raw` is the borrowed conversion, not Rust's consuming `Box::into_raw`.
The safe place is unavailable until the matching callback returns its updated
value. Removing the exposure does not deallocate the Rust Box. -/
def to_raw (repr : Aeneas.Std.Repr T) (b : T) : Result (MutRawPtr T × (Unit → Result T)) :=
  Aeneas.Std.bind (RawPtr.allocExposure repr [b]) fun p =>
    Result.ok (p, fun (_ : Unit) => core.ptr.end_from_mut repr p)

def borrowed_box (repr : Aeneas.Std.Repr U32) (initial replacement : U32) : Result (U32 × U32) :=
  Aeneas.Std.bind (to_raw repr initial) fun (p, end_borrow) => do
    let before ← RawPtr.read repr p
    MutRawPtr.write repr p replacement
    let b ← end_borrow ()
    pure (before, alloc.boxed.Box.deref b)

def borrowed_pair (repr : Aeneas.Std.Repr (U32 × U32))
    (first second replacement : U32) : Result (U32 × U32) :=
  Aeneas.Std.bind (to_raw repr (first, second)) fun (p, end_borrow) => do
    let (old_first, _) ← RawPtr.read repr p
    MutRawPtr.write repr p (old_first, replacement)
    let b ← end_borrow ()
    pure (alloc.boxed.Box.deref b)

/-- The callback recovers any subsequently written value, not just the initial one. -/
theorem to_raw.spec (repr : Aeneas.Std.Repr T) (value : T)
    (hsize : 0 < repr.size) (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (to_raw repr value)
      (fun (p, back) s' =>
        (∀ updated, HeapWP.Triple (sep (alloc repr p 1 false) (pointsTo repr p updated))
          (back ()) (fun result h => result = updated ∧ emp h)) ∧
        s'.next.val = s.next.val + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p 1 false) (pointsTo repr p value) h) s := by
  unfold to_raw
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
  apply HeapWP.Spec.bind (to_raw.spec repr initial hsize hfit s F hi hm hc)
  rintro ⟨p, back⟩ s' ⟨hback, _, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono
    (borrowed_box_tail.spec repr p back initial replacement hsize hback h F s' hp hd hm' hi')
  rintro result s'' ⟨h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

theorem borrowed_pair_tail.spec (repr : Aeneas.Std.Repr (U32 × U32))
    (p : MutRawPtr (U32 × U32)) (back : Unit → Result (U32 × U32))
    (first second replacement : U32) (hsize : 0 < repr.size)
    (hback : ∀ updated, HeapWP.Triple (sep (alloc repr p 1 false) (pointsTo repr p updated))
      (back ()) (fun result h => result = updated ∧ emp h)) :
    HeapWP.Triple (sep (alloc repr p 1 false) (pointsTo repr p (first, second)))
      (do let (old_first, _) ← RawPtr.read repr p
          MutRawPtr.write repr p (old_first, replacement)
          let b ← back ()
          pure (alloc.boxed.Box.deref b))
      (fun result h => result = (first, replacement) ∧ emp h) := by
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp)
    (fun value h hp => (sep_and_left (value = (first, second))
      (pointsTo repr p (first, second)) (alloc repr p 1 false) h).mp hp)
    (HeapWP.frame (R := alloc repr p 1 false)
      (HeapWP.read.spec repr p (first, second) 0 hsize)))
  intro value
  apply HeapWP.Triple.pure_pre
  intro hv
  subst value
  apply HeapWP.Triple.bind (HeapWP.frame (R := alloc repr p 1 false)
    (HeapWP.write.spec repr p (first, second) (first, replacement) hsize))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (hback (first, replacement)))
  intro b
  apply HeapWP.Triple.pure_pre
  intro hb
  subst b
  exact HeapWP.Triple.pure emp (first, replacement)

/-- Safe access after the backward call observes the aggregate written through the alias. -/
theorem borrowed_pair.spec (repr : Aeneas.Std.Repr (U32 × U32))
    (first second replacement : U32) (hsize : 0 < repr.size)
    (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (borrowed_pair repr first second replacement)
      (fun result s' => result = (first, replacement) ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold borrowed_pair
  apply HeapWP.Spec.bind (to_raw.spec repr (first, second) hsize hfit s F hi hm hc)
  rintro ⟨p, back⟩ s' ⟨hback, _, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono
    (borrowed_pair_tail.spec repr p back first second replacement hsize hback h F s' hp hd hm' hi')
  rintro result s'' ⟨h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

end raw_box_manual

/- These are compositions of the model's raw API, not additional adaptations of
Rust translation. Restoration calls stand for matching backward computations. -/
namespace raw_api

def shared_reads (repr : Aeneas.Std.Repr T) (p : RawPtr T) : Result (List T) := do
  let outer ← RawPtr.shareRange repr p 1
  let inner ← RawPtr.shareRange repr p 1
  let observed ← RawPtr.readRange repr (RawPtr.cast_const p) 1
  RawPtr.endShareRange repr p inner
  RawPtr.endShareRange repr p outer
  pure observed

/-- Nested shared borrows permit const reads and restore the original writable resource. -/
theorem shared_reads.spec (repr : Aeneas.Std.Repr T) (p : RawPtr T) (value : T)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr p value) (shared_reads repr p)
      (fun result h => result = [value] ∧ pointsTo repr p value 0 h) := by
  unfold shared_reads
  apply HeapWP.Triple.bind (HeapWP.shareRange_single.spec repr p value 0 hsize)
  intro outer
  apply HeapWP.Triple.pure_pre
  intro houter
  subst outer
  apply HeapWP.Triple.bind (HeapWP.shareRange_single.spec repr p value 1 hsize)
  intro inner
  apply HeapWP.Triple.pure_pre
  intro hinner
  subst inner
  apply HeapWP.Triple.bind (HeapWP.readRange_single.spec repr p value 2 hsize)
  intro observed
  apply HeapWP.Triple.pure_pre
  intro hobserved
  subst observed
  apply HeapWP.Triple.bind (HeapWP.endShareRange_single.spec repr p value 1 hsize)
  intro _
  apply HeapWP.Triple.bind (HeapWP.endShareRange_single.spec repr p value 0 hsize)
  intro _
  exact HeapWP.Triple.pure (pointsTo repr p value) [value]

def borrowed_update (repr : Aeneas.Std.Repr T) (p : RawPtr T) (replacement : T) :
    Result (T × T) := do
  let before ← RawPtr.borrow repr p
  RawPtr.endBorrow repr p replacement
  let after ← RawPtr.read repr p
  pure (before, after)

/-- Exclusive restoration chooses bytes for the updated value, which subsequent raw reads observe. -/
theorem borrowed_update.spec (repr : Aeneas.Std.Repr T) (p : RawPtr T)
    (initial replacement : T) (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr p initial) (borrowed_update repr p replacement)
      (fun result h => result = (initial, replacement) ∧ pointsTo repr p replacement 0 h) := by
  unfold borrowed_update
  apply HeapWP.Triple.bind (HeapWP.borrow.spec repr p initial hsize)
  intro before
  apply HeapWP.Triple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.Triple.bind (HeapWP.endBorrow.spec repr p replacement hsize)
  intro _
  apply HeapWP.Triple.bind (HeapWP.read.spec repr p replacement 0 hsize)
  intro after
  apply HeapWP.Triple.pure_pre
  intro hafter
  subst after
  exact HeapWP.Triple.pure (pointsTo repr p replacement) (initial, replacement)

def permission_round_trip (repr : Aeneas.Std.Repr T) (p : RawPtr T) (replacement : T) :
    Result (List T × T × T) := do
  let shared ← shared_reads repr p
  let (before, after) ← borrowed_update repr p replacement
  pure (shared, before, after)

/-- Shared restoration composes with exclusive borrowing and an update at the same pointer. -/
theorem permission_round_trip.spec (repr : Aeneas.Std.Repr T) (p : RawPtr T)
    (initial replacement : T) (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr p initial) (permission_round_trip repr p replacement)
      (fun result h => result = ([initial], initial, replacement) ∧
        pointsTo repr p replacement 0 h) := by
  unfold permission_round_trip
  apply HeapWP.Triple.bind (shared_reads.spec repr p initial hsize)
  intro shared
  apply HeapWP.Triple.pure_pre
  intro hshared
  subst shared
  apply HeapWP.Triple.bind (borrowed_update.spec repr p initial replacement hsize)
  intro values
  apply HeapWP.Triple.pure_pre
  intro hvalues
  subst values
  exact HeapWP.Triple.pure (pointsTo repr p replacement) ([initial], initial, replacement)

end raw_api

/-- info: 'raw_read_write_read.read_write_read.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_read_write_read.read_write_read.spec

/-- info: 'raw_read_write_read.discarded_read.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_read_write_read.discarded_read.spec

/-- info: 'raw_box.alias_write.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box.alias_write.spec

/-- info: 'raw_box_manual.to_raw.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box_manual.to_raw.spec

/-- info: 'raw_box_manual.borrowed_box.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box_manual.borrowed_box.spec

/-- info: 'raw_box_manual.borrowed_pair.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box_manual.borrowed_pair.spec

/-- info: 'raw_api.permission_round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_api.permission_round_trip.spec
