module

public import RawBox
public import RawBoxProofs
public import RawReadWriteRead
public import Aeneas.Std.Heap.EffectSpecs
public import Aeneas.Std.Heap.RangeRestoration
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Primitives

public section

open Aeneas.Std
open Aeneas.Std.SepLogic

namespace raw_box

theorem alias_write_tail.spec (repr : Aeneas.Std.Repr U32) (p : MutRawPtr U32)
    (bptr : BasePtr) (initial replacement : U32)
    (noPointers : ∀ q, ¬ repr.Carries replacement q) (hsize : 0 < repr.size) :
    HeapWP.RootTriple [p.provenance]
      (sep (alloc repr p bptr 1 true) (pointsTo repr p bptr initial))
      (do let before ← RawPtr.read repr p
          MutRawPtr.write repr p replacement
          let after ← RawPtr.read repr p
          let _ ← alloc.boxed.Box.from_raw repr p
          pure (before, after))
      (fun result h => result = (initial, replacement) ∧ emp h) := by
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.read_owned repr p bptr initial true hsize)
  intro before
  apply HeapWP.RootTriple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.RootTriple.bind
    (HeapWP.RootTriple.write_owned repr p bptr initial replacement true noPointers hsize)
  intro _
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.read_owned repr p bptr replacement true hsize)
  intro after
  apply HeapWP.RootTriple.pure_pre
  intro hafter
  subst after
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq (fun _ hp => hp)
    (fun _ _ hp => hp.2) (HeapWP.RootTriple.fromRaw repr p bptr replacement hsize (by simp)))
  intro _
  exact HeapWP.RootTriple.pure emp (initial, replacement)

/-- The corrected alias example observes the write and releases its allocation. -/
theorem alias_write.spec (repr : Aeneas.Std.Repr U32) (initial replacement : U32)
    (noPointers : ∀ q, ¬ repr.Carries replacement q) (hsize : 0 < repr.size)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (feasible : ∃ p s', State.newBlock repr [initial] true s p s') :
    HeapWP.Spec (alias_write repr initial replacement)
      (fun result s' => result = (initial, replacement) ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold alias_write
  apply HeapWP.Spec.bind (HeapWP.intoRaw_return.spec repr initial s F hi hm feasible)
  rintro p s' ⟨authority, _, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono (alias_write_tail.spec repr p p.address initial replacement noPointers hsize
    h F s' hp hd hm' hi' (by simpa using authority))
  rintro result s'' ⟨_, h', _, hm'', hi'', hv, rfl⟩
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
    (hsize : 0 < repr.size)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (feasible : ∃ p s', State.newBlock repr [value] false s p s') :
    HeapWP.Spec (to_raw repr value)
      (fun (p, back) s' =>
        (∀ updated, HeapWP.Triple
          (sep (alloc repr p p.address 1 false) (readable repr p p.address updated))
          (back ()) (fun result h => result = updated ∧ emp h)) ∧
        s'.next = s.next + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p p.address 1 false) (readable repr p p.address value) h) s := by
  unfold to_raw
  apply HeapWP.Spec.bind (HeapWP.allocExposure.spec repr value s F hi hm feasible)
  intro p s' hp
  apply HeapWP.Spec.pure _ _ _ |>.mpr
  exact ⟨fun updated => HeapWP.end_from_mut.spec repr p p.address updated hsize, hp⟩

theorem borrowed_box_tail.spec (repr : Aeneas.Std.Repr U32) (p : MutRawPtr U32)
    (bptr : BasePtr) (back : Unit → Result U32) (initial replacement : U32)
    (noPointers : ∀ q, ¬ repr.Carries replacement q) (hsize : 0 < repr.size)
    (hback : ∀ updated, HeapWP.Triple
      (sep (alloc repr p bptr 1 false) (readable repr p bptr updated))
      (back ()) (fun result h => result = updated ∧ emp h)) :
    HeapWP.Triple (sep (alloc repr p bptr 1 false) (readable repr p bptr initial))
      (do let before ← RawPtr.read repr p
          MutRawPtr.write repr p replacement
          let b ← back ()
          pure (before, alloc.boxed.Box.deref b))
      (fun result h => result = (initial, replacement) ∧ emp h) := by
  apply HeapWP.Triple.bind (HeapWP.read_view.spec repr p bptr initial false hsize)
  intro before
  apply HeapWP.Triple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.Triple.bind
    (HeapWP.write_view.spec repr p bptr initial replacement false noPointers hsize)
  intro _
  apply HeapWP.Triple.bind (hback replacement)
  intro b
  apply HeapWP.Triple.pure_pre
  intro hb
  subst b
  exact HeapWP.Triple.pure emp (initial, replacement)

/-- Raw writes reach the safe Box through the matching callback, leaving no exposure. -/
theorem borrowed_box.spec (repr : Aeneas.Std.Repr U32) (initial replacement : U32)
    (noPointers : ∀ q, ¬ repr.Carries replacement q) (hsize : 0 < repr.size)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (feasible : ∃ p s', State.newBlock repr [initial] false s p s') :
    HeapWP.Spec (borrowed_box repr initial replacement)
      (fun result s' => result = (initial, replacement) ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold borrowed_box
  apply HeapWP.Spec.bind (to_raw.spec repr initial hsize s F hi hm feasible)
  rintro ⟨p, back⟩ s' ⟨hback, _, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono
    (borrowed_box_tail.spec repr p p.address back initial replacement noPointers hsize
      hback h F s' hp hd hm' hi')
  rintro result s'' ⟨h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

theorem borrowed_pair_tail.spec (repr : Aeneas.Std.Repr (U32 × U32))
    (p : MutRawPtr (U32 × U32)) (bptr : BasePtr) (back : Unit → Result (U32 × U32))
    (first second replacement : U32)
    (noPointers : ∀ q, ¬ repr.Carries (first, replacement) q) (hsize : 0 < repr.size)
    (hback : ∀ updated, HeapWP.Triple
      (sep (alloc repr p bptr 1 false) (readable repr p bptr updated))
      (back ()) (fun result h => result = updated ∧ emp h)) :
    HeapWP.Triple (sep (alloc repr p bptr 1 false) (readable repr p bptr (first, second)))
      (do let (old_first, _) ← RawPtr.read repr p
          MutRawPtr.write repr p (old_first, replacement)
          let b ← back ()
          pure (alloc.boxed.Box.deref b))
      (fun result h => result = (first, replacement) ∧ emp h) := by
  apply HeapWP.Triple.bind (HeapWP.read_view.spec repr p bptr (first, second) false hsize)
  intro value
  apply HeapWP.Triple.pure_pre
  intro hv
  subst value
  apply HeapWP.Triple.bind
    (HeapWP.write_view.spec repr p bptr (first, second) (first, replacement) false noPointers hsize)
  intro _
  apply HeapWP.Triple.bind (hback (first, replacement))
  intro b
  apply HeapWP.Triple.pure_pre
  intro hb
  subst b
  exact HeapWP.Triple.pure emp (first, replacement)

/-- Safe access after the backward call observes the aggregate written through the alias. -/
theorem borrowed_pair.spec (repr : Aeneas.Std.Repr (U32 × U32))
    (first second replacement : U32) (hsize : 0 < repr.size)
    (noPointers : ∀ q, ¬ repr.Carries (first, replacement) q)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (feasible : ∃ p s', State.newBlock repr [(first, second)] false s p s') :
    HeapWP.Spec (borrowed_pair repr first second replacement)
      (fun result s' => result = (first, replacement) ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold borrowed_pair
  apply HeapWP.Spec.bind (to_raw.spec repr (first, second) hsize s F hi hm feasible)
  rintro ⟨p, back⟩ s' ⟨hback, _, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono
    (borrowed_pair_tail.spec repr p p.address back first second replacement noPointers hsize
      hback h F s' hp hd hm' hi')
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
theorem shared_reads.spec (repr : Aeneas.Std.Repr T) (p : RawPtr T) (bptr : BasePtr) (value : T)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr p bptr value) (shared_reads repr p)
      (fun result h => result = [value] ∧ pointsTo repr p bptr value 0 h) := by
  intro h F s₀ hp hd hm hi
  unfold shared_reads
  apply HeapWP.Spec.bind
    (HeapWP.shareRange_single_return.spec repr p bptr value 0 hsize h F s₀ hp hd hm hi)
  rintro outer s₁ ⟨rfl, ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩, returnOuter⟩
  apply HeapWP.Spec.bind
    (HeapWP.shareRange_single_return.spec repr p bptr value 1 hsize h₁ F s₁ hp₁ hd₁ hm₁ hi₁)
  rintro inner s₂ ⟨rfl, ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩, returnInner⟩
  have reading := HeapWP.Spec.checkedModify.mp
    (HeapWP.readRange_single.spec repr p bptr value 2 hsize h₂ F s₂ hp₂ hd₂ hm₂ hi₂)
  have readExact : HeapWP.Spec (RawPtr.readRange repr p 1)
      (fun observed s₃ => observed = [value] ∧ s₃ = s₂) s₂ := by
    apply HeapWP.Spec.checkedModify.mpr
    refine ⟨reading.1, ?_⟩
    intro observed s₃ run
    obtain ⟨_, _, _, _, hv, _⟩ := reading.2 observed s₃ run
    exact ⟨hv, run.2⟩
  apply HeapWP.Spec.bind readExact
  rintro observed s₃ ⟨rfl, rfl⟩
  apply HeapWP.Spec.bind returnInner
  rintro _ s₄ rfl
  apply HeapWP.Spec.bind returnOuter
  rintro _ s₅ rfl
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨h, hd, hm, hi, rfl, hp⟩

def borrowed_update (repr : Aeneas.Std.Repr T) (p : RawPtr T) (replacement : T) :
    Result (T × T) := do
  let before ← RawPtr.withBorrow repr p (fun _ => replacement)
  let after ← RawPtr.read repr p
  pure (before, after)

/-- Exclusive restoration chooses bytes for the updated value, which subsequent raw reads observe. -/
theorem borrowed_update.spec (repr : Aeneas.Std.Repr T) (p : RawPtr T)
    (bptr : BasePtr) (initial replacement : T)
    (noPointers : ∀ q, ¬ repr.Carries replacement q) (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr p bptr initial) (borrowed_update repr p replacement)
      (fun result h => result = (initial, replacement) ∧ pointsTo repr p bptr replacement 0 h) := by
  unfold borrowed_update
  apply HeapWP.Triple.bind (HeapWP.withBorrow.spec repr p bptr initial
    (fun _ => replacement) noPointers hsize)
  intro before
  apply HeapWP.Triple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.Triple.bind (HeapWP.read.spec repr p bptr replacement 0 hsize)
  intro after
  apply HeapWP.Triple.pure_pre
  intro hafter
  subst after
  exact HeapWP.Triple.pure (pointsTo repr p bptr replacement) (initial, replacement)

def permission_round_trip (repr : Aeneas.Std.Repr T) (p : RawPtr T) (replacement : T) :
    Result (List T × T × T) := do
  let shared ← shared_reads repr p
  let (before, after) ← borrowed_update repr p replacement
  pure (shared, before, after)

/-- Shared restoration composes with exclusive borrowing and an update at the same pointer. -/
theorem permission_round_trip.spec (repr : Aeneas.Std.Repr T) (p : RawPtr T)
    (bptr : BasePtr) (initial replacement : T)
    (noPointers : ∀ q, ¬ repr.Carries replacement q) (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr p bptr initial) (permission_round_trip repr p replacement)
      (fun result h => result = ([initial], initial, replacement) ∧
        pointsTo repr p bptr replacement 0 h) := by
  unfold permission_round_trip
  apply HeapWP.Triple.bind (shared_reads.spec repr p bptr initial hsize)
  intro shared
  apply HeapWP.Triple.pure_pre
  intro hshared
  subst shared
  apply HeapWP.Triple.bind (borrowed_update.spec repr p bptr initial replacement noPointers hsize)
  intro values
  apply HeapWP.Triple.pure_pre
  intro hvalues
  subst values
  exact HeapWP.Triple.pure (pointsTo repr p bptr replacement) ([initial], initial, replacement)

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
