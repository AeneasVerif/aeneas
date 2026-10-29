module

public import RawBox
public import RawReadWriteRead
public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Alloc.Boxed
import all Aeneas.Std.Primitives
import all Aeneas.Std.Heap.Effects

public section

open Aeneas.Std
open Aeneas.Std.SepLogic

namespace raw_read_write_read

/-- The manually corrected translation observes both the old and new values. -/
theorem read_write_read.spec (p : MutRawPtr U32) (initial : U32) :
    HeapWP.Triple (pointsTo p initial) (read_write_read p)
      (fun result h => result = (initial, 1#u32) ∧ pointsTo p 1#u32 h) := by
  unfold read_write_read
  apply HeapWP.Triple.bind (HeapWP.read.spec p initial 0)
  intro before
  apply HeapWP.Triple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.Triple.bind
    (HeapWP.write.spec p (.shared 0 initial) 1#u32 True.intro)
  intro _
  apply HeapWP.Triple.bind (HeapWP.read.spec p 1#u32 0)
  intro after
  apply HeapWP.Triple.pure_pre
  intro hafter
  subst after
  exact HeapWP.Triple.pure (pointsTo p 1#u32) (initial, 1#u32)

/-- Discarding the first read does not permit reusing it after a write. -/
theorem discarded_read.spec (p : MutRawPtr U32) (initial : U32) :
    HeapWP.Triple (pointsTo p initial) (discarded_read p)
      (fun result h => result = 1#u32 ∧ pointsTo p 1#u32 h) := by
  unfold discarded_read
  apply HeapWP.Triple.bind (HeapWP.read.spec p initial 0)
  intro _
  apply HeapWP.Triple.pure_pre
  intro _
  apply HeapWP.Triple.bind
    (HeapWP.write.spec p (.shared 0 initial) 1#u32 True.intro)
  intro _
  exact HeapWP.read.spec p 1#u32 0

end raw_read_write_read

namespace raw_box

/-- The corrected alias example observes the write and releases its allocation. -/
theorem alias_write.spec (initial replacement : U32) :
    HeapWP.Triple emp (alias_write initial replacement)
      (fun result h => result = (initial, replacement) ∧ emp h) := by
  unfold alias_write
  apply HeapWP.Triple.bind (HeapWP.intoRaw.spec initial)
  intro p
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun value h hp => (sep_and_left (value = initial)
      (pointsTo p initial) (alloc p 1 true) h).mp hp)
    (HeapWP.frame (R := alloc p 1 true) (HeapWP.read.spec p initial 0)))
  intro before
  apply HeapWP.Triple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.Triple.bind (HeapWP.frame (R := alloc p 1 true)
    (HeapWP.write.spec p (.shared 0 initial) replacement True.intro))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun _ h => h)
    (fun value h hp => (sep_and_left (value = replacement)
      (pointsTo p replacement) (alloc p 1 true) h).mp hp)
    (HeapWP.frame (R := alloc p 1 true) (HeapWP.read.spec p replacement 0)))
  intro after
  apply HeapWP.Triple.pure_pre
  intro hafter
  subst after
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ hp => hp.2) (HeapWP.fromRaw.spec p replacement))
  intro _
  exact HeapWP.Triple.pure emp (initial, replacement)

end raw_box

namespace raw_box_manual

unseal Result

/- Returning an effectful callback raises the result universe. Keep the
   cross-universe composition rule local to this prototype. -/
theorem bind {α : Type u} {β : Type v}
    {P : Assertion.{0}} {Q : α → Assertion.{0}} {R : β → Assertion.{0}}
    {c : Result α} {k : α → Result β}
    (hc : HeapWP.Triple P c Q)
    (hk : ∀ x, HeapWP.Triple (Q x) (k x) R) :
    HeapWP.Triple P (Aeneas.Std.bind c k) R := by
  intro h F s hp hd hm hi
  apply Aeneas.Data.Coinductive.DWP.bind (hc h F s hp hd hm hi)
  rintro x s' ⟨h', hd', hm', hi', hq⟩
  exact hk x h' F s' hq hd' hm' hi'

/- A candidate *borrowed* conversion, not Rust's consuming `Box::into_raw`.
   The Rust counterpart of `borrowed_box` is:

   pub fn borrowed_box(initial: u32, replacement: u32) -> (u32, u32) {
       let mut b = Box::new(initial);
       let p = std::ptr::from_mut(&mut *b);
       let before = unsafe { p.read() };
       unsafe { p.write(replacement) };
       (before, *b)
   }

   The model's Box is a plain value. The safe place is unavailable until its
   backward callback returns the updated value. Ending the exposure does not free
   the Rust Box; it removes only its temporary raw-memory representation.
   This is handwritten design validation, not current compiler output. -/
def into_raw (b : T) : Result (MutRawPtr T × (Unit → Result T)) :=
  Aeneas.Std.bind (RawPtr.allocExposure [b]) fun p =>
    Result.ok (p, fun (_ : Unit) => core.ptr.end_from_mut p)

def borrowed_box (initial replacement : U32) : Result (U32 × U32) :=
  Aeneas.Std.bind (into_raw initial) fun (p, end_borrow) => do
    let before ← RawPtr.read p
    MutRawPtr.write p replacement
    let b ← end_borrow ()
    pure (before, alloc.boxed.Box.deref b)

theorem allocExposure.spec (value : T) :
    HeapWP.Triple emp (RawPtr.allocExposure [value])
      (fun p => sep (alloc p 1 false) (pointsTo p value)) := by
  simpa [RawPtr.allocExposure, State.newExposure, State.newBlock, Cell.full] using
    HeapWP.Triple.guardedModify (SepLogic.newBlock.spec [value] false)

theorem end_from_mut.spec (p : MutRawPtr T) (value : T) :
    HeapWP.Triple (sep (alloc p 1 false) (pointsTo p value))
      (core.ptr.end_from_mut p) (fun result h => result = value ∧ emp h) := by
  unfold core.ptr.end_from_mut
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun x h hp => (sep_and_left (x = value)
      (pointsTo p value) (alloc p 1 false) h).mp hp)
    (HeapWP.frame (R := alloc p 1 false) (HeapWP.read.spec p value 0)))
  intro x
  apply HeapWP.Triple.pure_pre
  intro hx
  subst x
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (HeapWP.Triple.guardedModify
      (SepLogic.freeBlock.spec p [.shared 0 value] false (by simp [Cell.writable]))))
  intro _
  exact HeapWP.Triple.pure emp value

/-- The callback recovers any subsequently written value, not just the initial one. -/
theorem into_raw.spec (value : T) :
    HeapWP.Triple emp (into_raw value)
      (fun (p, back) h =>
        (∀ updated, HeapWP.Triple (sep (alloc p 1 false) (pointsTo p updated))
          (back ()) (fun result h => result = updated ∧ emp h)) ∧
        sep (alloc p 1 false) (pointsTo p value) h) := by
  unfold into_raw
  apply bind (allocExposure.spec value)
  intro p
  apply HeapWP.Triple.conseq (fun _ h => h) _ (HeapWP.Triple.pure
    (sep (alloc p 1 false) (pointsTo p value))
    (p, fun (_ : Unit) => core.ptr.end_from_mut p))
  rintro _ _ ⟨rfl, hp⟩
  exact ⟨fun updated => end_from_mut.spec p updated, hp⟩

/-- Raw writes reach the safe Box through the end-borrow callback, leaving no raw exposure. -/
theorem borrowed_box.spec (initial replacement : U32) :
    HeapWP.Triple emp (borrowed_box initial replacement)
      (fun result h => result = (initial, replacement) ∧ emp h) := by
  unfold borrowed_box
  apply bind (into_raw.spec initial)
  rintro ⟨p, end_borrow⟩
  apply HeapWP.Triple.pure_pre
  intro hback
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun value h hp => (sep_and_left (value = initial)
      (pointsTo p initial) (alloc p 1 false) h).mp hp)
    (HeapWP.frame (R := alloc p 1 false) (HeapWP.read.spec p initial 0)))
  intro before
  apply HeapWP.Triple.pure_pre
  intro hbefore
  subst before
  apply HeapWP.Triple.bind (HeapWP.frame (R := alloc p 1 false)
    (HeapWP.write.spec p (.shared 0 initial) replacement True.intro))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (hback replacement))
  intro b
  apply HeapWP.Triple.pure_pre
  intro hb
  subst b
  exact HeapWP.Triple.pure emp (initial, replacement)

end raw_box_manual

/--
info: 'raw_read_write_read.read_write_read.spec' depends on axioms: [propext, Classical.choice, Quot.sound, layout]
-/
#guard_msgs in
#print axioms raw_read_write_read.read_write_read.spec

/--
info: 'raw_read_write_read.discarded_read.spec' depends on axioms: [propext, Classical.choice, Quot.sound, layout]
-/
#guard_msgs in
#print axioms raw_read_write_read.discarded_read.spec

/--
info: 'raw_box.alias_write.spec' depends on axioms: [propext, Classical.choice, Quot.sound, layout]
-/
#guard_msgs in
#print axioms raw_box.alias_write.spec

/--
info: 'raw_box_manual.into_raw.spec' depends on axioms: [propext, Classical.choice, Quot.sound, layout]
-/
#guard_msgs in
#print axioms raw_box_manual.into_raw.spec

/--
info: 'raw_box_manual.borrowed_box.spec' depends on axioms: [propext, Classical.choice, Quot.sound, layout]
-/
#guard_msgs in
#print axioms raw_box_manual.borrowed_box.spec
