module

import Aeneas.Std.HeapLemmas
import Aeneas.Std.Scalar.Notations
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

/-! Composed heap lifecycles and rejection examples, parametric in `Layout`.
The commands reproduce the relational effects of the Rust wrappers; they do not
constitute an integration with the ordinary effect-rejecting weakest precondition. -/

namespace Aeneas.Std.HeapTests

open SepLogic

universe u

variable {m : Layout.{u}}

def boxIntoFromRaw (m : Layout.{0}) (value : Nat) : Cmd m Nat :=
  Cmd.bind (Heap.newBlock m [value] true) fun p =>
  Cmd.bind (Heap.read m p) fun x =>
  Cmd.bind (Heap.freeBlock m p 1 true) fun _ =>
  Cmd.pure m x

theorem boxIntoFromRaw.spec (m : Layout.{0}) (value : Nat) :
    Triple m emp (boxIntoFromRaw m value) (fun x h => x = value ∧ emp h) := by
  apply Triple.bind (newBlock.spec [value] true)
  intro p
  apply Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp) (fun _ _ h => h)
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun x h hp => (sep_and_left (x = value)
      (block p [.shared 0 value]) (alloc p 1 true) h).mp hp)
    (frame (R := alloc p 1 true) (read.spec p value 0)))
  intro x
  apply Triple.pure_pre
  intro hx
  subst x
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (freeBlock.spec p [.shared 0 value] true (by simp [Cell.writable])))
  intro _
  exact Triple.pure m emp value

def borrowLifecycle (m : Layout.{0}) (a b : Nat) : Cmd m (List Nat × Nat) :=
  Cmd.bind (Heap.alloc m (ty := Nat) 1) fun p =>
  Cmd.bind (Heap.write m p a) fun _ =>
  Cmd.bind (Heap.borrowRange m p 1) fun original =>
  Cmd.bind (Heap.endBorrowRange m p [b]) fun _ =>
  Cmd.bind (Heap.read m p) fun value =>
  Cmd.bind (Heap.freeBlock m p 1 true) fun _ =>
  Cmd.pure m (original, value)

theorem borrowLifecycle.spec (m : Layout.{0}) (a b : Nat) (hsize : 0 < m.byteLength Nat) :
    Triple m emp (borrowLifecycle m a b) (fun result h => result = ([a], b) ∧ emp h) := by
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun _ h hp => (sep_comm _ _ h).mp hp) (alloc.spec Nat 1))
  intro p
  apply Triple.bind (frame (R := alloc p 1 true)
    (write.spec p .uninitialized a True.intro))
  intro _
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun result h hp => (sep_and_left (result = [a])
      (block p [.borrowed]) (alloc p 1 true) h).mp hp)
    (frame (R := alloc p 1 true) (borrowRange.spec p [a] (Or.inr hsize))))
  intro original
  apply Triple.pure_pre
  intro horiginal
  subst original
  apply Triple.bind (frame (R := alloc p 1 true) (endBorrowRange.spec p [b]))
  intro _
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun value h hp => (sep_and_left (value = b)
      (block p [.shared 0 b]) (alloc p 1 true) h).mp hp)
    (frame (R := alloc p 1 true) (read.spec p b 0)))
  intro value
  apply Triple.pure_pre
  intro hvalue
  subst value
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (freeBlock.spec p [.shared 0 b] true (by simp [Cell.writable])))
  intro _
  exact Triple.pure m emp ([a], b)

/-- Borrow one cell, update its neighbor in the same representation, then restore it. -/
def neighboringBorrow (m : Layout.{0}) (p : RawPtr Nat) (a' b' : Nat) : Cmd m (List Nat) :=
  Cmd.bind (Heap.borrowRange m p 1) fun original =>
  Cmd.bind (Heap.write m (⟨p.base, p.index + 1⟩) b') fun _ =>
  Cmd.bind (Heap.endBorrowRange m p [a']) fun _ =>
  Cmd.pure m original

theorem neighboringBorrow.spec (m : Layout.{0}) (p : RawPtr Nat) (a b a' b' : Nat)
    (hsize : 0 < m.byteLength Nat) :
    Triple m (block p (Cell.full [a, b])) (neighboringBorrow m p a' b')
      (fun result h => result = [a] ∧ block p (Cell.full [a', b']) h) := by
  apply Triple.conseq
    (fun h hp => (block_append p (Cell.full [a]) (Cell.full [b]) h).mp hp)
    (fun _ _ h => h)
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun result h hp => (sep_and_left (result = [a])
      (block p [.borrowed]) (block (⟨p.base, p.index + 1⟩) (Cell.full [b])) h).mp hp)
    (frame (R := block (⟨p.base, p.index + 1⟩) (Cell.full [b]))
      (borrowRange.spec p [a] (Or.inr hsize))))
  intro original
  apply Triple.pure_pre
  intro horiginal
  subst original
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => (sep_comm _ _ h).mp hp)
    (frame (R := block p [.borrowed])
      (write.spec (⟨p.base, p.index + 1⟩) (.shared 0 b) b' True.intro)))
  intro _
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun _ h hp => (block_append p (Cell.full [a']) (Cell.full [b']) h).mpr hp)
    (frame (R := block (⟨p.base, p.index + 1⟩) (Cell.full [b']))
      (endBorrowRange.spec p [a'])))
  intro _
  exact Triple.pure m (block p (Cell.full [a', b'])) [a]

def nestedSharing (m : Layout.{0}) (p : RawPtr Nat) : Cmd m Nat :=
  Cmd.bind (Heap.shareRange m p 1) fun _ =>
  Cmd.bind (Heap.shareRange m p 1) fun _ =>
  Cmd.bind (Heap.read m p) fun value =>
  Cmd.bind (Heap.endShareRange m p [value]) fun _ =>
  Cmd.bind (Heap.endShareRange m p [value]) fun _ =>
  Cmd.pure m value

theorem nestedSharing.spec (m : Layout.{0}) (p : RawPtr Nat) (a : Nat) :
    Triple m (pointsTo p a) (nestedSharing m p)
      (fun result h => result = a ∧ pointsTo p a h) := by
  apply Triple.bind (Triple.conseq (fun _ h => h) (fun _ _ h => h.2)
    (shareRange.spec p [a] 0))
  intro _
  apply Triple.bind (Triple.conseq (fun _ h => h) (fun _ _ h => h.2)
    (shareRange.spec p [a] 1))
  intro _
  apply Triple.bind (read.spec p a 2)
  intro value
  apply Triple.pure_pre
  intro hvalue
  subst value
  apply Triple.bind (endShareRange.spec p [a] 1)
  intro _
  apply Triple.bind (endShareRange.spec p [a] 0)
  intro _
  exact Triple.pure m (pointsTo p a) a

def sharedExposureLifecycle (m : Layout.{0}) (a : Nat) : Cmd m Nat :=
  Cmd.bind (Heap.newSharedExposure m [a]) fun p =>
  Cmd.bind (Heap.read m p) fun value =>
  Cmd.bind (Heap.endSharedExposure m p [a]) fun _ =>
  Cmd.pure m value

theorem sharedExposureLifecycle.spec (m : Layout.{0}) (a : Nat) :
    Triple m emp (sharedExposureLifecycle m a) (fun value h => value = a ∧ emp h) := by
  apply Triple.bind (newSharedExposure.spec [a])
  intro p
  apply Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp) (fun _ _ h => h)
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun value h hp => (sep_and_left (value = a)
      (block p [.shared 1 a]) (alloc p 1 false) h).mp hp)
    (frame (R := alloc p 1 false) (read.spec p a 1)))
  intro value
  apply Triple.pure_pre
  intro hvalue
  subst value
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (endSharedExposure.spec p [a]))
  intro _
  exact Triple.pure m emp a

def emptyAllocation (m : Layout.{0}) : Cmd m Unit :=
  Cmd.bind (Heap.alloc m (ty := Nat) 0) fun p =>
  Cmd.bind (Heap.offset m p 0) fun q =>
  Heap.freeBlock m q 0 true

theorem emptyAllocation.spec (m : Layout.{0}) :
    Triple m emp (emptyAllocation m) (fun _ => emp) := by
  apply Triple.bind (alloc.spec Nat 0)
  intro p
  apply Triple.bind (offsetWholeBlock.spec p [] true 0 0 (by simp) (by simp))
  intro q
  apply Triple.pure_pre
  intro hq
  subst q
  simpa using freeBlock.spec (m := m) p [] true (by simp)

/-- Move to one-past-the-end, then return using a negative displacement. -/
def signedRoundTrip (m : Layout.{0}) (p : RawPtr Nat) : Cmd m (RawPtr Nat) :=
  Cmd.bind (Heap.offset m p 2) fun finish => Heap.offset m finish (-2)

theorem signedRoundTrip.spec (m : Layout.{0}) (p : RawPtr Nat) (a b : Nat) :
    Triple m (sep (alloc p 2 true) (block p (Cell.full [a, b])))
      (signedRoundTrip m p)
      (fun result h => result = p ∧
        sep (alloc p 2 true) (block p (Cell.full [a, b])) h) := by
  apply Triple.bind (offsetWholeBlock.spec p (Cell.full [a, b]) true 0 2
    (by simp [Cell.full]) (by simp [Cell.full]))
  intro finish
  apply Triple.pure_pre
  intro hfinish
  subst finish
  exact offsetWholeBlock.spec p (Cell.full [a, b]) true 2 0
    (by simp [Cell.full]) (by simp [Cell.full])

def signedPointerRoundTrip (p : RawPtr Nat) : Result (RawPtr Nat) := do
  let finish ← RawPtr.add p 2#usize
  RawPtr.offset finish (-2)#isize

theorem signedPointerRoundTrip.spec (p : RawPtr Nat) (a b : Nat) :
    HeapWP.Triple (sep (alloc p 2 true) (block p (Cell.full [a, b])))
      (signedPointerRoundTrip p)
      (fun result h => result = p ∧
        sep (alloc p 2 true) (block p (Cell.full [a, b])) h) := by
  apply HeapWP.Triple.bind (HeapWP.add.spec p (Cell.full [a, b]) true 0 2 2#usize
    (by simp [Cell.full]) (by simp [Cell.full]) rfl)
  intro finish
  apply HeapWP.Triple.pure_pre
  intro hfinish
  subst finish
  have hcount : ((-2)#isize).val = (0 : Int) - 2 := by scalar_tac
  exact HeapWP.offset.spec p (Cell.full [a, b]) true 2 0 (-2)#isize
    (by simp [Cell.full]) (by simp [Cell.full]) hcount

/-- Uninitialized storage is writable, but not readable. -/
example (s s' : Heap m.Repr) (p : RawPtr ty) (value : ty)
    (hm : Fragment.Matches m s (cellsHeap p [.uninitialized])) :
    ¬ Heap.read m p s value s' :=
  read.denied hm rfl value

/-- An exclusive borrow blocks reads, raw writes, and whole-base cleanup. -/
example (s s' : Heap m.Repr) (p : RawPtr ty) (value : ty)
    (hm : Fragment.Matches m s (cellsHeap p [.borrowed])) (count : Nat) :
    ¬ Heap.read m p s value s' ∧ ¬ Heap.write m p value s () s' ∧
      ¬ Heap.freeBlock m (⟨p.base, 0⟩ : RawPtr ty) count true s () s' :=
  ⟨read.denied hm rfl value, write.denied hm (by simp [Cell.writable]) value,
    freeBlock.denied (q := ⟨p.base, 0⟩) hm (by simp [Cell.writable]) rfl count true⟩

/-- Shared permissions retain reads but exclude writes and cleanup. -/
example (s s' : Heap m.Repr) (p : RawPtr ty) (old value : ty) (depth count : Nat)
    (hm : Fragment.Matches m s (cellsHeap p [.shared (depth + 1) old])) :
    ¬ Heap.write m p value s () s' ∧
      ¬ Heap.freeBlock m (⟨p.base, 0⟩ : RawPtr ty) count false s () s' :=
  ⟨write.denied hm (by simp [Cell.writable]) value,
    freeBlock.denied (q := ⟨p.base, 0⟩) hm (by simp [Cell.writable]) rfl count false⟩

example (s s' : Heap m.Repr) (p : RawPtr ty) (count : Nat) (own : Bool)
    (hoff : p.index ≠ 0) : ¬ Heap.freeBlock m p count own s () s' :=
  fun h => hoff h.1

example (s s' : Heap m.Repr) (p : RawPtr ty) (count : Nat)
    (hview : s.allocated p.base = false) : ¬ Heap.freeBlock m p count true s () s' := by
  intro h
  simp [Heap.freeBlock, hview] at h

example (s s' : Heap m.Repr) (p : RawPtr ty) (count : Nat)
    (howned : s.allocated p.base = true) : ¬ Heap.freeBlock m p count false s () s' := by
  intro h
  simp [Heap.freeBlock, howned] at h

example (s s' : Heap m.Repr) (p : RawPtr ty) (r : m.Repr) (count : Nat)
    (hs : s.cells p.base = some r) (hne : count ≠ m.extent ty r) (own : Bool) :
    ¬ Heap.freeBlock m p count own s () s' := by
  rintro ⟨_, _, ⟨actual, ⟨r', ha, hext, _⟩, hn, _⟩, _⟩
  have he : r' = r := Option.some.inj (ha.symm.trans hs)
  exact hne (by grind)

/-- Removing the base prevents a second cleanup, even for an empty allocation. -/
example (s s' s'' : Heap m.Repr) (p : RawPtr ty) (count : Nat) (own : Bool)
    (h : Heap.freeBlock m p count own s () s') :
    ¬ Heap.freeBlock m p count own s' () s'' := by
  obtain ⟨_, _, _, rfl⟩ := h
  rintro ⟨_, _, ⟨cs, ⟨r, hs, _⟩, _⟩, _⟩
  simp at hs

example (s s' : Heap m.Repr) (p : RawPtr ty) (value : ty) :
    ¬ Heap.read m p (s.remove p.base) value s' := by
  rintro ⟨⟨r, depth, hs, _⟩, _⟩
  simp at hs

example (s s' : Heap m.Repr) (p : RawPtr ty) (value : ty) :
    ¬ Heap.write m p value (s.remove p.base) () s' := by
  rintro ⟨r, r', hs, _⟩
  simp at hs

example (s s' : Heap m.Repr) (p : RawPtr ty) (values : List ty) (hne : values ≠ []) :
    ¬ Heap.endBorrowRange m p values (s.remove p.base) () s' := by
  intro hu
  have ho : List.replicate values.length (.borrowed : Cell ty) ≠ [] := by
    simpa using hne
  obtain ⟨_, r, r', hs, _⟩ := (ite_eq_right ho).mp hu
  simp at hs

/-- Fresh exposures cannot reuse a freed allocation's base. -/
example (s s' s'' : Heap m.Repr) (hi : s.Inv) (p q : RawPtr ty) (count : Nat)
    (hfree : Heap.freeBlock m p count true s () s')
    (values : List ty) (hnew : Heap.newBlock m values false s' q s'') :
    q.base ≠ p.base := by
  obtain ⟨_, _, ⟨cs, ⟨r, hs, _⟩, _⟩, rfl⟩ := hfree
  obtain ⟨_, rfl, _⟩ := hnew
  exact (Nat.ne_of_lt (hi.base_lt hs)).symm

example (s s' : Heap m.Repr) (p : RawPtr ty) (value : ty)
    (hm : Fragment.Matches m s (cellsHeap p [.shared 2 value])) :
    ¬ Heap.endSharedExposure m p [value] s () s' := by
  rintro ⟨hoff, _, ⟨r, hs, _, hv, _⟩, _⟩
  have hv' : m.Views ty r p.index [.shared 1 value] := by simpa [hoff] using hv
  have he := views_unique hm (by simp) hs hv'
  simp at he

example (s s' : Heap m.Repr) (p : RawPtr ty) (n count : Nat)
    (hs : s.extent m ty p.base = some n) (hbound : n < p.index + count)
    (q : RawPtr ty) : ¬ Heap.offset m p count s q s' := by
  rintro ⟨⟨actual, ha, _, hb⟩, _, hindex, _⟩
  have he : actual = n := Option.some.inj (ha.symm.trans hs)
  grind

/-- A signed displacement cannot move before the beginning. -/
example (s s' : Heap m.Repr) (p q : RawPtr ty) (count : Int)
    (hbound : (p.index : Int) + count < 0) :
    ¬ Heap.offset m p count s q s' := by
  rintro ⟨_, _, hindex, _⟩
  grind

/-- An invalid starting index cannot be repaired by moving back into the allocation. -/
example (s s' : Heap m.Repr) (p q : RawPtr ty) (n : Nat) (count : Int)
    (hs : s.extent m ty p.base = some n) (hbound : n < p.index) :
    ¬ Heap.offset m p count s q s' := by
  rintro ⟨⟨actual, ha, hb, _⟩, _⟩
  have he : actual = n := Option.some.inj (ha.symm.trans hs)
  exact (Nat.not_le_of_lt hbound) (he ▸ hb)

/-- Empty borrow and share ranges are literal no-ops, without assuming a live base. -/
example (s s' : Heap m.Repr) (p : RawPtr ty) :
    Heap.borrowRange m p 0 s [] s' ↔ s' = s := by
  simp [Heap.borrowRange, Heap.replaceRange, Cell.full]

example (s s' : Heap m.Repr) (p : RawPtr ty) :
    Heap.shareRange m p 0 s [] s' ↔ s' = s := by
  simp [Heap.shareRange, Heap.replaceRange]

/-- A disjoint interpretation survives an update, including failed decoding. -/
example (s s' : Heap m.Repr) (p : RawPtr T) (value : T) (q : RawPtr U)
    (hu : Heap.write m p value s () s')
    (hd : CellsDisjoint m.byteLength T p.index U q.index) :
    Heap.observe m s' q = Heap.observe m s q :=
  hu.preserves_disjoint q (Or.inr hd)

/-- Failed decoding cannot authorize a write to shared bytes. -/
example (s s' : Heap m.Repr) (r : m.Repr) (p : RawPtr T) (q : RawPtr U)
    (hs : s.cells p.base = some r) (hb : q.base = p.base)
    (hv : m.view T r p.index (.shared (depth + 1) original))
    (b : Nat) (htlo : p.index * m.byteLength T ≤ b)
    (hthi : b < (p.index + 1) * m.byteLength T)
    (hulo : q.index * m.byteLength U ≤ b)
    (huhi : b < (q.index + 1) * m.byteLength U) (value : U) :
    ¬ Heap.write m q value s () s' := by
  have hp := m.view_permission _ _ _ _ hv b htlo hthi
  exact Heap.write.denied_by_byte (by simpa [hb] using hs) b hulo huhi
    (.shared (depth + 1)) hp (by simp) value

/-- Borrowing the second four-byte cell protects byte five, not byte index one. -/
theorem crossTypeBorrow (m : Layout.{0}) (s s' : Heap m.Repr) (base : BasePtr)
    (r r' : m.Repr) (h32 : m.byteLength U32 = 4) (h8 : m.byteLength U8 = 1)
    (hu : m.setCell U32 1 (some .borrowed) r r') (hs : s.cells base = some r')
    (value : U8) :
    m.decode U8 r' 5 = none ∧
      ¬ Heap.read m (⟨base, 5⟩ : RawPtr U8) s value s' ∧
      ¬ Heap.write m (⟨base, 5⟩ : RawPtr U8) value s () s' ∧
      ¬ Heap.endBorrowRange m (⟨base, 5⟩ : RawPtr U8) [value] s () s' := by
  have ht : U32 ≠ U8 := by
    intro he
    have := congrArg m.byteLength he
    grind
  have hoverlap : ¬ CellsDisjoint m.byteLength U32 1 U8 5 := by
    simp [CellsDisjoint, ht, h32, h8]
  have hp : m.permission r' 5 = some .borrowed :=
    m.view_permission _ _ _ _ (m.set_view _ _ _ _ _ hu) 5
      (by simp [h32]) (by simp [h32])
  have hnone : m.decode U8 r' 5 = none := by
    cases he : m.decode U8 r' 5
    · rfl
    · rename_i c
      exact (m.set_borrow_type _ _ _ _ hu U8 5 ht hoverlap c
        (Layout.decode_eq_some.mp he)).elim
  exact ⟨hnone,
    Heap.read.denied_by_byte hs 5 (by simp [h8]) (by simp [h8])
      .borrowed hp (by simp) value,
    Heap.write.denied_by_byte hs 5 (by simp [h8]) (by simp [h8])
      .borrowed hp (by simp) value,
    Heap.endBorrowRange.denied_other_type hu ⟨base, 5⟩ hs ht hoverlap [value] (by simp)⟩

/-- A four-byte integer store into the second half of a pointer destroys its typed validity. -/
theorem integerWriteInvalidatesPointer (m : Layout.{0}) (s s' : Heap m.Repr)
    (base : BasePtr) (value : U32)
    (h32 : m.byteLength U32 = 4) (hp : m.byteLength (RawPtr U32) = 8)
    (hint : m.kind U32 = .integer) (hptr : m.kind (RawPtr U32) = .pointer)
    (hw : Heap.write m (⟨base, 1⟩ : RawPtr U32) value s () s') :
    Heap.observe m s' (⟨base, 0⟩ : RawPtr (RawPtr U32)) = none := by
  have ht : U32 ≠ RawPtr U32 := by
    intro he
    have := congrArg m.kind he
    grind
  apply hw.invalidates_pointer ⟨base, 0⟩ rfl hint hptr
  simp [CellsDisjoint, ht, h32, hp]

/-- Distinct typed indices need not be disjoint; disjoint byte intervals are sufficient. -/
example (m : Layout.{0}) (s s' : Heap m.Repr) (base : BasePtr) (value : U8)
    (h32 : m.byteLength U32 = 4) (h8 : m.byteLength U8 = 1)
    (hw : Heap.write m (⟨base, 3⟩ : RawPtr U8) value s () s') :
    Heap.observe m s' (⟨base, 1⟩ : RawPtr U32) =
      Heap.observe m s (⟨base, 1⟩ : RawPtr U32) := by
  apply hw.preserves_disjoint ⟨base, 1⟩
  right
  exact Or.inr (Or.inr (by simp [h32, h8]))

/-- A mixed-permission four-byte interpretation fails instead of averaging permissions. -/
example (m : Layout.{0}) (r : m.Repr) (h32 : m.byteLength U32 = 4)
    (ha : m.permission r 4 = some .borrowed) (hb : m.permission r 5 = some (.shared 0)) :
    m.decode U32 r 1 = none := by
  exact Heap.decode_none_of_permission_conflict
    (a := 4) (b := 5) (by simp [h32]) (by simp [h32]) (by simp [ha, hb])

def byteCodec : ByteCodec (BitVec 8) where
  byteLength := 1
  encode value := [value]
  decode bytes := match bytes with | [value] => some value | _ => none
  supports _ := True
  encode_length _ := rfl
  roundTrip _ _ := rfl

/-- Client codecs constrain the actual bytes of successful raw writes. -/
example (m : Layout.{0}) (s s' : Heap m.Repr) (p : RawPtr (BitVec 8)) (value : BitVec 8)
    (hc : m.Realizes (BitVec 8) byteCodec) (hw : Heap.write m p value s () s') :
    ∃ r, s'.cells p.base = some r ∧
      ((m.bytes r).drop p.index).take 1 = [value] := by
  obtain ⟨r, hs, _, hb⟩ := hw.bytes byteCodec hc
  exact ⟨r, hs, by simpa [byteCodec] using hb⟩

/-- Writing back a failed observation changes nothing, even when the base is absent. -/
example (s s' : Heap m.Repr) (p : RawPtr ty) :
    Heap.writeBack m p none s s' ↔ s' = s := Heap.writeBack_none p s s'

/-- Heap relations alone do not authenticate backward computations: directly invoking
`endShareRange` can make a fresh shared exposure writable. This is intentionally a witness
to the trusted translation boundary, not a Rust-callable program or a valid borrow protocol. -/
theorem restoration_is_privileged (m : Layout.{u}) (s : Heap m.Repr) (hi : s.Inv)
    (original value : ty) :
    ∃ (p : RawPtr ty) (s₁ s₂ s₃ : Heap m.Repr),
      Heap.newSharedExposure m [original] s p s₁ ∧
      Heap.endShareRange m p [original] s₁ () s₂ ∧
      Heap.write m p value s₂ () s₃ := by
  let p : RawPtr ty := ⟨s.next, 0⟩
  obtain ⟨r₁, hc⟩ := m.create_exists ty [.shared 1 original]
  have hv₁ : m.view ty r₁ 0 (.shared 1 original) := m.create_view _ _ _ hc 0 (by simp)
  obtain ⟨r₂, hu₂⟩ := m.set_exists ty 0 r₁ (m.view_bound _ _ _ _ hv₁) (.shared 0 original)
  have hv₂ := m.set_view _ _ _ _ _ hu₂
  obtain ⟨r₃, hu₃⟩ := m.set_exists ty 0 r₂ (m.view_bound _ _ _ _ hv₂) (.shared 0 value)
  let s₁ := s.createRepr r₁ false
  let s₂ := s₁.storeRepr p.base r₂
  refine ⟨p, s₁, s₂, s₂.storeRepr p.base r₃, ⟨hi, rfl, r₁, hc, rfl⟩, ⟨0, ?_⟩, ?_⟩
  · apply (ite_eq_right (by simp)).mpr
    refine ⟨rfl, r₁, r₂, ?_, ?_, .cons hu₂ (.nil _ _), rfl⟩
    · simp [s₁, p, Heap.createRepr, update]
    · intro i hi
      have he : i = 0 := by simpa using hi
      subst i
      exact hv₁
  · exact ⟨r₂, r₃, by simp [s₂], Heap.writable_of_view hv₂ True.intro, hu₃, rfl⟩

/- The effect bridge must reject undefined behaviour, failure, divergence, and a
postcondition that accepts only one of several possible successors. -/
example (s : State.{0}) :
    ¬ HeapWP.Spec (Result.guardedModify (fun _ (_ : Nat) _ => False))
      (fun _ _ => True) s := by
  rw [HeapWP.Spec.guardedModify]
  rintro ⟨⟨_, _, h⟩, _⟩
  exact h

example (s : State.{0}) :
    ¬ HeapWP.Spec (Result.guardedModify
      (fun s₀ (x : Nat) s₁ => (x = 0 ∨ x = 1) ∧ s₁ = s₀))
      (fun x _ => x = 0) s := by
  rw [HeapWP.Spec.guardedModify]
  rintro ⟨_, h⟩
  have he := h 1 s ⟨Or.inr rfl, rfl⟩
  exact Nat.noConfusion he

example (s : State.{0}) :
    HeapWP.Spec (Result.guardedModify
      (fun s₀ (x : Nat) s₁ => (x = 0 ∨ x = 1) ∧ s₁ = s₀))
      (fun x s₁ => (x = 0 ∨ x = 1) ∧ s₁ = s) s := by
  rw [HeapWP.Spec.guardedModify]
  exact ⟨⟨0, s, Or.inl rfl, rfl⟩, fun _ _ h => h⟩

example (s : State.{0}) :
    ¬ HeapWP.Spec (Result.fail .undef : Result Nat) (fun _ _ => True) s :=
  HeapWP.Spec.fail .undef

example (s : State.{0}) :
    ¬ HeapWP.Spec (Result.div : Result Nat) (fun _ _ => True) s :=
  HeapWP.Spec.div

end Aeneas.Std.HeapTests
