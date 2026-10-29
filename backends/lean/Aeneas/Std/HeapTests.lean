module

import Aeneas.Std.HeapLemmas
import Aeneas.Std.Scalar.Notations
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

/-! Composed heap lifecycles and rejection examples for the block relations.
The commands reproduce the relational effects of the Rust wrappers; they do not
constitute an integration with the ordinary effect-rejecting weakest precondition. -/

namespace Aeneas.Std.HeapTests

open SepLogic

universe u

def boxIntoFromRaw (value : Nat) : Cmd Nat :=
  Cmd.bind (Heap.newBlock [value] true) fun p =>
  Cmd.bind (Heap.read p) fun x =>
  Cmd.bind (Heap.freeBlock p 1 true) fun _ =>
  Cmd.pure x

theorem boxIntoFromRaw.spec (value : Nat) :
    Triple emp (boxIntoFromRaw value) (fun x h => x = value ∧ emp h) := by
  apply Triple.bind (newBlock.spec [value] true)
  intro p
  apply Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp) (fun _ _ h => h)
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun x h hp => (sep_and_left (x = value)
      (block p [.shared 0 (some value)]) (alloc p 1 true) h).mp hp)
    (frame (R := alloc p 1 true) (read.spec p value 0)))
  intro x
  apply Triple.pure_pre
  intro hx
  subst x
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (freeBlock.spec p [.shared 0 (some value)] true (by simp [Cell.writable])))
  intro _
  exact Triple.pure emp value

def borrowLifecycle (a b : Nat) : Cmd (List Nat × Nat) :=
  Cmd.bind (Heap.alloc (ty := Nat) 1) fun p =>
  Cmd.bind (Heap.write p a) fun _ =>
  Cmd.bind (Heap.borrowRange p 1) fun original =>
  Cmd.bind (Heap.endBorrowRange p [b]) fun _ =>
  Cmd.bind (Heap.read p) fun value =>
  Cmd.bind (Heap.freeBlock p 1 true) fun _ =>
  Cmd.pure (original, value)

theorem borrowLifecycle.spec (a b : Nat) (hsize : 0 < Heap.size Nat) :
    Triple emp (borrowLifecycle a b) (fun result h => result = ([a], b) ∧ emp h) := by
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun _ h hp => (sep_comm _ _ h).mp hp) (alloc.spec Nat 1))
  intro p
  apply Triple.bind (frame (R := alloc p 1 true)
    (write.spec p (.shared 0 none) a rfl))
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
      (block p [.shared 0 (some b)]) (alloc p 1 true) h).mp hp)
    (frame (R := alloc p 1 true) (read.spec p b 0)))
  intro value
  apply Triple.pure_pre
  intro hvalue
  subst value
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (freeBlock.spec p [.shared 0 (some b)] true (by simp [Cell.writable])))
  intro _
  exact Triple.pure emp ([a], b)

/-- Borrow one cell, update its neighbor in the same representation, then restore it. -/
def neighboringBorrow (p : RawPtr Nat) (a' b' : Nat) : Cmd (List Nat) :=
  Cmd.bind (Heap.borrowRange p 1) fun original =>
  Cmd.bind (Heap.write (⟨p.base, p.index + 1⟩) b') fun _ =>
  Cmd.bind (Heap.endBorrowRange p [a']) fun _ =>
  Cmd.pure original

theorem neighboringBorrow.spec (p : RawPtr Nat) (a b a' b' : Nat)
    (hsize : 0 < Heap.size Nat) :
    Triple (block p (Cell.full [a, b])) (neighboringBorrow p a' b')
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
      (write.spec (⟨p.base, p.index + 1⟩) (.shared 0 (some b)) b' rfl)))
  intro _
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun _ h hp => (block_append p (Cell.full [a']) (Cell.full [b']) h).mpr hp)
    (frame (R := block (⟨p.base, p.index + 1⟩) (Cell.full [b']))
      (endBorrowRange.spec p [a'])))
  intro _
  exact Triple.pure (block p (Cell.full [a', b'])) [a]

def nestedSharing (p : RawPtr Nat) : Cmd Nat :=
  Cmd.bind (Heap.shareRange p 1) fun _ =>
  Cmd.bind (Heap.shareRange p 1) fun _ =>
  Cmd.bind (Heap.read p) fun value =>
  Cmd.bind (Heap.endShareRange p [value]) fun _ =>
  Cmd.bind (Heap.endShareRange p [value]) fun _ =>
  Cmd.pure value

theorem nestedSharing.spec (p : RawPtr Nat) (a : Nat) :
    Triple (pointsTo p a) (nestedSharing p)
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
  exact Triple.pure (pointsTo p a) a

def sharedExposureLifecycle (a : Nat) : Cmd Nat :=
  Cmd.bind (Heap.newSharedExposure [a]) fun p =>
  Cmd.bind (Heap.read p) fun value =>
  Cmd.bind (Heap.endSharedExposure p [a]) fun _ =>
  Cmd.pure value

theorem sharedExposureLifecycle.spec (a : Nat) :
    Triple emp (sharedExposureLifecycle a) (fun value h => value = a ∧ emp h) := by
  apply Triple.bind (newSharedExposure.spec [a])
  intro p
  apply Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp) (fun _ _ h => h)
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun value h hp => (sep_and_left (value = a)
      (block p [.shared 1 (some a)]) (alloc p 1 false) h).mp hp)
    (frame (R := alloc p 1 false) (read.spec p a 1)))
  intro value
  apply Triple.pure_pre
  intro hvalue
  subst value
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (endSharedExposure.spec p [a]))
  intro _
  exact Triple.pure emp a

def emptyAllocation : Cmd Unit :=
  Cmd.bind (Heap.alloc (ty := Nat) 0) fun p =>
  Cmd.bind (Heap.offset p 0) fun q =>
  Heap.freeBlock q 0 true

theorem emptyAllocation.spec :
    Triple emp (emptyAllocation ) (fun _ => emp) := by
  apply Triple.bind (alloc.spec Nat 0)
  intro p
  apply Triple.bind (offsetWholeBlock.spec p [] true 0 0 (by simp) (by simp))
  intro q
  apply Triple.pure_pre
  intro hq
  subst q
  simpa using freeBlock.spec p [] true (by simp)

/-- Move to one-past-the-end, then return using a negative displacement. -/
def signedRoundTrip (p : RawPtr Nat) : Cmd (RawPtr Nat) :=
  Cmd.bind (Heap.offset p 2) fun finish => Heap.offset finish (-2)

theorem signedRoundTrip.spec (p : RawPtr Nat) (a b : Nat) :
    Triple (sep (alloc p 2 true) (block p (Cell.full [a, b])))
      (signedRoundTrip p)
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
example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (value : ty)
    (hm : Fragment.Matches s (cellsHeap p [(.shared 0 none)])) :
    ¬ Heap.read p s value s' :=
  read.denied hm rfl value

/-- An exclusive borrow blocks reads, raw writes, and whole-base cleanup. -/
example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (value : ty)
    (hm : Fragment.Matches s (cellsHeap p [.borrowed])) (count : Nat) :
    ¬ Heap.read p s value s' ∧ ¬ Heap.write p value s () s' ∧
      ¬ Heap.freeBlock (⟨p.base, 0⟩ : RawPtr ty) count true s () s' :=
  ⟨read.denied hm rfl value, write.denied hm (by simp [Cell.writable]) value,
    freeBlock.denied (q := ⟨p.base, 0⟩) hm (by simp [Cell.writable]) rfl count true⟩

/-- Shared permissions retain reads but exclude writes and cleanup. -/
example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (old value : ty) (depth count : Nat)
    (hm : Fragment.Matches s (cellsHeap p [.shared (depth + 1) (some old)])) :
    ¬ Heap.write p value s () s' ∧
      ¬ Heap.freeBlock (⟨p.base, 0⟩ : RawPtr ty) count false s () s' :=
  ⟨write.denied hm (by simp [Cell.writable]) value,
    freeBlock.denied (q := ⟨p.base, 0⟩) hm (by simp [Cell.writable]) rfl count false⟩

example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (count : Nat) (own : Bool)
    (hoff : p.index ≠ 0) : ¬ Heap.freeBlock p count own s () s' :=
  fun h => hoff h.1

example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (count : Nat)
    (hview : s.allocated p.base = false) : ¬ Heap.freeBlock p count true s () s' := by
  intro h
  simp [Heap.freeBlock, hview] at h

example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (count : Nat)
    (howned : s.allocated p.base = true) : ¬ Heap.freeBlock p count false s () s' := by
  intro h
  simp [Heap.freeBlock, howned] at h

example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (r : Std.Block.{u}) (count : Nat)
    (hs : s.cells p.base = some r) (hne : count ≠ Std.Block.extent ty r) (own : Bool) :
    ¬ Heap.freeBlock p count own s () s' := by
  rintro ⟨_, _, ⟨actual, ⟨r', ha, _, hext, _⟩, hn, _⟩, _⟩
  have he : r' = r := Option.some.inj (ha.symm.trans hs)
  exact hne (by grind)

/-- Removing the base prevents a second cleanup, even for an empty allocation. -/
example (s s' s'' : Heap Std.Block.{u}) (p : RawPtr ty) (count : Nat) (own : Bool)
    (h : Heap.freeBlock p count own s () s') :
    ¬ Heap.freeBlock p count own s' () s'' := by
  obtain ⟨_, _, _, rfl⟩ := h
  rintro ⟨_, _, ⟨cs, ⟨r, hs, _⟩, _⟩, _⟩
  simp at hs

example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (value : ty) :
    ¬ Heap.read p (s.remove p.base) value s' := by
  rintro ⟨⟨r, depth, hs, _⟩, _⟩
  simp at hs

example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (value : ty) :
    ¬ Heap.write p value (s.remove p.base) () s' := by
  rintro ⟨r, r', hs, _⟩
  simp at hs

example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (values : List ty) (hne : values ≠ []) :
    ¬ Heap.endBorrowRange p values (s.remove p.base) () s' := by
  intro hu
  have ho : List.replicate values.length (.borrowed : Cell ty) ≠ [] := by
    simpa using hne
  obtain ⟨_, r, r', hs, _⟩ := (ite_eq_right ho).mp hu
  simp at hs

/-- Fresh exposures cannot reuse a freed allocation's base. -/
example (s s' s'' : Heap Std.Block.{u}) (hi : s.Inv) (p q : RawPtr ty) (count : Nat)
    (hfree : Heap.freeBlock p count true s () s')
    (values : List ty) (hnew : Heap.newBlock values false s' q s'') :
    q.base ≠ p.base := by
  obtain ⟨_, _, ⟨cs, ⟨r, hs, _⟩, _⟩, rfl⟩ := hfree
  obtain ⟨_, rfl, _⟩ := hnew
  exact (Nat.ne_of_lt (hi.base_lt hs)).symm

example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (value : ty)
    (hm : Fragment.Matches s (cellsHeap p [.shared 2 (some value)])) :
    ¬ Heap.endSharedExposure p [value] s () s' := by
  rintro ⟨hoff, _, ⟨r, hs, _, _, hv, _⟩, _⟩
  have hv' : Std.Block.Views ty r p.index [.shared 1 (some value)] := by simpa [hoff] using hv
  have he := views_unique hm (by simp) hs hv'
  simp at he

example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) (n count : Nat)
    (hs : s.extent ty p.base = some n) (hbound : n < p.index + count)
    (q : RawPtr ty) : ¬ Heap.offset p count s q s' := by
  rintro ⟨⟨actual, ha, _, hb⟩, _, hindex, _⟩
  have he : actual = n := Option.some.inj (ha.symm.trans hs)
  grind

/-- A signed displacement cannot move before the beginning. -/
example (s s' : Heap Std.Block.{u}) (p q : RawPtr ty) (count : Int)
    (hbound : (p.index : Int) + count < 0) :
    ¬ Heap.offset p count s q s' := by
  rintro ⟨_, _, hindex, _⟩
  grind

/-- An invalid starting index cannot be repaired by moving back into the allocation. -/
example (s s' : Heap Std.Block.{u}) (p q : RawPtr ty) (n : Nat) (count : Int)
    (hs : s.extent ty p.base = some n) (hbound : n < p.index) :
    ¬ Heap.offset p count s q s' := by
  rintro ⟨⟨actual, ha, hb, _⟩, _⟩
  have he : actual = n := Option.some.inj (ha.symm.trans hs)
  exact (Nat.not_le_of_lt hbound) (he ▸ hb)

/-- Empty borrow and share ranges are literal no-ops, without assuming a live base. -/
example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) :
    Heap.borrowRange p 0 s [] s' ↔ s' = s := by
  simp [Heap.borrowRange, Heap.replaceRange, Cell.full]

example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) :
    Heap.shareRange p 0 s [] s' ↔ s' = s := by
  simp [Heap.shareRange, Heap.replaceRange]

/-- A disjoint interpretation survives an update, including failed decoding. -/
example (s s' : Heap Std.Block.{u}) (p : RawPtr T) (value : T) (q : RawPtr U)
    (hu : Heap.write p value s () s')
    (hd : CellsDisjoint T p.index U q.index) :
    Heap.observe s' q = Heap.observe s q :=
  hu.preserves_disjoint q (Or.inr hd)

/-- Failed decoding cannot authorize a write to shared bytes. -/
example (s s' : Heap Std.Block.{u}) (r : Std.Block.{u}) (p : RawPtr T) (q : RawPtr U)
    (hs : s.cells p.base = some r) (hb : q.base = p.base)
    (hv : Std.Block.view T r p.index (.shared (depth + 1) (some original)))
    (b : Nat) (htlo : p.index * Heap.size T ≤ b)
    (hthi : b < (p.index + 1) * Heap.size T)
    (hulo : q.index * Heap.size U ≤ b)
    (huhi : b < (q.index + 1) * Heap.size U) (value : U) :
    ¬ Heap.write q value s () s' := by
  obtain ⟨byte, hp, hd, _⟩ := Std.Block.view_bytes _ _ _ _ hv b htlo hthi
  have hn : ¬ byte.writable := by
    intro hw
    exact Nat.noConfusion (Option.some.inj (hd.symm.trans hw))
  exact Heap.write.denied_by_byte (by simpa [hb] using hs) b hulo huhi
    byte hp hn value

/-- Borrowing the second four-byte cell protects byte five, not byte index one. -/
theorem crossTypeBorrow (s s' : Heap Std.Block.{0}) (base : BasePtr)
    (r r' : Std.Block.{0}) (h32 : Heap.size U32 = 4) (h8 : Heap.size U8 = 1)
    (hu : Std.Block.setCell U32 1 (some .borrowed) r r') (hs : s.cells base = some r')
    (value : U8) :
    Std.Block.decode U8 r' 5 = none ∧
      ¬ Heap.read (⟨base, 5⟩ : RawPtr U8) s value s' ∧
      ¬ Heap.write (⟨base, 5⟩ : RawPtr U8) value s () s' ∧
      ¬ Heap.endBorrowRange (⟨base, 5⟩ : RawPtr U8) [value] s () s' := by
  have ht : U32 ≠ U8 := by
    intro he
    have := congrArg Heap.size he
    grind
  have hoverlap : ¬ CellsDisjoint U32 1 U8 5 := by
    simp [CellsDisjoint, ht, h32, h8]
  have hp : (Std.Block.bytes r')[5]? = some .borrowed :=
    Std.Block.view_borrowed_byte (Std.Block.set_view _ _ _ _ _ hu)
      (by simp [h32]) (by simp [h32])
  have hnone : Std.Block.decode U8 r' 5 = none := by
    cases he : Std.Block.decode U8 r' 5
    · rfl
    · rename_i c
      exact (Std.Block.set_borrow_type _ _ _ _ hu U8 5 ht hoverlap c
        (Std.Block.decode_eq_some.mp he)).elim
  exact ⟨hnone,
    Heap.read.denied_by_byte hs 5 (by simp [h8]) (by simp [h8])
      .borrowed hp rfl value,
    Heap.write.denied_by_byte hs 5 (by simp [h8]) (by simp [h8])
      .borrowed hp (by simp [Cell.writable]) value,
    Heap.endBorrowRange.denied_other_type hu ⟨base, 5⟩ hs ht hoverlap [value] (by simp)⟩

/-- A four-byte integer store into the second half of a pointer destroys its typed validity. -/
theorem integerWriteInvalidatesPointer (s s' : Heap Std.Block.{0})
    (base : BasePtr) (value : U32)
    (h32 : Heap.size U32 = 4) (hp : Heap.size (RawPtr U32) = 8)
    (hw : Heap.write (⟨base, 1⟩ : RawPtr U32) value s () s') :
    Heap.observe s' (⟨base, 0⟩ : RawPtr (RawPtr U32)) = none := by
  have ht : U32 ≠ RawPtr U32 := by
    intro he
    have := congrArg Heap.size he
    grind
  apply hw.invalidates_pointer ⟨base, 0⟩ rfl ht
  simp [CellsDisjoint, ht, h32, hp]

/-- Distinct typed indices need not be disjoint; disjoint byte intervals are sufficient. -/
example (s s' : Heap Std.Block.{0}) (base : BasePtr) (value : U8)
    (h32 : Heap.size U32 = 4) (h8 : Heap.size U8 = 1)
    (hw : Heap.write (⟨base, 3⟩ : RawPtr U8) value s () s') :
    Heap.observe s' (⟨base, 1⟩ : RawPtr U32) =
      Heap.observe s (⟨base, 1⟩ : RawPtr U32) := by
  apply hw.preserves_disjoint ⟨base, 1⟩
  right
  exact Or.inr (Or.inr (by simp [h32, h8]))

/-- A mixed-permission four-byte interpretation fails instead of averaging permissions. -/
example (r : Std.Block.{0}) (h32 : Heap.size U32 = 4)
    (ha : (Std.Block.bytes r)[4]? = some .borrowed)
    (hb : (Std.Block.bytes r)[5]? = some (.shared 0 none)) :
    Std.Block.decode U32 r 1 = none := by
  exact Heap.decode_none_of_depth_conflict
    (a := 4) (b := 5) (by simp [h32]) (by simp [h32]) (by simp [ha, hb])

def byteRepr : Heap.Repr U8 where
  size := 1
  alignment := ⟨1, 0, rfl⟩
  encode value := [value]
  decode bytes := match bytes with | [value] => some value | _ => none
  supports _ := True

/-- A two-byte-aligned base cannot be accessed as a four-byte-aligned type. -/
example (s s' : Heap Std.Block.{u}) (p q : RawPtr T) (value : T)
    (ha : s.alignment p.base = some ⟨2, 1, rfl⟩)
    (ht : (Heap.align T).val = 4) (count : Int) :
    Heap.observe s p = none ∧
      ¬ Heap.read p s value s' ∧
      ¬ Heap.write p value s () s' ∧
      ¬ Heap.offset p count s q s' := by
  have hn : ¬ Heap.Aligned T s p.base := by
    rintro ⟨a, hbase, hdiv⟩
    have he := Option.some.inj (hbase.symm.trans ha)
    subst a
    simp [ht] at hdiv
  refine ⟨by simp [Heap.observe, hn], ?_, ?_, ?_⟩
  · rintro ⟨⟨_, _, _, halign, _⟩, _⟩
    exact hn halign
  · rintro ⟨_, _, _, halign, _⟩
    exact hn halign
  · rintro ⟨⟨_, hextent, _⟩, _⟩
    simp [Heap.extent, hn] at hextent

/-- Missing byte values remain unreadable and retain their sharing protection. -/
example (s s' : Heap Std.Block.{u}) (p : RawPtr T) (r : Std.Block.{u})
    (hs : s.cells p.base = some r) (b : Nat)
    (hlo : p.index * Heap.size T ≤ b) (hhi : b < (p.index + 1) * Heap.size T)
    (hp : (Std.Block.bytes r)[b]? = some (.shared (depth + 1) none)) (value : T) :
    ¬ Heap.read p s value s' ∧ ¬ Heap.write p value s () s' := by
  refine ⟨Heap.read.denied_by_byte hs b hlo hhi _ hp rfl value, ?_⟩
  exact Heap.write.denied_by_byte hs b hlo hhi _ hp
    (by simp [Cell.writable]) value

/-- Client codecs constrain the actual bytes of successful raw writes. -/
example (s s' : Heap Std.Block.{0}) (p : RawPtr U8) (value : U8)
    (hr : Heap.repr U8 = byteRepr)
    (hc : Std.Block.Realizes U8) (hw : Heap.write p value s () s') :
    ∃ r, s'.cells p.base = some r ∧
      (((Std.Block.bytes r).drop p.index).take 1).map Cell.read = [some value] := by
  obtain ⟨r, hs, _, hb⟩ := hw.bytes hc
  exact ⟨r, hs, by simpa [Heap.size, hr, byteRepr] using hb⟩

/-- Writing back a failed observation changes nothing, even when the base is absent. -/
example (s s' : Heap Std.Block.{u}) (p : RawPtr ty) :
    Heap.writeBack p none s s' ↔ s' = s := Heap.writeBack_none p s s'

/-- Heap relations alone do not authenticate backward computations: directly invoking
`endShareRange` can make a fresh shared exposure writable. This is intentionally a witness
to the trusted translation boundary, not a Rust-callable program or a valid borrow protocol. -/
theorem restoration_is_privileged (s : Heap Std.Block.{u}) (hi : s.Inv)
    (original value : ty) :
    ∃ (p : RawPtr ty) (s₁ s₂ s₃ : Heap Std.Block.{u}),
      Heap.newSharedExposure [original] s p s₁ ∧
      Heap.endShareRange p [original] s₁ () s₂ ∧
      Heap.write p value s₂ () s₃ := by
  let p : RawPtr ty := ⟨s.next, 0⟩
  obtain ⟨r₁, hc⟩ := Std.Block.create_exists ty [.shared 1 (some original)]
  have hv₁ : Std.Block.view ty r₁ 0 (.shared 1 (some original)) := Std.Block.create_view _ _ _ hc 0 (by simp)
  obtain ⟨r₂, hu₂⟩ := Std.Block.set_exists ty 0 r₁ (Std.Block.view_bound _ _ _ _ hv₁) (.shared 0 (some original))
  have hv₂ := Std.Block.set_view _ _ _ _ _ hu₂
  obtain ⟨r₃, hu₃⟩ := Std.Block.set_exists ty 0 r₂ (Std.Block.view_bound _ _ _ _ hv₂) (.shared 0 (some value))
  let s₁ := s.createRepr r₁ false (Heap.align ty)
  let s₂ := s₁.storeRepr p.base r₂
  refine ⟨p, s₁, s₂, s₂.storeRepr p.base r₃, ⟨hi, rfl, r₁, hc, rfl⟩, ⟨0, ?_⟩, ?_⟩
  · apply (ite_eq_right (by simp)).mpr
    refine ⟨rfl, r₁, r₂, ?_, ?_, ?_, .cons hu₂ (.nil _ _), rfl⟩
    · simp [s₁, p]
    · simp [s₁, p]
    · intro i hi
      have he : i = 0 := by simpa using hi
      subst i
      exact hv₁
  · exact ⟨r₂, r₃, by simp [s₂, s₁, p], by simp [s₂, s₁, p],
      Heap.writable_of_view hv₂ rfl, hu₃, rfl⟩

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
