module

import Aeneas.Std.HeapLemmas
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
      (block p [.val (some 0) value]) (alloc p 1 true) h).mp hp)
    (frame (R := alloc p 1 true) (read.spec p value 0)))
  intro x
  apply Triple.pure_pre
  intro hx
  subst x
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (freeBlock.spec p [.val (some 0) value] true (by simp [Cell.writable])))
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

theorem borrowLifecycle.spec (m : Layout.{0}) (a b : Nat) :
    Triple m emp (borrowLifecycle m a b) (fun result h => result = ([a], b) ∧ emp h) := by
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun _ h hp => (sep_comm _ _ h).mp hp) (alloc.spec Nat 1))
  intro p
  apply Triple.bind (frame (R := alloc p 1 true)
    (write.spec p .uninitialized a True.intro))
  intro _
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun result h hp => (sep_and_left (result = [a])
      (block p (Cell.borrowed [a])) (alloc p 1 true) h).mp hp)
    (frame (R := alloc p 1 true) (borrowRange.spec p [a])))
  intro original
  apply Triple.pure_pre
  intro horiginal
  subst original
  apply Triple.bind (frame (R := alloc p 1 true) (endBorrowRange.spec p [a] [b] rfl))
  intro _
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun value h hp => (sep_and_left (value = b)
      (block p [.val (some 0) b]) (alloc p 1 true) h).mp hp)
    (frame (R := alloc p 1 true) (read.spec p b 0)))
  intro value
  apply Triple.pure_pre
  intro hvalue
  subst value
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (freeBlock.spec p [.val (some 0) b] true (by simp [Cell.writable])))
  intro _
  exact Triple.pure m emp ([a], b)

/-- Borrow one cell, update its neighbor in the same representation, then restore it. -/
def neighboringBorrow (m : Layout.{0}) (p : RawPtr Nat) (a' b' : Nat) : Cmd m (List Nat) :=
  Cmd.bind (Heap.borrowRange m p 1) fun original =>
  Cmd.bind (Heap.write m (p.shift 1) b') fun _ =>
  Cmd.bind (Heap.endBorrowRange m p [a']) fun _ =>
  Cmd.pure m original

theorem neighboringBorrow.spec (m : Layout.{0}) (p : RawPtr Nat) (a b a' b' : Nat) :
    Triple m (block p (Cell.full [a, b])) (neighboringBorrow m p a' b')
      (fun result h => result = [a] ∧ block p (Cell.full [a', b']) h) := by
  apply Triple.conseq
    (fun h hp => (block_append p (Cell.full [a]) (Cell.full [b]) h).mp hp)
    (fun _ _ h => h)
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun result h hp => (sep_and_left (result = [a])
      (block p (Cell.borrowed [a])) (block (p.shift 1) (Cell.full [b])) h).mp hp)
    (frame (R := block (p.shift 1) (Cell.full [b])) (borrowRange.spec p [a])))
  intro original
  apply Triple.pure_pre
  intro horiginal
  subst original
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => (sep_comm _ _ h).mp hp)
    (frame (R := block p (Cell.borrowed [a]))
      (write.spec (p.shift 1) (.val (some 0) b) b' True.intro)))
  intro _
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun _ h hp => (block_append p (Cell.full [a']) (Cell.full [b']) h).mpr hp)
    (frame (R := block (p.shift 1) (Cell.full [b']))
      (endBorrowRange.spec p [a] [a'] rfl)))
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

def sharedViewLifecycle (m : Layout.{0}) (a : Nat) : Cmd m Nat :=
  Cmd.bind (Heap.newSharedView m [a]) fun p =>
  Cmd.bind (Heap.read m p) fun value =>
  Cmd.bind (Heap.endSharedView m p [a]) fun _ =>
  Cmd.pure m value

theorem sharedViewLifecycle.spec (m : Layout.{0}) (a : Nat) :
    Triple m emp (sharedViewLifecycle m a) (fun value h => value = a ∧ emp h) := by
  apply Triple.bind (newSharedView.spec [a])
  intro p
  apply Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp) (fun _ _ h => h)
  apply Triple.bind (Triple.conseq (fun _ h => h)
    (fun value h hp => (sep_and_left (value = a)
      (block p [.val (some 1) a]) (alloc p 1 false) h).mp hp)
    (frame (R := alloc p 1 false) (read.spec p a 1)))
  intro value
  apply Triple.pure_pre
  intro hvalue
  subst value
  apply Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (endSharedView.spec p [a]))
  intro _
  exact Triple.pure m emp a

def emptyAllocation (m : Layout.{0}) : Cmd m Unit :=
  Cmd.bind (Heap.alloc m (ty := Nat) 0) fun p =>
  Cmd.bind (Heap.add m p 0) fun q =>
  Heap.freeBlock m q 0 true

theorem emptyAllocation.spec (m : Layout.{0}) :
    Triple m emp (emptyAllocation m) (fun _ => emp) := by
  apply Triple.bind (alloc.spec Nat 0)
  intro p
  apply Triple.bind (addWholeBlock.spec p [] true 0 (by simp))
  intro q
  apply Triple.pure_pre
  intro hq
  subst q
  simpa using freeBlock.spec (m := m) p [] true (by simp)

/-- Uninitialized storage is writable, but not readable. -/
example (s s' : Heap m.Repr) (p : RawPtr ty) (value : ty)
    (hm : Fragment.Matches m s (cellsHeap p [.uninitialized])) :
    ¬ Heap.read m p s value s' :=
  read.denied hm rfl value

/-- An exclusive borrow blocks reads, raw writes, and whole-base cleanup. -/
example (s s' : Heap m.Repr) (p : RawPtr ty) (old value : ty)
    (hm : Fragment.Matches m s (cellsHeap p [.val none old])) (count : Nat) :
    ¬ Heap.read m p s value s' ∧ ¬ Heap.write m p value s () s' ∧
      ¬ Heap.freeBlock m (⟨p.base, 0⟩ : RawPtr ty) count true s () s' :=
  ⟨read.denied hm rfl value, write.denied hm (by simp [Cell.writable]) value,
    freeBlock.denied (q := ⟨p.base, 0⟩) hm (by simp [Cell.writable]) rfl count true⟩

/-- Shared permissions retain reads but exclude writes and cleanup. -/
example (s s' : Heap m.Repr) (p : RawPtr ty) (old value : ty) (depth count : Nat)
    (hm : Fragment.Matches m s (cellsHeap p [.val (some (depth + 1)) old])) :
    ¬ Heap.write m p value s () s' ∧
      ¬ Heap.freeBlock m (⟨p.base, 0⟩ : RawPtr ty) count false s () s' :=
  ⟨write.denied hm (by simp [Cell.writable]) value,
    freeBlock.denied (q := ⟨p.base, 0⟩) hm (by simp [Cell.writable]) rfl count false⟩

example (s s' : Heap m.Repr) (p : RawPtr ty) (count : Nat) (own : Bool)
    (hoff : p.offset ≠ 0) : ¬ Heap.freeBlock m p count own s () s' :=
  fun h => hoff h.1

example (s s' : Heap m.Repr) (p : RawPtr ty) (count : Nat)
    (hview : s.allocated p.base = false) : ¬ Heap.freeBlock m p count true s () s' := by
  intro h
  simp [Heap.freeBlock, hview] at h

example (s s' : Heap m.Repr) (p : RawPtr ty) (count : Nat)
    (howned : s.allocated p.base = true) : ¬ Heap.freeBlock m p count false s () s' := by
  intro h
  simp [Heap.freeBlock, howned] at h

example (s s' : Heap m.Repr) (p : RawPtr ty) (cs : List (Cell ty)) (count : Nat)
    (hs : s.load m.interpret ty p.base = some cs) (hne : count ≠ cs.length) (own : Bool) :
    ¬ Heap.freeBlock m p count own s () s' := by
  rintro ⟨_, _, ⟨actual, ha, hn, _⟩, _⟩
  have he : actual = cs := Option.some.inj (ha.symm.trans hs)
  exact hne (he ▸ hn.symm)

/-- Removing the base prevents a second cleanup, even for an empty allocation. -/
example (s s' s'' : Heap m.Repr) (p : RawPtr ty) (count : Nat) (own : Bool)
    (h : Heap.freeBlock m p count own s () s') :
    ¬ Heap.freeBlock m p count own s' () s'' := by
  obtain ⟨_, _, _, rfl⟩ := h
  rintro ⟨_, _, ⟨cs, hs, _⟩, _⟩
  simp at hs

example (s s' : Heap m.Repr) (p : RawPtr ty) (value : ty) :
    ¬ Heap.read m p (s.remove p.base) value s' := by
  rintro ⟨⟨before, after, f, _, hs⟩, _⟩
  simp at hs

example (s s' : Heap m.Repr) (p : RawPtr ty) (value : ty) :
    ¬ Heap.write m p value (s.remove p.base) () s' := by
  rintro ⟨old, _, hu⟩
  obtain ⟨before, after, _, hs, _⟩ := hu.load (by simp)
  simp at hs

example (s s' : Heap m.Repr) (p : RawPtr ty) (values : List ty) (hne : values ≠ []) :
    ¬ Heap.endBorrowRange m p values (s.remove p.base) () s' := by
  rintro ⟨original, hu⟩
  have hl := replaceRange.length hu
  have ho : Cell.borrowed original ≠ [] := by
    intro he
    have hz : values.length = 0 := by simpa [he, Cell.full] using hl.symm
    exact hne (List.length_eq_zero_iff.mp hz)
  obtain ⟨before, after, _, hs, _⟩ := hu.load ho
  simp at hs

/-- Fresh views cannot reuse a freed allocation's base. -/
example (s s' s'' : Heap m.Repr) (hi : s.Inv) (p q : RawPtr ty) (count : Nat)
    (hfree : Heap.freeBlock m p count true s () s')
    (values : List ty) (hnew : Heap.newBlock m values false s' q s'') :
    q.base ≠ p.base := by
  obtain ⟨_, _, ⟨cs, hs, _⟩, rfl⟩ := hfree
  obtain ⟨_, rfl, _⟩ := hnew
  exact (Nat.ne_of_lt (hi.base_lt hs)).symm

example (s s' : Heap m.Repr) (p : RawPtr ty) (value : ty)
    (hm : Fragment.Matches m s (cellsHeap p [.val (some 2) value])) :
    ¬ Heap.endSharedView m p [value] s () s' := by
  rintro ⟨hoff, _, hs, _⟩
  have he := segment_unique hm (other := Cell.shared 1 [value])
    (before := []) (after := []) (by simp [Cell.shared]) (by simpa using hoff.symm)
    (by simpa using hs)
  simp [Cell.shared] at he

example (s s' : Heap m.Repr) (p : RawPtr ty) (cs : List (Cell ty)) (count : Nat)
    (hs : s.load m.interpret ty p.base = some cs) (hbound : cs.length < p.offset + count)
    (q : RawPtr ty) : ¬ Heap.add m p count s q s' := by
  rintro ⟨⟨actual, ha, hb⟩, _⟩
  have he : actual = cs := Option.some.inj (ha.symm.trans hs)
  exact (Nat.not_le_of_lt hbound) (he ▸ hb)

/-- Empty borrow and share ranges are literal no-ops, without assuming a live base. -/
example (s s' : Heap m.Repr) (p : RawPtr ty) :
    Heap.borrowRange m p 0 s [] s' ↔ s' = s := by
  simp [Heap.borrowRange, Heap.replaceRange, Cell.full, Cell.borrowed]

example (s s' : Heap m.Repr) (p : RawPtr ty) :
    Heap.shareRange m p 0 s [] s' ↔ s' = s := by
  simp [Heap.shareRange, Heap.replaceRange, Cell.shared]

/-- Changing a hidden `T` payload cannot change any successful or failed raw `U` read. -/
example (s s' : Heap m.Repr) (p : RawPtr T) (x y : T) (q : RawPtr U)
    (hb : q.base = p.base)
    (hu : Heap.replaceRange m s p [.val none x] [.val none y] s') (value : U) :
    Heap.read m q s value s ↔ Heap.read m q s' value s' := by
  have he : List.Forall₂ Cell.ReadEquivalent [.val none x] [.val none y] :=
    .cons True.intro .nil
  exact hu.hidden_read_iff he q hb value

example (s s' : Heap m.Repr) (p : RawPtr U) (value : U)
    (T : Type u) (original : T) (depth : Nat)
    (hs : s.load m.interpret T p.base = some [.val (some (depth + 1)) original])
    (hw : Heap.write m p value s () s') :
    (s'.load m.interpret T p.base).bind (fun cs => cs[0]?) =
      some (.val (some (depth + 1)) original) :=
  hw.preserves_protected hs 0 (by simp) (by simp [Cell.writable])

/-- Heap relations alone do not authenticate backward computations: directly invoking
`endShareRange` can make a fresh shared view writable. This is intentionally a witness
to the trusted translation boundary, not a Rust-callable program or a valid borrow protocol. -/
theorem restoration_is_privileged (m : Layout.{u}) (s : Heap m.Repr) (hi : s.Inv)
    (original value : ty) :
    ∃ (p : RawPtr ty) (s₁ s₂ s₃ : Heap m.Repr),
      Heap.newSharedView m [original] s p s₁ ∧
      Heap.endShareRange m p [original] s₁ () s₂ ∧
      Heap.write m p value s₂ () s₃ := by
  let p : RawPtr ty := ⟨s.next, 0⟩
  let s₁ := s.create m (Cell.shared 1 [original]) false
  let s₂ := s₁.store m.represent ty p.base [.val (some 0) original]
  let s₃ := s₂.store m.represent ty p.base [.val (some 0) value]
  have hs : s₁.load m.interpret ty p.base = some (Cell.shared 1 [original]) := by
    simpa [s₁, p, Heap.create] using m.roundTrip ty (Cell.shared 1 [original])
  refine ⟨p, s₁, s₂, s₃, ⟨hi, rfl, rfl⟩, ⟨0, ?_⟩, ?_⟩
  · apply (ite_eq_right (by simp [Cell.shared])).mpr
    exact ⟨rfl, [], [], rfl, by simpa using hs, rfl⟩
  · refine ⟨.val (some 0) original, True.intro, ?_⟩
    apply (ite_eq_right (by simp)).mpr
    exact ⟨rfl, [], [], rfl, by simp [s₂], rfl⟩

end Aeneas.Std.HeapTests
