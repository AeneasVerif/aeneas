module

public import RawRyuMwe.ByteOps
public import Aeneas.Std.Heap.SliceExposure
public import Aeneas.Std.Heap.RangeRestoration
import all Aeneas.Std.Heap.Allocation
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Slice
import all Aeneas.Std.Core.Ptr

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace scalar_mwe

set_option maxHeartbeats 1000000

/- A raw snapshot is not a typed read of MaybeUninit storage. Placements are
   explicit ghost choices in this handwritten adapter, not Rust arguments.
   The choice of allocation root remains demonic and subject to Heap.Inv. -/
def exposeBytes (bytes : List Aeneas.Std.Byte) (depth : Nat) (address : BasePtr) :
    Result (RawPtr U8) :=
  Result.allocatingModify fun s₀ p s₁ =>
    ∃ root : Option Nat,
      s₀.createRepr ⟨address, root.getD s₀.next,
        bytes.map (Cell.shared depth), false, true, true⟩ = some (p.provenance, s₁) ∧
      p.address = address

abbrev storageAt (p : RawPtr U8) (bytes : List Aeneas.Std.Byte) (depth : Nat) :=
  alloc Repr.u8 p p.address bytes.length false ∗ bytesAt p p.address bytes depth

def retained (p : RawPtr U8) (size : Nat) (s : Heap) : Prop :=
  ∃ block, s.allocations p.provenance = some block ∧ block.bptr = p.address ∧
    block.repr.length = size ∧ s.allocationAlive block = true

theorem retained_create (p : RawPtr U8) (size : Nat) (s₀ s₁ : Heap)
    (hi : s₀.Inv) (old : retained p size s₀) (fresh : Block) (id : Nat)
    (run : s₀.createRepr fresh = some (id, s₁)) : retained p size s₁ := by
  obtain ⟨block, lookup, base, len, alive⟩ := old
  obtain ⟨_, rfl⟩ := Heap.createRepr.success run
  have different := Nat.ne_of_lt (hi.base_lt lookup)
  refine ⟨block, by simpa [update, different] using lookup, base, len, ?_⟩
  cases hr : s₀.allocations block.root
  · simp [Heap.allocationAlive, hr] at alive
  · have rootDifferent := Nat.ne_of_lt (hi.base_lt hr)
    simpa [Heap.allocationAlive, update, rootDifferent, hr] using alive

theorem exposeBytes.spec (bytes : List Aeneas.Std.Byte) (depth : Nat) (address : BasePtr)
    (s₀ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec (exposeBytes bytes depth address)
      (fun p s₁ => p.address = address ∧
        (∀ old size, retained old size s₀ → retained old size s₁) ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧
          storageAt p bytes depth h) s₀ := by
  apply HeapWP.Spec.allocatingModify.mpr
  rintro p s₁ ⟨root, created, base⟩
  let fresh : Block :=
    ⟨address, root.getD s₀.next, bytes.map (Cell.shared depth), false, true, true⟩
  have success := Heap.createRepr.success created
  have valid := Heap.createRepr_Inv s₀ fresh p.provenance s₁ hi created
  have lookup : s₁.allocations p.provenance = some fresh := by
    simp [success.1, success.2, update, fresh]
  have live : s₁.live fresh = true := by
    have vb := valid.validBlock lookup
    cases hr : s₁.allocations fresh.root
    · simp [Heap.validBlock, hr] at vb
    · simp [Heap.validBlock, Heap.live, hr, fresh] at vb ⊢
      agrind
  obtain ⟨_, post⟩ := createRepr.spec s₀ fresh (success.2 ▸ valid.2) (success.2 ▸ live)
    ∅ F rfl (Fragment.disjoint_empty_left F) (by simpa using hm) hi
  obtain ⟨h, hd, hm₁, hi₁, _, whole⟩ := post p.provenance s₁ created
  refine ⟨base, fun old size hp => retained_create old size s₀ s₁ hi hp fresh
    p.provenance created, h, hd, hm₁, hi₁, ?_⟩
  refine ⟨allocHeap Repr.u8 address p.provenance bytes.length false,
    cellsHeap address p.provenance 0 (bytes.map (Cell.shared depth)), ?_, ?_, ?_, ?_⟩
  · rintro _ rfl _ ⟨i, hi, rfl⟩
    right
    simp [Resource.key]
  · simpa [fresh, allocHeap, Repr.u8] using whole
  · exact ⟨rfl, by simp only [base]⟩
  · exact ⟨by simp [base], by simp [Repr.u8], by simp [base, RawPtr.offsetFrom]⟩

theorem whole_storage (p : RawPtr U8) (bytes : List Aeneas.Std.Byte) (depth : Nat)
    (h : Fragment) (s : Heap) (hp : storageAt p bytes depth h)
    (hm : Fragment.Matches s h) :
    ∃ block, s.allocations p.provenance = some block ∧ s.live block = true ∧
      block.bptr = p.address ∧ block.owned = false ∧
      block.repr = bytes.map (Cell.shared depth) ∧
      h = Fragment.single (.cleanup p.provenance block.repr.length block.bptr false) ∪
        cellsHeap block.bptr p.provenance 0 block.repr := by
  obtain ⟨a, b, _, rfl, ⟨_, rfl⟩, _, _, cells⟩ := hp
  obtain ⟨hma, hmb⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨block, lookup, len, live, base, own⟩ := hma _ rfl
  have length : block.repr.length = bytes.length := by simpa [Repr.u8] using len
  have repr : block.repr = bytes.map (Cell.shared depth) := by
    apply List.ext_getElem?
    intro i
    by_cases bound : i < bytes.length
    · have resource : Resource.Holds s (.cell p.provenance i p.address (.shared depth bytes[i])) := by
        have selected := hmb (.cell p.provenance i p.address (.shared depth bytes[i]))
        apply selected
        rw [cells]
        exact ⟨i, by simpa using bound, by simp [RawPtr.offsetFrom]⟩
      obtain ⟨actual, hl, _, _, selected⟩ := resource
      have eq := Option.some.inj (hl.symm.trans lookup)
      subst actual
      simpa [List.getElem?_eq_getElem bound] using selected
    · simp [List.getElem?_eq_none (by agrind : block.repr.length ≤ i),
        List.getElem?_eq_none (by simp; agrind : (bytes.map (Cell.shared depth)).length ≤ i)]
  exact ⟨block, lookup, live, base, own, repr,
    by simp [allocHeap, Repr.u8, base, cells, repr, RawPtr.offsetFrom]⟩

def closeBytes (p : RawPtr U8) (size depth : Nat) : Result Unit :=
  Result.checkedModify fun s₀ (_ : Unit) s₁ =>
    Heap.endExposureAt Repr.u8 p size depth s₀ = some s₁

theorem closeBytes.spec (p : RawPtr U8) (bytes : List Aeneas.Std.Byte) (depth : Nat) :
    HeapWP.Triple (storageAt p bytes depth) (closeBytes p bytes.length depth)
      (fun _ => empty) := by
  apply HeapWP.Triple.checkedModify
  intro h F s₀ hp hd hm hi
  obtain ⟨block, lookup, live, base, own, repr, whole⟩ :=
    whole_storage p bytes depth h s₀ hp ((Fragment.matches_union _ _ _).mp hm).1
  have invariant := Heap.retire_Inv hi p.provenance
  have commit : Heap.commit (s₀.retire p.provenance) = some (s₀.retire p.provenance) := by
    simp [Heap.commit, invariant.2]
  have run : Heap.endExposureAt Repr.u8 p bytes.length depth s₀ =
      some (s₀.retire p.provenance) := by
    simp [Heap.endExposureAt, lookup, live, base, own, repr, Repr.u8, Cell.depth, commit]
  obtain ⟨_, post⟩ := retire.spec s₀ p.provenance block lookup h F
    (by simpa [own] using whole) hd hm hi
  refine ⟨⟨(), _, run⟩, ?_⟩
  intro _ s₁ result
  have eq := Option.some.inj (result.symm.trans run)
  subst s₁
  exact post () _ commit

def snapshotBytes (p : RawPtr U8) : Result (List Aeneas.Std.Byte) :=
  Result.checkedModify fun s₀ bytes s₁ =>
    ∃ block, s₀.allocations p.provenance = some block ∧ s₀.live block = true ∧
      block.bptr = p.address ∧ block.repr.mapM Cell.read = some bytes ∧ s₁ = s₀

theorem snapshotBytes.spec (p : RawPtr U8) (bytes : List Aeneas.Std.Byte) (depth : Nat)
    (h F : Fragment) (s₀ : Heap) (hp : storageAt p bytes depth h)
    (hm : Fragment.Matches s₀ (h ∪ F)) :
    HeapWP.Spec (snapshotBytes p) (fun result s₁ => result = bytes ∧ s₁ = s₀) s₀ := by
  obtain ⟨block, lookup, live, base, _, repr, _⟩ :=
    whole_storage p bytes depth h s₀ hp ((Fragment.matches_union _ _ _).mp hm).1
  have read : block.repr.mapM Cell.read = some bytes := by
    rw [repr]
    clear hp repr
    induction bytes
    · rfl
    · rename_i byte bytes ih
      simp only [List.map_cons, List.mapM_cons, Cell.read, ih]
      rfl
  apply HeapWP.Spec.checkedModify.mpr
  refine ⟨⟨bytes, s₀, block, lookup, live, base, read, rfl⟩, ?_⟩
  rintro result s₁ ⟨other, hl, _, _, hr, rfl⟩
  have eq := Option.some.inj (hl.symm.trans lookup)
  subst other
  exact ⟨Option.some.inj (hr.symm.trans read), rfl⟩

theorem allocationAlive_retire (s : Heap) (id : Nat) (block : Block) :
    (s.retire id).allocationAlive block = s.allocationAlive block := by
  by_cases eq : block.root = id
  · simp [Heap.allocationAlive, Heap.retire, update, eq, Option.map_map, Function.comp_def]
  · simp [Heap.allocationAlive, Heap.retire, update, eq]

theorem retained_retire (p : RawPtr U8) (size : Nat) (s : Heap) (id : Nat)
    (hp : retained p size s) : retained p size (s.retire id) := by
  obtain ⟨block, lookup, base, len, alive⟩ := hp
  by_cases eq : p.provenance = id
  · refine ⟨{ block with active := false }, ?_, base, len, ?_⟩
    · simp [Heap.retire, update, ← eq, lookup]
    · rw [allocationAlive_retire]
      exact alive
  · exact ⟨block, by simp [Heap.retire, update, eq, lookup], base, len,
      (allocationAlive_retire s id block).trans alive⟩

theorem closeBytes.state_spec (p : RawPtr U8) (bytes : List Aeneas.Std.Byte) (depth : Nat)
    (h F : Fragment) (s₀ : Heap) (hp : storageAt p bytes depth h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s₀ (h ∪ F)) (hi : s₀.Inv) :
    HeapWP.Spec (closeBytes p bytes.length depth)
      (fun _ s₁ => s₁.Inv ∧ Fragment.Matches s₁ F ∧ retained p bytes.length s₁ ∧
        ∀ old size, retained old size s₀ → retained old size s₁) s₀ := by
  obtain ⟨block, lookup, live, base, own, repr, _⟩ :=
    whole_storage p bytes depth h s₀ hp ((Fragment.matches_union _ _ _).mp hm).1
  have kept : retained p bytes.length s₀ :=
    ⟨block, lookup, base, by simp [repr], Heap.allocationAlive_of_live s₀ block live⟩
  have inv := Heap.retire_Inv hi p.provenance
  have run : Heap.endExposureAt Repr.u8 p bytes.length depth s₀ =
      some (s₀.retire p.provenance) := by
    simp [Heap.endExposureAt, lookup, live, base, own, repr, Repr.u8,
      Cell.depth, Heap.commit, inv.2]
  obtain ⟨enabled, post⟩ := HeapWP.Spec.checkedModify.mp
    (closeBytes.spec p bytes depth h F s₀ hp hd hm hi)
  apply HeapWP.Spec.checkedModify.mpr
  refine ⟨enabled, ?_⟩
  intro result s₁ hr
  obtain ⟨h₁, _, hm₁, hi₁, empty₁⟩ := post result s₁ hr
  have eq := Option.some.inj (hr.symm.trans run)
  subst s₁
  subst h₁
  exact ⟨hi₁, by simpa using hm₁, retained_retire p bytes.length s₀ p.provenance kept,
    fun old size hp => retained_retire old size s₀ p.provenance hp⟩

theorem borrow_prefix.spec (p : RawPtr U8) (base : BasePtr) (values : Vector U8 n)
    (suffix : List Aeneas.Std.Byte) (depth : Nat) (count : Usize)
    (len : count.val = n) (positive : 0 < n)
    (h F : Fragment) (s₀ : Heap)
    (hp : bytesAt p base (values.toList.map Byte.data ++ suffix) depth h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s₀ (h ∪ F)) (hi : s₀.Inv) :
    HeapWP.Spec (core.slice.raw.from_raw_parts Repr.u8 p count)
      (fun result s₁ => result.1.val = values.toList ∧
        HeapWP.Spec result.2 (fun _ s₂ => s₂ = s₀) s₁) s₀ := by
  obtain ⟨lower, aligned, cells⟩ := hp
  let front := (values.toList.map Byte.data).map (Cell.shared depth)
  let tail := suffix.map (Cell.shared depth)
  let a := cellsHeap base p.provenance (p.offsetFrom base) front
  let b := cellsHeap base p.provenance (p.offsetFrom base + front.length) tail
  have split : h = a ∪ b := by
    simpa [List.map_append, cellsHeap_append, a, b, front, tail] using cells
  have ab : a.Disjoint b := disjoint_cellsHeap_append _ _ _ front tail
  have aF := (Fragment.disjoint_union_left.mp (split ▸ hd)).1
  have prefixCells : pointsToRange Repr.u8 p base values depth a := by
    apply (raw_memory_views.u8_range p base values depth a).mpr
    exact ⟨lower, aligned, by simp [a, front, Vector.toList_map]⟩
  have matching : Fragment.Matches s₀ (a ∪ (b ∪ F)) := by
    simpa [split, Fragment.union_assoc] using hm
  have separated := Fragment.disjoint_union_right.mpr ⟨ab, aF⟩
  unfold core.slice.raw.from_raw_parts
  rw [len]
  apply HeapWP.Spec.bind
    (HeapWP.shareRange_return.spec Repr.u8 p base values depth positive (by decide)
      a (b ∪ F) s₀ prefixCells separated matching hi)
  rintro data s₁ ⟨rfl, returning⟩
  have fits : values.toList.length ≤ Usize.max := by
    simp only [Vector.length_toList]
    rw [← len]
    scalar_tac
  rw [dite_eq_left fits]
  apply (HeapWP.Spec.pure _ _ _).mpr
  simpa only [Slice.from_val] using And.intro (rfl : values.toList = values.toList) returning

/- A scoped materialization retains the raw bytes through its actual return.
   The proof below quantifies over every successful fresh-view choice. -/
def withStorage (old : List Aeneas.Std.Byte) (address : BasePtr)
    (action : RawPtr U8 → Result α) : Result (α × List Aeneas.Std.Byte) := do
  let p ← exposeBytes old 0 address
  let result ← action p
  let updated ← snapshotBytes p
  closeBytes p old.length 0
  pure (result, updated)

theorem withStorage.spec (old new : List Aeneas.Std.Byte) (address : BasePtr)
    (action : RawPtr U8 → Result α) (post : α → Prop) (len : new.length = old.length)
    (body : ∀ p, p.address = address →
      HeapWP.Triple (storageAt p old 0) (action p)
        (fun result h => post result ∧ storageAt p new 0 h))
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (withStorage old address action)
      (fun result s₁ => post result.1 ∧ result.2 = new ∧ s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  unfold withStorage
  apply HeapWP.Spec.bind (exposeBytes.spec old 0 address s₀ F hi hm)
  rintro p s₁ ⟨addr, _, h₁, hd₁, hm₁, hi₁, hp₁⟩
  apply HeapWP.Spec.bind (body p addr h₁ F s₁ hp₁ hd₁ hm₁ hi₁)
  rintro result s₂ ⟨h₂, hd₂, hm₂, hi₂, resultPost, hp₂⟩
  apply HeapWP.Spec.bind (snapshotBytes.spec p new 0 h₂ F s₂ hp₂ hm₂)
  rintro updated s₃ ⟨updatedEq, stateEq⟩
  subst updated
  subst s₃
  have closing := closeBytes.state_spec p new 0 h₂ F s₂ hp₂ hd₂ hm₂ hi₂
  rw [len] at closing
  apply HeapWP.Spec.bind closing
  rintro _ s₃ ⟨hi₃, hm₃, _, _⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨resultPost, rfl, hi₃, hm₃⟩

theorem preserve_storage (old new : List Aeneas.Std.Byte) (p : RawPtr U8)
    (action : Result α) (post : α → Prop) (len : new.length = old.length)
    (body : HeapWP.Triple (bytesAt p p.address old) action
      (fun result h => post result ∧ bytesAt p p.address new 0 h)) :
    HeapWP.Triple (storageAt p old 0) action
      (fun result h => post result ∧ storageAt p new 0 h) := by
  apply HeapWP.Triple.conseq (P' := bytesAt p p.address old ∗
      alloc Repr.u8 p p.address old.length false)
    (Q' := fun result => (fun h => post result ∧ bytesAt p p.address new 0 h) ∗
      alloc Repr.u8 p p.address old.length false)
  · intro h hp
    exact (sep_comm _ _ h).mp hp
  · rintro result h ⟨a, b, hd, rfl, ⟨resultPost, cells⟩, cleanup⟩
    exact ⟨resultPost, b, a, hd.symm, Fragment.union_comm _ _, len ▸ cleanup, cells⟩
  · exact HeapWP.frame body

theorem add_storage.spec (p : RawPtr U8) (bytes : List Aeneas.Std.Byte) (depth : Nat)
    (offset : Usize) (bound : offset.val < bytes.length)
    (h F : Fragment) (s₀ : Heap) (hp : storageAt p bytes depth h)
    (hm : Fragment.Matches s₀ (h ∪ F)) (hi : s₀.Inv) :
    HeapWP.Spec (RawPtr.add Repr.u8 p offset)
      (fun q s₁ => q.provenance = p.provenance ∧
        q.address.val = p.address.val + offset.val ∧ s₁ = s₀) s₀ := by
  obtain ⟨blk, lookup, live, base, _, repr, _⟩ :=
    whole_storage p bytes depth h s₀ hp ((Fragment.matches_union _ _ _).mp hm).1
  have len : blk.repr.length = bytes.length := by simp [repr]
  have valid := hi.validBlock lookup
  simp only [Heap.validBlock, Bool.and_eq_true] at valid
  have bounded := valid.1.1
  simp only [Heap.bounded, Bool.and_eq_true, decide_eq_true_eq, base, len] at bounded
  have fits : p.address.val + offset.val < 2 ^ UScalarTy.numBits .Usize := by agrind
  let q : RawPtr U8 := ⟨p.provenance, ⟨BitVec.ofNat _ (p.address.val + offset.val)⟩⟩
  have addr : q.address.val = p.address.val + offset.val := by
    change (p.address.val + offset.val) % _ = _
    exact Nat.mod_eq_of_lt fits
  have fitInt : (p.address.val : Int) + offset.val < 2 ^ System.Platform.numBits := by
    exact_mod_cast fits
  have run : Heap.offset Repr.u8 p offset.val s₀ = some q := by
    simp [Heap.offset, Repr.u8, lookup, live, base, len, fitInt, q, Int.toNat_add,
      Nat.le_of_lt bound]
  apply HeapWP.Spec.checkedModify.mpr
  refine ⟨⟨q, s₀, run, rfl⟩, ?_⟩
  rintro result s₁ ⟨hr, rfl⟩
  have eq := Option.some.inj (hr.symm.trans run)
  subst result
  exact ⟨rfl, addr, rfl⟩

theorem sep_shuffle (P Q R S : Assertion) (h : Fragment) :
    ((P ∗ Q) ∗ (R ∗ S)) h ↔ ((Q ∗ S) ∗ (P ∗ R)) h := by
  have assoc (A B C : Assertion) : ((A ∗ B) ∗ C) = (A ∗ (B ∗ C)) :=
    funext fun h => propext (sep_assoc A B C h)
  have comm (A B : Assertion) : (A ∗ B) = (B ∗ A) :=
    funext fun h => propext (sep_comm A B h)
  rw [assoc P Q (R ∗ S), ← assoc Q R S, comm Q R, assoc R Q S,
    ← assoc P R (Q ∗ S), comm (P ∗ R) (Q ∗ S)]

theorem preserve_two_storage (p q : RawPtr U8) (oldP newP oldQ newQ : List Aeneas.Std.Byte)
    (dp dq : Nat) (action : Result α) (post : α → Prop)
    (lenP : newP.length = oldP.length) (lenQ : newQ.length = oldQ.length)
    (body : HeapWP.Triple (bytesAt p p.address oldP dp ∗ bytesAt q q.address oldQ dq)
      action (fun result h => post result ∧
        (bytesAt p p.address newP dp ∗ bytesAt q q.address newQ dq) h)) :
    HeapWP.Triple (storageAt p oldP dp ∗ storageAt q oldQ dq)
      action (fun result h => post result ∧
        (storageAt p newP dp ∗ storageAt q newQ dq) h) := by
  have framed := HeapWP.frame
    (R := alloc Repr.u8 p p.address oldP.length false ∗
      alloc Repr.u8 q q.address oldQ.length false) body
  intro h F s₀ hp hd hm hi
  apply HeapWP.Spec.mono (framed h F s₀ ((sep_shuffle _ _ _ _ h).mp hp) hd hm hi)
  rintro result s₁ ⟨h₁, hd₁, hm₁, hi₁, a, b, hab, union, ⟨resultPost, cells⟩, cleanup⟩
  refine ⟨h₁, hd₁, hm₁, hi₁, resultPost, ?_⟩
  apply (sep_shuffle _ _ _ _ h₁).mpr
  exact ⟨a, b, hab, union, cells, by simpa [lenP, lenQ] using cleanup⟩

end scalar_mwe
