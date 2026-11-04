module

public import RawMemoryViews.Initialization
public import Aeneas.Std.Heap.ScopedView
public import RawScale.RangeAccess
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Primitives

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_memory_views

set_option maxHeartbeats 1000000

abbrev writableBytes (p : RawPtr U8) (base : BasePtr) (bytes : Vector Aeneas.Std.Byte n) :=
  block Aeneas.Std.Repr.u8 p base (bytes.map (Cell.shared 0)).toList

/-- Pointer addition needs a live writable range, not initialized byte values. -/
theorem add_writable.spec (p : RawPtr U8) (base : BasePtr)
    (bytes : Vector Aeneas.Std.Byte n) (i : Usize) (positive : 0 < n) (bound : i.val ≤ n)
    (fits : p.address.val + i.val < 2 ^ UScalarTy.numBits .Usize) :
    ⦃ writableBytes p base bytes ⦄ RawPtr.add Aeneas.Std.Repr.u8 p i
    ⦃ (q : RawPtr U8) => fun h =>
      q.provenance = p.provenance ∧ q.address.val = p.address.val + i.val ∧
      writableBytes p base bytes h ⦄ := by
  apply HeapWP.Triple.checkedModify
  intro h F s hp hd hm hi
  have keep := hp
  obtain ⟨lower, _, cells⟩ := hp
  have matching := ((Fragment.matches_union _ _ _).mp hm).1
  rw [cells] at matching
  have size : (Aeneas.Std.Repr.u8.region n).size = n := by
    simp [Aeneas.Std.Repr.region, Aeneas.Std.Repr.u8]
  obtain ⟨blk, hb, hl, live, baseEq, _⟩ :=
    bytes_of_matches (s := s) (bptr := base)
      (repr := Aeneas.Std.Repr.u8.region n) (p := p.cast Unit)
      (data := (bytes.map (Cell.shared 0)).cast size.symm)
      (by simpa [size] using positive) matching
  simp only [size] at hb
  simp only [RawPtr.offsetFrom, RawPtr.cast] at hb
  change s.allocations p.provenance = some blk at hl
  have start : p.address.val ≤ base.val + blk.repr.length := by
    agrind
  have finish : (p.address.val : Int) + i.val ≤ base.val + blk.repr.length := by
    agrind
  have low : (base.val : Int) ≤ (p.address.val : Int) + i.val := by agrind
  have fit : (p.address.val : Int) + i.val < (2 : Int) ^ System.Platform.numBits := by
    exact_mod_cast fits
  let q : RawPtr U8 := ⟨p.provenance, ⟨BitVec.ofNat _ (p.address.val + i.val)⟩⟩
  have address : q.address.val = p.address.val + i.val := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  have run : Heap.offset Aeneas.Std.Repr.u8 p i.val s = some q := by
    have target_nat : ((p.address.val : Int) + i.val).toNat = p.address.val + i.val := by
      exact_mod_cast Int.toNat_natCast (p.address.val + i.val)
    simp [Heap.offset, Aeneas.Std.Repr.u8, hl, live, baseEq, lower, start, low, finish, fit, q,
      target_nat]
  refine ⟨⟨q, s, run, rfl⟩, ?_⟩
  rintro result s₁ ⟨run₁, rfl⟩
  have eq := Option.some.inj (run₁.symm.trans run)
  subst result
  exact ⟨h, hd, hm, hi, rfl, address, keep⟩

theorem write_byte.spec (p q : RawPtr U8) (base : BasePtr)
    (bytes : Vector Aeneas.Std.Byte n) (i : Fin n) (value : U8)
    (prov : q.provenance = p.provenance) (address : q.address.val = p.address.val + i.val) :
    ⦃ writableBytes p base bytes ⦄ MutRawPtr.write Aeneas.Std.Repr.u8 q value
    ⦃ _ => writableBytes p base (bytes.set i.val (.data value)) ⦄ := by
  intro h F s hp hd hm hi
  let cells := (bytes.map (Cell.shared 0)).toList
  have index : i.val < cells.length := by simp [cells]
  have split := block_append Aeneas.Std.Repr.u8 p q base
    (cells.take i.val) (cells.drop i.val) prov
    (by simpa [cells, List.length_take, Nat.min_eq_left (Nat.le_of_lt i.isLt)] using address)
    (by simp [Aeneas.Std.Repr.u8]) h
  rw [List.take_append_drop] at split
  obtain ⟨front, rest, apart, joined, prefixCells, restCells⟩ := split.mp hp
  have tailEq : cells.drop i.val = cells[i.val] :: cells.drop (i.val + 1) :=
    List.drop_eq_getElem_cons index
  rw [tailEq] at restCells
  let suffix : Assertion := fun h => h = cellsHeap base q.provenance
    (q.offsetFrom base + 1) (cells.drop (i.val + 1))
  obtain ⟨lower, aligned, restEq⟩ := restCells
  have singleAndSuffix : (block Aeneas.Std.Repr.u8 q base [cells[i.val]] ∗ suffix) rest := by
    refine ⟨cellsHeap base q.provenance (q.offsetFrom base) [cells[i.val]],
      cellsHeap base q.provenance (q.offsetFrom base + 1) (cells.drop (i.val + 1)),
      disjoint_cellsHeap_append _ _ _ _ _, ?_, ?_, rfl⟩
    · change rest = cellsHeap base q.provenance (q.offsetFrom base)
        ([cells[i.val]] ++ cells.drop (i.val + 1)) at restEq
      rw [cellsHeap_append] at restEq
      exact restEq
    · exact ⟨lower, aligned, rfl⟩
  have write := HeapWP.frame (R := suffix) (HeapWP.Triple.checkedModify
    (SepLogic.write.spec Aeneas.Std.Repr.u8 q base #v[bytes[i.val]] value
      (Aeneas.Std.Repr.u8_noPointers value) (by decide)))
  have single : (#v[bytes[i.val]].map (Cell.shared 0)).toList = [cells[i.val]] := by
    simp [cells]
  erw [single] at write
  have restFrame : rest.Disjoint (front ∪ F) :=
    Fragment.disjoint_union_right.mpr
      ⟨apart.symm, (Fragment.disjoint_union_left.mp (joined ▸ hd)).2⟩
  have restMatch : Fragment.Matches s (rest ∪ (front ∪ F)) := by
    simp only [joined, Fragment.matches_union] at hm ⊢
    tauto
  apply HeapWP.Spec.mono (write rest (front ∪ F) s singleAndSuffix restFrame restMatch hi)
  rintro _ s₁ ⟨rest₁, disjoint, matching, inv, a, b, _, rfl, point, rfl⟩
  obtain ⟨data, encoded, _, _, eq⟩ := point
  have dataEq : data = #v[Aeneas.Std.Byte.data value] := encoded
  subst data
  let cells₁ := ((bytes.set i.val (.data value)).map (Cell.shared 0)).toList
  have finalCells : cells₁ = cells.take i.val ++ [.shared 0 (.data value)] ++ cells.drop (i.val + 1) := by
    simp only [cells₁, cells, Vector.map_set, Vector.toList_set]
    rw [List.set_eq_take_append_cons_drop]
    simp
  have offset : q.offsetFrom base = p.offsetFrom base + i.val := by
    obtain ⟨lower₀, _, _⟩ := hp
    simp only [RawPtr.offsetFrom]
    agrind
  have full : front ∪ (a ∪ cellsHeap base q.provenance
      (q.offsetFrom base + 1) (cells.drop (i.val + 1))) =
      cellsHeap base p.provenance (p.offsetFrom base) cells₁ := by
    have singleton : (Vector.map (Cell.shared 0) #v[Aeneas.Std.Byte.data value]).toList =
        [.shared 0 (.data value)] := by
      rw [Vector.toList_map]
      rfl
    erw [singleton] at eq
    rw [finalCells, cellsHeap_append, cellsHeap_append, prefixCells.2.2, eq]
    simp [cells, prov, offset, Fragment.union_assoc, Nat.add_assoc]
  refine ⟨_, ?_, ?_, inv, hp.1, hp.2.1, full⟩
  · apply Fragment.disjoint_union_left.mpr
    exact ⟨(Fragment.disjoint_union_left.mp (joined ▸ hd)).1,
      (Fragment.disjoint_union_right.mp disjoint).2⟩
  · simp only [Fragment.matches_union] at matching ⊢
    tauto

/- Descriptor arguments are the only change to the emitted Rust loop. -/
def fill_raw_loop (bytes : MutRawPtr U8) (length : Usize) (value : U8) (i : Usize) :
    Result Unit := do
  if i < length then
    let p ← RawPtr.add Aeneas.Std.Repr.u8 bytes i
    MutRawPtr.write Aeneas.Std.Repr.u8 p value
    let next ← i + 1#usize
    fill_raw_loop bytes length value next
  else pure ()
partial_fixpoint

def fill_raw (bytes : MutRawPtr U8) (length : Usize) (value : U8) : Result Unit :=
  fill_raw_loop bytes length value 0#usize

def filledFrom (bytes : Vector Aeneas.Std.Byte n) (value : U8) (start : Nat) :
    Vector Aeneas.Std.Byte n :=
  Vector.ofFn fun j => if start ≤ j.val then .data value else bytes[j.val]

theorem filledFrom_step (bytes : Vector Aeneas.Std.Byte n) (value : U8) (i : Fin n) :
    filledFrom (bytes.set i.val (.data value)) value (i.val + 1) = filledFrom bytes value i.val := by
  apply Vector.ext
  intro j hj
  simp only [filledFrom, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases eq : j = i.val
  · simp [eq]
  · have boundary : (i.val + 1 ≤ j) = (i.val ≤ j) := by agrind
    simp [Ne.symm eq, boundary]

/-- Each byte is written without reading its old representation. All other
    views and the fresh-ID counter remain unchanged throughout the loop. -/
theorem fill_raw_loop.spec (p : RawPtr U8) (length : Usize) (value : U8) (i : Usize)
    (base : BasePtr) (bytes : Vector Aeneas.Std.Byte length.val)
    (bound : i.val ≤ length.val)
    (fits : ∀ j, j < length.val → p.address.val + j < 2 ^ UScalarTy.numBits .Usize)
    (h F : Fragment) (s₀ : Heap) (hp : writableBytes p base bytes h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s₀ (h ∪ F)) (hi : s₀.Inv) :
    HeapWP.Spec (fill_raw_loop p length value i)
      (fun _ s₁ => Heap.StableExcept p.provenance s₀ s₁ ∧
        ∃ h₁, h₁.Disjoint F ∧ Fragment.Matches s₁ (h₁ ∪ F) ∧ s₁.Inv ∧
          writableBytes p base (filledFrom bytes value i.val) h₁) s₀ := by
  unfold fill_raw_loop
  by_cases more : i.val < length.val
  · have comparison : i < length := by simpa using more
    rw [ite_eq_left comparison]
    have add := add_writable.spec p base bytes i (by agrind) (by agrind) (fits i.val more)
      h F s₀ hp hd hm hi
    obtain ⟨enabled, post⟩ := HeapWP.Spec.checkedModify.mp add
    have add' := HeapWP.Spec.checkedModify.mpr
      ⟨enabled, fun q s₁ run => And.intro run.2 (post q s₁ run)⟩
    apply HeapWP.Spec.bind add'
    rintro q s₁ ⟨same, h₁, hd₁, hm₁, hi₁, prov, address, hp₁⟩
    subst s₁
    have write := write_byte.spec p q base bytes ⟨i.val, more⟩ value prov address
      h₁ F s₀ hp₁ hd₁ hm₁ hi₁
    obtain ⟨enabled, post⟩ := HeapWP.Spec.checkedModify.mp write
    have write' := HeapWP.Spec.checkedModify.mpr
      ⟨enabled, fun result s₂ run => And.intro
        (show Heap.StableExcept p.provenance s₀ s₂ from by
          obtain ⟨data, _, written⟩ := run
          rw [← prov]
          exact Heap.modify_stable written)
        (post result s₂ run)⟩
    apply HeapWP.Spec.bind write'
    rintro _ s₂ ⟨stable, h₂, hd₂, hm₂, hi₂, hp₂⟩
    have increment : i + 1#usize ⦃ (next : Usize) => next.val = i.val + 1 ⦄ := by
      step*
    apply HeapWP.Spec.bind (HeapWP.Spec.of_spec increment s₂)
    rintro next s₃ ⟨nextEq, same⟩
    subst s₃
    have loop := fill_raw_loop.spec p length value next base (bytes.set i.val (.data value))
      (by agrind) fits h₂ F s₂ hp₂ hd₂ hm₂ hi₂
    apply HeapWP.Spec.mono loop
    rintro _ s₃ ⟨stable₁, h₃, hd₃, hm₃, hi₃, hp₃⟩
    rw [nextEq, filledFrom_step bytes value ⟨i.val, more⟩] at hp₃
    exact ⟨stable.trans stable₁, h₃, hd₃, hm₃, hi₃, hp₃⟩
  · have comparison : ¬ i < length := by simpa using more
    rw [ite_eq_right comparison]
    have done : filledFrom bytes value i.val = bytes := by
      apply Vector.ext
      intro j hj
      have before : ¬ i.val ≤ j := by agrind
      simp [filledFrom, before]
    exact (HeapWP.Spec.pure _ _ _).mpr
      ⟨⟨rfl, fun _ _ => rfl⟩, h, hd, hm, hi, by simpa only [done] using hp⟩
termination_by length.val - i.val
decreasing_by agrind

theorem fill_raw.spec (p : RawPtr U8) (length : Usize) (value : U8)
    (base : BasePtr) (bytes : Vector Aeneas.Std.Byte length.val)
    (fits : ∀ j, j < length.val → p.address.val + j < 2 ^ UScalarTy.numBits .Usize) :
    ⦃ writableBytes p base bytes ⦄ fill_raw p length value
    ⦃ _ => writableBytes p base (Vector.replicate length.val (.data value)) ⦄ := by
  intro h F s hp hd hm hi
  apply HeapWP.Spec.mono (fill_raw_loop.spec p length value 0#usize base bytes
    (by simp) fits h F s hp hd hm hi)
  rintro _ s₁ ⟨_, h₁, hd₁, hm₁, hi₁, hp₁⟩
  have zero : filledFrom bytes value (0#usize).val = Vector.replicate length.val (.data value) := by
    apply Vector.ext
    intro j hj
    simp [filledFrom]
  exact ⟨h₁, hd₁, hm₁, hi₁, zero ▸ hp₁⟩

end raw_memory_views
