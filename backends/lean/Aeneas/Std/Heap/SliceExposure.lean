module

public import Aeneas.Std.Heap.RangeAccess
public import Aeneas.Std.Heap.SharedExposure
public import Aeneas.Std.Slice
import all Aeneas.Std.Heap.Allocation
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Slice

@[expose] public section

namespace Aeneas.Std

open SepLogic
open scoped HeapWP

set_option maxHeartbeats 1000000

private theorem exposesList_index (repr : Repr T) (s : Heap) (address : Nat)
    (values : List T) (data : List (Vector Byte repr.size))
    (exposed : State.exposesList repr s address values data) :
    ∃ (_ : data.length = values.length), ∀ i (hi : i < values.length),
      State.exposes repr s (address + i * repr.size) values[i]
        (data[i]'(by agrind)) := by
  induction values generalizing data address
  · cases data
    · simp
    · contradiction
  · rename_i value values ih
    cases data
    · contradiction
    · rename_i bytes data
      obtain ⟨head, tail⟩ := exposed
      obtain ⟨len, rest⟩ := ih (address + repr.size) data tail
      refine ⟨by simp [len], ?_⟩
      intro i hi
      cases i
      · simpa using head
      · rename_i i
        simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          rest i (by agrind)

private theorem create_range_resources (repr : Repr T)
    (data : Vector (Vector Byte repr.size) count) (depth : Nat)
    (bptr : BasePtr) (root : Option Nat) (s s₁ : Heap) (id : Nat)
    (aligned : repr.align.val ∣ bptr.val) (hi : s.Inv)
    (F : Fragment) (hm : Fragment.Matches s F)
    (created : s.createRepr
      ⟨bptr, root.getD s.next, repr.create data.toList depth, false, true, true⟩ =
        some (id, s₁)) :
    ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧
      (alloc repr ⟨id, bptr⟩ bptr count false ∗
        block repr ⟨id, bptr⟩ bptr
          (data.flatMap (fun b => b.map (Cell.shared depth))).toList) h := by
  let fresh : Block :=
    ⟨bptr, root.getD s.next, repr.create data.toList depth, false, true, true⟩
  have hs := Heap.createRepr.success created
  have hi' := Heap.createRepr_Inv s fresh id s₁ hi created
  have hl : s₁.allocations id = some fresh := by simp [hs.1, hs.2, update, fresh]
  have live : s₁.live fresh = true := by
    have hv := hi'.validBlock hl
    cases hr : s₁.allocations fresh.root
    · simp [Heap.validBlock, hr] at hv
    · simp [Heap.validBlock, Heap.live, hr, fresh] at hv ⊢
      agrind
  obtain ⟨_, post⟩ := createRepr.spec s fresh (hs.2 ▸ hi'.2) (hs.2 ▸ live)
    ∅ F rfl (Fragment.disjoint_empty_left F) (by simpa using hm) hi
  obtain ⟨h, hd, hm', hinv, _, hh⟩ := post id s₁ created
  refine ⟨h, hd, hm', hinv, allocHeap repr bptr id count false,
    cellsHeap bptr id 0 (data.flatMap (fun b => b.map (Cell.shared depth))).toList,
    ?_, ?_, ⟨rfl, rfl⟩, ?_⟩
  · rintro _ rfl _ ⟨i, hi, rfl⟩
    right
    simp [Resource.key]
  · simpa [fresh, allocHeap, Repr.create, Vector.flatMap, Vector.toList] using hh
  · exact ⟨Nat.le_refl _, aligned, by simp [RawPtr.offsetFrom]⟩

theorem shared_range_exposure.spec (repr : Repr T) (values : Vector T count)
    (s₀ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec (RawPtr.allocSharedExposure repr values.toList)
      (fun p s₁ => ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧
        (alloc repr p p.address count false ∗
          readableRange repr p p.address values 1) h) s₀ := by
  apply HeapWP.Spec.allocatingModify.mpr
  rintro p s₁ ⟨data, bptr, root, exposed, created⟩
  obtain ⟨len, each⟩ := exposesList_index repr s₀ bptr.val values.toList data exposed
  let bytes : Vector (Vector Byte repr.size) count := ⟨data.toArray, by simp [len]⟩
  have bytesList : bytes.toList = data := by simp [bytes]
  unfold Heap.newSharedExposure at created
  split at created
  · rename_i aligned
    obtain ⟨⟨id, result⟩, run, he⟩ := Option.map_eq_some_iff.mp created
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨h, hd, hm, hi, a, b, hab, hh, ha, hb⟩ :=
      create_range_resources repr bytes 1 bptr root s₀ result id aligned hi F hm
        (by simpa only [bytesList] using run)
    refine ⟨h, hd, hm, hi, a, b, hab, hh, ha, bytes, ?_, hb⟩
    intro i
    simpa [bytes] using (each i.val (by simp)).1
  · contradiction

private theorem create_range_carries (repr : Repr T) (values : Vector T count)
    (data : Vector (Vector Byte repr.size) count) (bptr : BasePtr) (root : Option Nat)
    (s s₁ : Heap) (id : Nat) (hi : s.Inv)
    (exposed : ∀ i : Fin count,
      State.exposes repr s (bptr.val + i.val * repr.size) values[i.val] data[i.val])
    (created : s.createRepr
      ⟨bptr, root.getD s.next, repr.create data.toList 0, false, true, true⟩ =
        some (id, s₁)) :
    ∀ i : Fin count, ∀ j : Fin repr.size, ∀ q lane,
      data[i.val][j.val] = .pointer q lane → repr.Carries values[i.val] q := by
  have success := Heap.createRepr.success created
  have hi' := Heap.createRepr_Inv _ _ _ _ hi created
  have fresh : s₁.allocations s.next =
      some ⟨bptr, root.getD s.next, repr.create data.toList 0, false, true, true⟩ := by
    simp [success.2, update]
  intro i j q lane byte
  have source := (exposed i).2 j
  rw [byte] at source
  rcases source with carried | ⟨other, blk, index, depth, hl, live, address, cell⟩
  · exact carried
  · have different : other ≠ s.next := Nat.ne_of_lt (hi.base_lt hl)
    have old : s₁.allocations other = some blk := by
      simpa [success.2, update, different] using hl
    have compatible := (Heap.compatible_iff _ _).mp
      (hi'.compatible fresh old (Ne.symm different))
    have active : blk.active = true := by
      simp only [Heap.live, Bool.and_eq_true] at live
      exact live.1
    have pairs := compatible.resolve_left (by simp) |>.resolve_left (by simp [active])
    have bound : i.val * repr.size + j.val < count * repr.size := by
      have := range_element_bound (start := 0) (size := repr.size)
        (r := count * repr.size) i.isLt (by simp)
      agrind
    have sizeBound : i.val * repr.size + j.val < (repr.create data.toList 0).length := by
      simpa [Repr.create] using bound
    have atByte : (repr.create data.toList 0)[i.val * repr.size + j.val] =
        Cell.shared 0 (.pointer q lane) := by
      have flat : repr.create data.toList 0 =
          (data.flatMap (fun b => b.map (Cell.shared 0))).toList := by
        simp [Repr.create, Vector.flatMap, Vector.toList]
      simp only [flat, Vector.getElem_toList, Vector.getElem_flatMap bound,
        Vector.getElem_map]
      have div : (i.val * repr.size + j.val) / repr.size = i.val := by
        rw [Nat.mul_comm i.val, Nat.mul_add_div (by agrind),
          Nat.div_eq_of_lt j.isLt, Nat.add_zero]
      simpa [div, Nat.add_mod, Nat.mod_eq_of_lt j.isLt] using
        congrArg (Cell.shared 0) byte
    have indexBound := List.getElem?_eq_some_iff.mp cell
    have conflict := pairs (i.val * repr.size + j.val) sizeBound
      index indexBound.1 (by simpa [Nat.add_assoc] using address.symm)
    simp [atByte, indexBound.2, Cell.compatible] at conflict

theorem mutable_range_exposure.spec (repr : Repr T) (values : Vector T count)
    (calibrated : ∀ value bytes, repr.decode bytes = some value →
      (∀ i : Fin repr.size, ∀ q lane,
        bytes[i.val] = .pointer q lane → repr.Carries value q) → repr.encode value bytes)
    (s₀ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec (RawPtr.allocExposure repr values.toList)
      (fun p s₁ => ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧
        (alloc repr p p.address count false ∗
          pointsToRange repr p p.address values) h) s₀ := by
  apply HeapWP.Spec.allocatingModify.mpr
  rintro p s₁ ⟨data, bptr, root, exposed, created⟩
  obtain ⟨len, each⟩ := exposesList_index repr s₀ bptr.val values.toList data exposed
  let bytes : Vector (Vector Byte repr.size) count := ⟨data.toArray, by simp [len]⟩
  have bytesList : bytes.toList = data := by simp [bytes]
  have exposed' : ∀ i : Fin count,
      State.exposes repr s₀ (bptr.val + i.val * repr.size) values[i.val] bytes[i.val] := by
    intro i
    simpa [bytes] using each i.val (by simp)
  unfold Heap.newBlock at created
  simp only [Bool.not_false, Bool.true_or, Bool.and_true] at created
  split at created
  · rename_i aligned
    obtain ⟨⟨id, result⟩, run, he⟩ := Option.map_eq_some_iff.mp created
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have run' : s₀.createRepr
        ⟨bptr, root.getD s₀.next, repr.create bytes.toList 0, false, true, true⟩ =
          some (id, result) := by simpa only [bytesList] using run
    have carries := create_range_carries repr values bytes bptr root s₀ result id hi exposed' run'
    obtain ⟨h, hd, hm, hi, a, b, hab, hh, ha, hb⟩ :=
      create_range_resources repr bytes 0 bptr root s₀ result id
        (of_decide_eq_true aligned) hi F hm run'
    exact ⟨h, hd, hm, hi, a, b, hab, hh, ha, bytes,
      fun i => calibrated _ _ (exposed' i).1 (carries i), hb⟩
  · contradiction

/- Cleanup ownership supplies liveness even when the range has no bytes. -/
theorem whole_readableRange (repr : Repr T) (p : RawPtr T) (values : Vector T count)
    (depth : Nat) (h : Fragment) (s : Heap)
    (hp : (alloc repr p p.address count false ∗
      readableRange repr p p.address values depth) h)
    (hm : Fragment.Matches s h) :
    ∃ blk, s.allocations p.provenance = some blk ∧ s.live blk = true ∧
      p.address = blk.bptr ∧ repr.align.val ∣ blk.bptr.val ∧ blk.owned = false ∧
      blk.repr.length = count * repr.size ∧
      blk.repr.all (fun cell => cell.depth == some depth) = true ∧
      h = Fragment.single (.cleanup p.provenance blk.repr.length blk.bptr blk.owned) ∪
        cellsHeap blk.bptr p.provenance 0 blk.repr := by
  obtain ⟨a, b, _, rfl, ⟨_, rfl⟩, data, _, _, ha, rfl⟩ := hp
  obtain ⟨hma, hmb⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨blk, hl, hlen, hlive, hbptr, hown⟩ := hma _ rfl
  have hrepr : blk.repr =
      (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList := by
    by_cases hz : count * repr.size = 0
    · have empty : blk.repr = [] := List.eq_nil_of_length_eq_zero (hlen.trans hz)
      simp [empty, Vector.toList_eq_nil_iff, hz]
    · obtain ⟨actual, hb, hl', _, _, selected⟩ :=
        bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
          (data := data.flatMap (fun b => b.map (Cell.shared depth)))
          (by simp only [Repr.region]; agrind) hmb
      have he : actual = blk := Option.some.inj (hl'.symm.trans hl)
      subst actual
      have hs := congrArg Vector.toList selected
      have ht : blk.repr.take (count * repr.size) = blk.repr := by
        rw [← hlen, List.take_length]
      simpa [Repr.select_toList, Block.bytes, hbptr, RawPtr.offsetFrom, RawPtr.cast,
        Repr.region, ht] using hs
  refine ⟨blk, hl, hlive, hbptr.symm, hbptr ▸ ha, hown, hlen, ?_, ?_⟩
  · have hrepr' : blk.repr =
        data.toList.flatMap (fun b => b.toList.map (Cell.shared depth)) := by
      simpa [Vector.flatMap, Vector.toList] using hrepr
    simp [hrepr', Cell.depth]
  · simp [allocHeap, hbptr, hown, hrepr, RawPtr.offsetFrom]

theorem read_whole_range (repr : Repr T) (p : RawPtr T) (values : Vector T count)
    (depth : Nat) (hsize : 0 < repr.size) (h : Fragment) (s : Heap)
    (hp : (alloc repr p p.address count false ∗ readableRange repr p p.address values depth) h)
    (hm : Fragment.Matches s h) :
    Heap.readRange repr p count s = some values.toList := by
  by_cases zero : count = 0
  · obtain ⟨blk, hl, live, addr, aligned, _, len, _, _⟩ :=
      whole_readableRange repr p values depth h s hp hm
    have empty : values.toList = [] := by simp [zero]
    simp [Heap.readRange, hl, live, addr, aligned, hsize, zero, empty]
  · obtain ⟨a, b, _, hh, _, hb⟩ := hp
    rw [hh, Fragment.matches_union] at hm
    exact read_of_readableRange (by agrind) hsize hb hm.2

theorem end_range_exposure.spec (repr : Repr T) (p : RawPtr T)
    (values : Vector T count) (depth : Nat) :
    SepLogic.Triple
      (alloc repr p p.address count false ∗ readableRange repr p p.address values depth)
      (fun s (_ : Unit) s' => Heap.endExposureAt repr p count depth s = some s')
      (fun _ => empty) := by
  intro h F s hp hd hm hi
  obtain ⟨blk, hl, live, addr, aligned, own, len, depths, whole⟩ :=
    whole_readableRange repr p values depth h s hp ((Fragment.matches_union _ _ _).mp hm).1
  have preserved := Heap.retire_Inv hi p.provenance
  have commit : Heap.commit (s.retire p.provenance) = some (s.retire p.provenance) := by
    simp [Heap.commit, preserved.2]
  have run : Heap.endExposureAt repr p count depth s = some (s.retire p.provenance) := by
    have hd : ∀ cell ∈ blk.repr, cell.depth = some depth := by
      simpa [-Cell.depth] using depths
    simp [-Cell.depth, Heap.endExposureAt, hl, live, addr, aligned, own, len, commit]
    exact hd
  obtain ⟨_, post⟩ := retire.spec s p.provenance blk hl h F whole hd hm hi
  refine ⟨⟨(), _, run⟩, ?_⟩
  intro _ s' he
  have hs : s' = s.retire p.provenance := Option.some.inj (he.symm.trans run)
  subst s'
  exact post () _ commit

theorem shared_range_end.spec (repr : Repr T) (p : RawPtr T) (values : Vector T count)
    (hsize : 0 < repr.size) :
    ⦃ alloc repr p p.address count false ∗ readableRange repr p p.address values 1 ⦄
    p.endSharedExposure repr values.toList
    ⦃ _ => empty ⦄ := by
  apply HeapWP.Triple.checkedModify
  intro h F s hp hd hm hi
  have read := read_whole_range repr p values 1 hsize h s hp
    ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨⟨_, s₁, run⟩, post⟩ := end_range_exposure.spec repr p values 1 h F s hp hd hm hi
  refine ⟨⟨(), s₁, ?_⟩, ?_⟩
  · exact ⟨by simpa using read, by simpa [Heap.endSharedExposure] using run⟩
  · rintro _ s' ⟨_, run'⟩
    apply post () s'
    simpa [Heap.endSharedExposure] using run'

theorem mutable_range_end.spec (repr : Repr T) (p : RawPtr T)
    (original : Slice T) (values : Vector T count) (hlen : original.length = count)
    (hsize : 0 < repr.size) :
    ⦃ alloc repr p p.address count false ∗ readableRange repr p p.address values 0 ⦄
    Slice.end_as_mut_ptr repr original p
    ⦃ result => fun h => result.val = values.toList ∧ empty h ⦄ := by
  intro h F s hp hd hm hi
  have read := read_whole_range repr p values 0 hsize h s hp
    ((Fragment.matches_union _ _ _).mp hm).1
  have readSpec : HeapWP.Spec (RawPtr.readRange repr p count)
      (fun x s' => x = values.toList ∧ s' = s) s := by
    apply HeapWP.Spec.checkedModify.mpr
    refine ⟨⟨values.toList, s, read, rfl⟩, ?_⟩
    rintro x s' ⟨hx, rfl⟩
    exact ⟨Option.some.inj (hx.symm.trans read), rfl⟩
  unfold Slice.end_as_mut_ptr
  simp only [hlen]
  apply HeapWP.Spec.bind readSpec
  rintro x s' ⟨hx, hs⟩
  subst x
  subst s'
  apply HeapWP.Spec.bind (HeapWP.Triple.checkedModify
    (end_range_exposure.spec repr p values 0) h F s hp hd hm hi)
  rintro _ s' ⟨h', hd', hm', hi', hemp⟩
  have length : values.toList.length ≤ Usize.max := by simp [← hlen]
  simp only [length, dite_true]
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨h', hd', hm', hi', by simp, hemp⟩

end Aeneas.Std
