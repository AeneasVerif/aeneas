module

public import Aeneas.Std.Heap.Notation
public import Aeneas.Std.Heap.Allocation
public import Aeneas.Std.Core.Ptr
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap.Allocation

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace Aeneas.Std

private theorem shared_resources (repr : Aeneas.Std.Repr T) (data : Vector Aeneas.Std.Byte repr.size)
    (bptr : BasePtr) (root : Option Nat) {s s' : Heap} {p : RawPtr T}
    (hi : s.Inv) {F : Fragment} (hm : Fragment.Matches s F)
    (run : Heap.newSharedExposure repr [data] bptr root s = some (p, s')) :
    ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
      (alloc repr p p.address 1 false ∗
        block repr p p.address (data.map (Cell.shared 1)).toList) h := by
  unfold Heap.newSharedExposure at run
  split at run
  · rename_i aligned
    obtain ⟨⟨id, result⟩, created, he⟩ := Option.map_eq_some_iff.mp run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    let fresh : Block := ⟨bptr, root.getD s.next, repr.create [data] 1, false, true, true⟩
    have hs := Heap.createRepr.success created
    have hi' := Heap.createRepr_Inv s fresh id result hi created
    have hl : result.allocations id = some fresh := by simp [hs.1, hs.2, update, fresh]
    have live : result.live fresh = true := by
      have hv := hi'.validBlock hl
      cases hr : result.allocations fresh.root
      · simp [Heap.validBlock, hr] at hv
      · simp [Heap.validBlock, Heap.live, hr, fresh] at hv ⊢
        agrind
    have valid : (Heap.mk (update s.allocations s.next (some fresh)) (s.next + 1)).check =
        true := hs.2 ▸ hi'.2
    have live' : (Heap.mk (update s.allocations s.next (some fresh)) (s.next + 1)).live fresh =
        true := hs.2 ▸ live
    obtain ⟨_, post⟩ := createRepr.spec s fresh valid live' ∅ F rfl
      (Fragment.disjoint_empty_left F) (by simpa using hm) hi
    obtain ⟨h, hd, hm', hinv, _, hh⟩ := post id result created
    refine ⟨h, hd, hm', hinv, allocHeap repr bptr id 1 false,
      cellsHeap bptr id 0 (data.map (Cell.shared 1)).toList, ?_, ?_, ⟨rfl, rfl⟩, ?_⟩
    · rintro _ rfl _ ⟨i, hi, rfl⟩
      right
      simp [Resource.key]
    · simpa [fresh, allocHeap, Repr.create, Vector.toList_map] using hh
    · exact ⟨Nat.le_refl _, aligned, by simp [RawPtr.offsetFrom]⟩
  · contradiction

theorem shared_exposure.spec (repr : Aeneas.Std.Repr T) (value : T)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F) :
    HeapWP.Spec (RawPtr.allocSharedExposure repr [value])
      (fun p s' => State.newSharedExposure repr [value] s p s' ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          (alloc repr p p.address 1 false ∗ readable repr p p.address value 1) h) s := by
  apply HeapWP.Spec.allocatingModify.mpr
  intro p s' run
  refine ⟨run, ?_⟩
  obtain ⟨data, bptr, root, exposed, created⟩ := run
  cases data
  · contradiction
  · rename_i bytes tail
    cases tail
    · obtain ⟨h, hd, hm', hi', a, b, hab, hh, ha, hb⟩ :=
        shared_resources repr bytes bptr root hi hm created
      exact ⟨h, hd, hm', hi', a, b, hab, hh, ha, bytes, exposed.1.1, hb⟩
    · simp [State.exposesList] at exposed

theorem shared_end.spec (repr : Aeneas.Std.Repr T) (p : RawPtr T) (value : T)
    (hsize : 0 < repr.size) :
    ⦃ alloc repr p p.address 1 false ∗ readable repr p p.address value 1 ⦄
    p.endSharedExposure repr [value]
    ⦃ _ => empty ⦄ := by
  apply HeapWP.Triple.checkedModify
  intro h F s hp hd hm hi
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have wholeView := hp
  obtain ⟨a, b, _, hh, _, hb⟩ := hp
  have bytesMatch : Fragment.Matches s b := by
    rw [hh, Fragment.matches_union] at localMatch
    exact localMatch.2
  have read := read_of_readable hsize hb bytesMatch
  obtain ⟨blk, hl, hlive, haddr, aligned, owned, hlen, hdepth, whole⟩ :=
    whole_readable hsize wholeView localMatch
  have preserved := Heap.retire_Inv hi p.provenance
  have commit : Heap.commit (s.retire p.provenance) = some (s.retire p.provenance) := by
    simp [Heap.commit, preserved.2]
  have run : Heap.endSharedExposure repr p 1 s = some (s.retire p.provenance) := by
    have depths : ∀ cell ∈ blk.repr, cell.depth = some 1 := by
      simpa [-Cell.depth] using hdepth
    simp [-Cell.depth, Heap.endSharedExposure, Heap.endExposureAt, hl, hlive, owned,
      haddr, aligned, hlen, commit]
    exact depths
  have readRange : Heap.readRange repr p 1 s = some [value] := by
    rw [Heap.readRange_single, read]
    rfl
  obtain ⟨_, post⟩ := retire.spec s p.provenance blk hl h F whole hd hm hi
  refine ⟨⟨(), s.retire p.provenance, readRange, run⟩, ?_⟩
  rintro _ s' ⟨_, he⟩
  have hs : s' = s.retire p.provenance := Option.some.inj (he.symm.trans run)
  subst s'
  exact post () _ commit

end Aeneas.Std
