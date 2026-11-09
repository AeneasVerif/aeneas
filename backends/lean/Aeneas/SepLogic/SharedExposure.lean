module

-- dropped: public import Aeneas.Std.Bytes.Notation
public import Aeneas.SepLogic.Allocation
public import Aeneas.Std.Core.Ptr
import all Aeneas.Std.Core.Ptr
public import Aeneas.SepLogic.Allocation

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.Bytes

namespace Aeneas.Std

open Aeneas.SepLogic

theorem shared_resources (repr : Aeneas.Std.Repr T) (data : Vector Aeneas.Std.Byte repr.size)
    (bptr : BasePtr) (root : Option Nat) {s s' : Heap} {p : RawPtr T}
    (hi : s.Inv) {F : Fragment} (hm : Fragment.Matches s F)
    (run : Heap.newSharedExposure repr [data] bptr root s = some (p, s')) :
    ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
      (alloc repr p p.address 1 false ∗ᵇ
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

end Aeneas.Std
