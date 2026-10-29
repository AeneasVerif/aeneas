module

public import Aeneas.Std.Heap.Specs
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

@[expose] public section

namespace Aeneas.Std.SepLogic

universe u

variable {m : Layout.{u}}

theorem matches_create_frame {s : Heap m.Repr} {F : Fragment.{u}}
    (hi : s.Inv) (hm : Fragment.Matches m s F) (r : m.Repr) (own : Bool) :
    Fragment.Matches m (s.createRepr r own) F := by
  intro resource hr
  have hh := hm resource hr
  obtain ⟨actual, hc⟩ := hh.live
  have hlt := hi.base_lt hc
  have hne : resource.base ≠ s.next := Nat.ne_of_lt hlt
  cases resource
  · rename_i ty p value
    change p.base ≠ s.next at hne
    obtain ⟨r', hs, hv⟩ := hh
    exact ⟨r', by simpa [Heap.createRepr, update, hne] using hs, hv⟩
  · rename_i ty base count allocated
    change base ≠ s.next at hne
    obtain ⟨ha, r', hs, hn⟩ := hh
    exact ⟨by simpa [Heap.createRepr, update, hne] using ha,
      r', by simpa [Heap.createRepr, update, hne] using hs, hn⟩

theorem fresh_disjoint {s : Heap m.Repr} {F : Fragment.{u}}
    (hi : s.Inv) (hm : Fragment.Matches m s F)
    {h : Fragment.{u}} (hfresh : ∀ r, h r → r.base = s.next) : h.Disjoint F := by
  intro r hr other ho
  obtain ⟨repr, hc⟩ := (hm other ho).live
  have hlt := hi.base_lt hc
  left
  rw [hfresh r hr]
  exact (Nat.ne_of_lt hlt).symm

theorem newCells.spec (cs : List (Cell ty)) (own : Bool) :
    Triple m emp (Heap.newCells m cs own)
      (fun p => sep (alloc p cs.length own) (block p cs)) := by
  intro h F s rfl _ hm hi
  have hF : Fragment.Matches m s F := by simpa using hm
  refine ⟨Heap.newCells.exists cs own s hi, fun p s' hrun => ?_⟩
  obtain ⟨_, rfl, r, hr, rfl⟩ := hrun
  let p : RawPtr ty := ⟨s.next, 0⟩
  let a := allocHeap ty s.next cs.length own
  let b := cellsHeap p cs
  have hfresh : ∀ resource, (a ∪ b) resource → resource.base = s.next := by
    rintro resource (rfl | ⟨i, hi, rfl⟩)
    · rfl
    · rfl
  refine ⟨a ∪ b, fresh_disjoint hi hF hfresh, ?_, hi.createRepr r own,
    a, b, disjoint_alloc_cells p cs.length own cs, rfl, ⟨rfl, rfl⟩, rfl⟩
  apply (Fragment.matches_union _ _ _ _).mpr
  refine ⟨?_, matches_create_frame hi hF r own⟩
  apply (Fragment.matches_union _ _ _ _).mpr
  constructor
  · apply (Fragment.matches_single _ _ _).mpr
    exact ⟨by simp [Heap.createRepr, update], r, by simp [Heap.createRepr, update],
      m.create_extent _ _ _ hr, m.create_bytes _ _ _ hr⟩
  · apply matches_views p cs (r := r) (by simp [Heap.createRepr, update, p])
    intro i hi
    simpa [p] using m.create_view ty cs r hr i hi

theorem newBlock.spec (values : List ty) (own : Bool) :
    Triple m emp (Heap.newBlock m values own)
      (fun p => sep (alloc p values.length own) (block p (Cell.full values))) := by
  simpa [Heap.newBlock, Cell.full] using newCells.spec (m := m) (Cell.full values) own

theorem alloc.spec (ty : Type u) (count : Nat) :
    Triple m emp (Heap.alloc m (ty := ty) count)
      (fun p => sep (alloc p count true)
        (block p (List.replicate count .uninitialized))) := by
  simpa [Heap.alloc] using newCells.spec (m := m)
    (List.replicate count (.uninitialized : Cell ty)) true

theorem newSharedExposure.spec (values : List ty) :
    Triple m emp (Heap.newSharedExposure m values)
      (fun p => sep (alloc p values.length false) (block p (values.map (Cell.shared 1)))) := by
  simpa [Heap.newSharedExposure] using newCells.spec (m := m) (values.map (Cell.shared 1)) false

theorem whole_of_matches {s : Heap m.Repr} {p : RawPtr ty} {cs : List (Cell ty)}
    {own : Bool} (hoff : p.index = 0)
    (ha : Fragment.Matches m s (allocHeap ty p.base cs.length own))
    (hc : Fragment.Matches m s (cellsHeap p cs)) :
    s.allocated p.base = own ∧ Heap.Whole m s p cs := by
  obtain ⟨halloc, r, hs, hlen, hbytes⟩ := (Fragment.matches_single _ _ _).mp ha
  refine ⟨halloc, r, hs, hlen, ?_, hbytes⟩
  intro i hi
  obtain ⟨r', hs', hv⟩ := matches_cellsHeap.mp hc i hi
  have he : r' = r := Option.some.inj (hs'.symm.trans hs)
  simpa [he, hoff] using hv

theorem frame_base_absent {s : Heap m.Repr} {p : RawPtr ty} {cs : List (Cell ty)}
    {own : Bool} {F : Fragment.{u}} (hoff : p.index = 0)
    (hd : (allocHeap ty p.base cs.length own ∪ cellsHeap p cs).Disjoint F)
    (hm : Fragment.Matches m s F) (hs : Heap.Whole m s p cs) :
    ∀ r, F r → r.base ≠ p.base := by
  intro resource hr hb
  obtain ⟨ha, hc⟩ := Fragment.disjoint_union_left.mp hd
  have hcompat := ha _ rfl resource hr
  have ht : ty = resource.ty := by
    rcases hcompat with hne | ⟨ht, _⟩
    · exact (hne hb.symm).elim
    · exact ht
  have hh := hm resource hr
  cases resource
  · rename_i otherTy q value
    change ty = otherTy at ht
    subst otherTy
    change q.base = p.base at hb
    obtain ⟨actual, hactual, hv⟩ := hh
    obtain ⟨r, hs, hn, _⟩ := hs
    have he : actual = r := by
      rw [hb] at hactual
      exact Option.some.inj (hactual.symm.trans hs)
    have hbound : q.index < cs.length := by
      have hvb := m.view_bound ty actual q.index value hv
      simpa [he, hn] using hvb
    have hbad := hc _ ⟨q.index, hbound, rfl⟩ _ hr
    simp [Resource.Compatible, Resource.base, Resource.ty, Resource.key, hb, hoff] at hbad
  · rcases hcompat with hne | ⟨_, hkey⟩
    · exact hne hb.symm
    · exact hkey rfl

theorem matches_remove_frame {s : Heap m.Repr} {F : Fragment.{u}} (base : BasePtr)
    (hm : Fragment.Matches m s F) (hne : ∀ r, F r → r.base ≠ base) :
    Fragment.Matches m (s.remove base) F := by
  intro resource hr
  have hh := hm resource hr
  have hb := hne resource hr
  cases resource
  · rename_i ty p value
    change p.base ≠ base at hb
    obtain ⟨r, hs, hv⟩ := hh
    exact ⟨r, by simpa [Heap.remove, update, hb] using hs, hv⟩
  · rename_i ty other count own
    change other ≠ base at hb
    obtain ⟨ha, r, hs, hn⟩ := hh
    exact ⟨by simpa [Heap.remove, update, hb] using ha,
      r, by simpa [Heap.remove, update, hb] using hs, hn⟩

theorem freeBlock.spec (p : RawPtr ty) (cs : List (Cell ty)) (own : Bool)
    (hw : ∀ c ∈ cs, c.writable) :
    Triple m (sep (alloc p cs.length own) (block p cs))
      (Heap.freeBlock m p cs.length own) (fun _ => emp) := by
  intro h F s hp hd hm hi
  obtain ⟨a, b, _, he, ⟨hoff, ha⟩, hb⟩ := hp
  change b = cellsHeap p cs at hb
  subst h a b
  obtain ⟨hab, hF⟩ := (Fragment.matches_union _ _ _ _).mp hm
  obtain ⟨ha, hc⟩ := (Fragment.matches_union _ _ _ _).mp hab
  obtain ⟨halloc, hs⟩ := whole_of_matches hoff ha hc
  refine ⟨⟨(), s.remove p.base, hoff, halloc, ⟨cs, hs, rfl, hw⟩, rfl⟩, ?_⟩
  rintro _ _ ⟨_, _, _, rfl⟩
  exact ⟨∅, Fragment.disjoint_empty_left F,
    by simpa using matches_remove_frame p.base hF (frame_base_absent hoff hd hF hs),
    hi.remove p.base, rfl⟩

theorem endSharedExposure.spec (p : RawPtr ty) (values : List ty) :
    Triple m (sep (alloc p values.length false) (block p (values.map (Cell.shared 1))))
      (Heap.endSharedExposure m p values) (fun _ => emp) := by
  intro h F s hp hd hm hi
  obtain ⟨a, b, _, he, ⟨hoff, ha⟩, hb⟩ := hp
  change b = cellsHeap p (values.map (Cell.shared 1)) at hb
  subst h a b
  obtain ⟨hab, hF⟩ := (Fragment.matches_union _ _ _ _).mp hm
  obtain ⟨ha, hc⟩ := (Fragment.matches_union _ _ _ _).mp hab
  have ha' : Fragment.Matches m s
      (allocHeap ty p.base (values.map (Cell.shared 1)).length false) := by simpa using ha
  obtain ⟨halloc, hs⟩ := whole_of_matches hoff ha' hc
  have hd' : (allocHeap ty p.base (values.map (Cell.shared 1)).length false ∪
      cellsHeap p (values.map (Cell.shared 1))).Disjoint F := by simpa using hd
  refine ⟨⟨(), s.remove p.base, hoff, halloc, hs, rfl⟩, ?_⟩
  rintro _ _ ⟨_, _, _, rfl⟩
  exact ⟨∅, Fragment.disjoint_empty_left F,
    by simpa using matches_remove_frame p.base hF (frame_base_absent hoff hd' hF hs),
    hi.remove p.base, rfl⟩

end Aeneas.Std.SepLogic
