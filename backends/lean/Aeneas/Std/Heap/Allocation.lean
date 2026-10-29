module

public import Aeneas.Std.Heap.Specs
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

@[expose] public section

namespace Aeneas.Std.SepLogic

universe u

theorem matches_create_frame {s : Heap Std.Block.{u}} {F : Fragment.{u}}
    (hi : s.Inv) (hm : Fragment.Matches s F) (r : Std.Block.{u}) (own : Bool)
    (alignment : Alignment) :
    Fragment.Matches (s.createRepr r own alignment) F := by
  intro resource hr
  have hh := hm resource hr
  obtain ⟨actual, hc⟩ := hh.live
  have hlt := hi.base_lt hc
  have hne : resource.base ≠ s.next := Nat.ne_of_lt hlt
  cases resource
  · rename_i ty p value
    change p.base ≠ s.next at hne
    obtain ⟨r', hs, ha, hv⟩ := hh
    exact ⟨r', by simpa [hne] using hs, by simpa [Heap.Aligned, hne] using ha, hv⟩
  · rename_i ty base count allocated
    change base ≠ s.next at hne
    obtain ⟨ha, r', hs, halign, hn⟩ := hh
    exact ⟨by simpa [hne] using ha, r', by simpa [hne] using hs,
      by simpa [Heap.Aligned, hne] using halign, hn⟩

theorem fresh_disjoint {s : Heap Std.Block.{u}} {F : Fragment.{u}}
    (hi : s.Inv) (hm : Fragment.Matches s F)
    {h : Fragment.{u}} (hfresh : ∀ r, h r → r.base = s.next) : h.Disjoint F := by
  intro r hr other ho
  obtain ⟨repr, hc⟩ := (hm other ho).live
  have hlt := hi.base_lt hc
  left
  rw [hfresh r hr]
  exact (Nat.ne_of_lt hlt).symm

theorem newCells.spec (cs : List (Cell ty)) (own : Bool) :
    Triple emp (Heap.newCells cs own)
      (fun p => sep (alloc p cs.length own) (block p cs)) := by
  intro h F s rfl _ hm hi
  have hF : Fragment.Matches s F := by simpa using hm
  refine ⟨Heap.newCells.exists cs own s hi, fun p s' hrun => ?_⟩
  obtain ⟨_, rfl, r, hr, rfl⟩ := hrun
  let p : RawPtr ty := ⟨s.next, 0⟩
  let a := allocHeap ty s.next cs.length own
  let b := cellsHeap p cs
  have hfresh : ∀ resource, (a ∪ b) resource → resource.base = s.next := by
    rintro resource (rfl | ⟨i, hi, rfl⟩)
    · rfl
    · rfl
  refine ⟨a ∪ b, fresh_disjoint hi hF hfresh, ?_, hi.createRepr r own _,
    a, b, disjoint_alloc_cells p cs.length own cs, rfl, ⟨rfl, rfl⟩, rfl⟩
  apply (Fragment.matches_union _ _ _).mpr
  refine ⟨?_, matches_create_frame hi hF r own _⟩
  apply (Fragment.matches_union _ _ _).mpr
  constructor
  · apply (Fragment.matches_single _ _).mpr
    exact ⟨by simp, r, by simp, by simp,
      Std.Block.create_extent _ _ _ hr, Std.Block.create_bytes _ _ _ hr⟩
  · apply matches_views p cs (r := r) (by simp [p]) (by simp [p])
    intro i hi
    simpa [p] using Std.Block.create_view ty cs r hr i hi

theorem newBlock.spec (values : List ty) (own : Bool) :
    Triple emp (Heap.newBlock values own)
      (fun p => sep (alloc p values.length own) (block p (Cell.full values))) := by
  simpa [Heap.newBlock, Cell.full] using newCells.spec (Cell.full values) own

theorem alloc.spec (ty : Type u) (count : Nat) :
    Triple emp (Heap.alloc (ty := ty) count)
      (fun p => sep (alloc p count true)
        (block p (List.replicate count (.shared 0 none)))) := by
  simpa [Heap.alloc] using newCells.spec (List.replicate count ((.shared 0 none) : Cell ty)) true

theorem newSharedExposure.spec (values : List ty) :
    Triple emp (Heap.newSharedExposure values)
      (fun p => sep (alloc p values.length false) (block p (values.map (Cell.shared 1 ∘ some)))) := by
  simpa [Heap.newSharedExposure] using newCells.spec (values.map (Cell.shared 1 ∘ some)) false

theorem whole_of_matches {s : Heap Std.Block.{u}} {p : RawPtr ty} {cs : List (Cell ty)}
    {own : Bool} (hoff : p.index = 0)
    (ha : Fragment.Matches s (allocHeap ty p.base cs.length own))
    (hc : Fragment.Matches s (cellsHeap p cs)) :
    s.allocated p.base = own ∧ Heap.Whole s p cs := by
  obtain ⟨halloc, r, hs, halign, hlen, hbytes⟩ := (Fragment.matches_single _ _).mp ha
  refine ⟨halloc, r, hs, halign, hlen, ?_, hbytes⟩
  intro i hi
  obtain ⟨r', hs', _, hv⟩ := matches_cellsHeap.mp hc i hi
  have he : r' = r := Option.some.inj (hs'.symm.trans hs)
  simpa [he, hoff] using hv

theorem frame_base_absent {s : Heap Std.Block.{u}} {p : RawPtr ty} {cs : List (Cell ty)}
    {own : Bool} {F : Fragment.{u}} (hoff : p.index = 0)
    (hd : (allocHeap ty p.base cs.length own ∪ cellsHeap p cs).Disjoint F)
    (hm : Fragment.Matches s F) (hs : Heap.Whole s p cs) :
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
    obtain ⟨actual, hactual, _, hv⟩ := hh
    obtain ⟨r, hs, _, hn, _⟩ := hs
    have he : actual = r := by
      rw [hb] at hactual
      exact Option.some.inj (hactual.symm.trans hs)
    have hbound : q.index < cs.length := by
      have hvb := Std.Block.view_bound ty actual q.index value hv
      simpa [he, hn] using hvb
    have hbad := hc _ ⟨q.index, hbound, rfl⟩ _ hr
    simp [Resource.Compatible, Resource.base, Resource.ty, Resource.key, hb, hoff] at hbad
  · rcases hcompat with hne | ⟨_, hkey⟩
    · exact hne hb.symm
    · exact hkey rfl

theorem matches_remove_frame {s : Heap Std.Block.{u}} {F : Fragment.{u}} (base : BasePtr)
    (hm : Fragment.Matches s F) (hne : ∀ r, F r → r.base ≠ base) :
    Fragment.Matches (s.remove base) F := by
  intro resource hr
  have hh := hm resource hr
  have hb := hne resource hr
  cases resource
  · rename_i ty p value
    change p.base ≠ base at hb
    obtain ⟨r, hs, ha, hv⟩ := hh
    exact ⟨r, by simpa [hb] using hs, by simpa [Heap.Aligned, hb] using ha, hv⟩
  · rename_i ty other count own
    change other ≠ base at hb
    obtain ⟨ha, r, hs, halign, hn⟩ := hh
    exact ⟨by simpa [hb] using ha, r, by simpa [hb] using hs,
      by simpa [Heap.Aligned, hb] using halign, hn⟩

theorem freeBlock.spec (p : RawPtr ty) (cs : List (Cell ty)) (own : Bool)
    (hw : ∀ c ∈ cs, c.writable) :
    Triple (sep (alloc p cs.length own) (block p cs))
      (Heap.freeBlock p cs.length own) (fun _ => emp) := by
  intro h F s hp hd hm hi
  obtain ⟨a, b, _, he, ⟨hoff, ha⟩, hb⟩ := hp
  change b = cellsHeap p cs at hb
  subst h a b
  obtain ⟨hab, hF⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨ha, hc⟩ := (Fragment.matches_union _ _ _).mp hab
  obtain ⟨halloc, hs⟩ := whole_of_matches hoff ha hc
  refine ⟨⟨(), s.remove p.base, hoff, halloc, ⟨cs, hs, rfl, hw⟩, rfl⟩, ?_⟩
  rintro _ _ ⟨_, _, _, rfl⟩
  exact ⟨∅, Fragment.disjoint_empty_left F,
    by simpa using matches_remove_frame p.base hF (frame_base_absent hoff hd hF hs),
    hi.remove p.base, rfl⟩

theorem endSharedExposure.spec (p : RawPtr ty) (values : List ty) :
    Triple (sep (alloc p values.length false) (block p (values.map (Cell.shared 1 ∘ some))))
      (Heap.endSharedExposure p values) (fun _ => emp) := by
  intro h F s hp hd hm hi
  obtain ⟨a, b, _, he, ⟨hoff, ha⟩, hb⟩ := hp
  change b = cellsHeap p (values.map (Cell.shared 1 ∘ some)) at hb
  subst h a b
  obtain ⟨hab, hF⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨ha, hc⟩ := (Fragment.matches_union _ _ _).mp hab
  have ha' : Fragment.Matches s
      (allocHeap ty p.base (values.map (Cell.shared 1 ∘ some)).length false) := by simpa using ha
  obtain ⟨halloc, hs⟩ := whole_of_matches hoff ha' hc
  have hd' : (allocHeap ty p.base (values.map (Cell.shared 1 ∘ some)).length false ∪
      cellsHeap p (values.map (Cell.shared 1 ∘ some))).Disjoint F := by simpa using hd
  refine ⟨⟨(), s.remove p.base, hoff, halloc, hs, rfl⟩, ?_⟩
  rintro _ _ ⟨_, _, _, rfl⟩
  exact ⟨∅, Fragment.disjoint_empty_left F,
    by simpa using matches_remove_frame p.base hF (frame_base_absent hoff hd' hF hs),
    hi.remove p.base, rfl⟩

end Aeneas.Std.SepLogic
