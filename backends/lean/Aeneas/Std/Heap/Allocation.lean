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
  obtain ⟨cs, hc⟩ := hh.live
  have hlt := hi.base_lt hc
  have hne : resource.base ≠ s.next := Nat.ne_of_lt hlt
  cases resource
  · rename_i ty p value
    obtain ⟨actual, ha, hv⟩ := hh
    exact ⟨actual, (Heap.load_createRepr_other _ _ _ _ _ _ hne).trans ha, hv⟩
  · rename_i ty base count allocated
    change base ≠ s.next at hne
    obtain ⟨ha, actual, hs, hn⟩ := hh
    exact ⟨by simpa [Heap.createRepr, update, hne] using ha,
      actual, (Heap.load_createRepr_other _ _ _ _ _ _ hne).trans hs, hn⟩

theorem fresh_disjoint {s : Heap m.Repr} {F : Fragment.{u}}
    (hi : s.Inv) (hm : Fragment.Matches m s F)
    {h : Fragment.{u}} (hfresh : ∀ r, h r → r.base = s.next) : h.Disjoint F := by
  intro r hr other ho
  obtain ⟨cs, hc⟩ := (hm other ho).live
  have hlt := hi.base_lt hc
  left
  rw [hfresh r hr]
  exact (Nat.ne_of_lt hlt).symm

theorem triple_create (ty : Type u) (cs : List (Cell ty)) (own : Bool)
    (op : Cmd m (RawPtr ty))
    (hsafe : ∀ s, s.Inv → ∃ p s', op s p s')
    (hpost : ∀ s p s', op s p s' → p = ⟨s.next, 0⟩ ∧
      ∃ r, m.interpret ty r = some cs ∧ s' = s.createRepr r own) :
    Triple m emp op (fun p => sep (alloc p cs.length own) (block p cs)) := by
  intro h F s rfl hd hm hi
  have hF : Fragment.Matches m s F := by simpa using hm
  refine ⟨hsafe s hi, fun p s' hrun => ?_⟩
  obtain ⟨rfl, r, hr, rfl⟩ := hpost s p s' hrun
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
    exact ⟨by simp [Heap.createRepr, update],
      cs, by simpa using hr, rfl⟩
  · exact matches_segment p [] cs [] rfl (by simpa [p] using hr)

theorem newBlock.spec (values : List ty) (own : Bool) :
    Triple m emp (Heap.newBlock m values own)
      (fun p => sep (alloc p values.length own) (block p (Cell.full values))) := by
  have ht := triple_create ty (Cell.full values) own (Heap.newBlock m values own)
    (fun s hi => ⟨⟨s.next, 0⟩, s.create m (Cell.full values) own, hi, rfl, rfl⟩)
    (fun _ _ _ h => ⟨h.2.1, _, m.roundTrip ty (Cell.full values), h.2.2⟩)
  simpa [Cell.full] using ht

theorem alloc.spec (ty : Type u) (count : Nat) :
    Triple m emp (Heap.alloc m (ty := ty) count)
      (fun p => sep (alloc p count true)
        (block p (List.replicate count .uninitialized))) := by
  have ht := triple_create ty (List.replicate count .uninitialized) true (Heap.alloc m count)
    (fun s hi => Heap.alloc.exists m ty count s hi)
    (fun _ _ _ h => by
      obtain ⟨_, hp, r, _, hr, hs⟩ := h
      exact ⟨hp, r, hr, hs⟩)
  simpa using ht

theorem newSharedView.spec (values : List ty) :
    Triple m emp (Heap.newSharedView m values)
      (fun p => sep (alloc p values.length false) (block p (Cell.shared 1 values))) := by
  have ht := triple_create ty (Cell.shared 1 values) false (Heap.newSharedView m values)
    (fun s hi => ⟨⟨s.next, 0⟩, s.create m (Cell.shared 1 values) false, hi, rfl, rfl⟩)
    (fun _ _ _ h => ⟨h.2.1, _, m.roundTrip ty (Cell.shared 1 values), h.2.2⟩)
  simpa [Cell.shared] using ht

theorem whole_of_matches {s : Heap m.Repr} {p : RawPtr ty} {cs : List (Cell ty)}
    {own : Bool} (hoff : p.offset = 0)
    (ha : Fragment.Matches m s (allocHeap ty p.base cs.length own))
    (hc : Fragment.Matches m s (cellsHeap p cs)) :
    s.allocated p.base = own ∧ s.load m.interpret ty p.base = some cs := by
  obtain ⟨halloc, actual, hs, hlen⟩ := (Fragment.matches_single _ _ _).mp ha
  have he := segment_unique hc hlen.symm (before := []) (after := []) hoff.symm
    (by simpa using hs)
  exact ⟨halloc, by simpa [he] using hs⟩

theorem frame_base_absent {s : Heap m.Repr} {p : RawPtr ty} {cs : List (Cell ty)}
    {own : Bool} {F : Fragment.{u}} (hoff : p.offset = 0)
    (hd : (allocHeap ty p.base cs.length own ∪ cellsHeap p cs).Disjoint F)
    (hm : Fragment.Matches m s F)
    (hs : s.load m.interpret ty p.base = some cs) :
    ∀ r, F r → r.base ≠ p.base := by
  intro r hr hb
  obtain ⟨ha, hc⟩ := Fragment.disjoint_union_left.mp hd
  have hcompat := ha _ rfl r hr
  have ht : ty = r.ty := by
    rcases hcompat with hne | ⟨ht, _⟩
    · exact (hne hb.symm).elim
    · exact ht
  have hh := hm r hr
  cases r
  · rename_i otherTy q value
    change ty = otherTy at ht
    subst otherTy
    change q.base = p.base at hb
    obtain ⟨actual, hactual, hv⟩ := hh
    have he : actual = cs := by
      rw [hb] at hactual
      exact Option.some.inj (hactual.symm.trans hs)
    have hbound : q.offset < cs.length :=
      he ▸ (List.getElem?_eq_some_iff.mp hv).1
    have hbad := hc _ ⟨q.offset, hbound, rfl⟩ _ hr
    simp [Resource.Compatible, Resource.base, Resource.ty, Resource.key, hb, hoff] at hbad
  · rcases hcompat with hne | ⟨_, hkey⟩
    · exact hne hb.symm
    · exact hkey rfl

theorem matches_remove_frame {s : Heap m.Repr} {F : Fragment.{u}} (base : BasePtr)
    (hm : Fragment.Matches m s F) (hne : ∀ r, F r → r.base ≠ base) :
    Fragment.Matches m (s.remove base) F := by
  intro r hr
  have hh := hm r hr
  have hb := hne r hr
  cases r
  · rename_i ty p value
    obtain ⟨actual, ha, hv⟩ := hh
    exact ⟨actual, (Heap.load_remove_other _ _ _ _ _ hb).trans ha, hv⟩
  · rename_i ty other count own
    change other ≠ base at hb
    obtain ⟨ha, actual, hs, hn⟩ := hh
    exact ⟨by simpa [Heap.remove, update, hb] using ha,
      actual, (Heap.load_remove_other _ _ _ _ _ hb).trans hs, hn⟩

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
  have hcan : Heap.freeBlock m p cs.length own s () (s.remove p.base) :=
    ⟨hoff, halloc, ⟨cs, hs, rfl, hw⟩, rfl⟩
  refine ⟨⟨(), _, hcan⟩, ?_⟩
  rintro _ _ ⟨_, _, _, rfl⟩
  exact ⟨∅, Fragment.disjoint_empty_left F,
    by simpa using matches_remove_frame p.base hF (frame_base_absent hoff hd hF hs),
    hi.remove p.base, rfl⟩

end Aeneas.Std.SepLogic
