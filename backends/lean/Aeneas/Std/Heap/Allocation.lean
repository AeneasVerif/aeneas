module

public import Aeneas.Std.Heap.Specs
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

/-! Checked allocation, freshness, and framed cleanup. Allocation needs capacity
in the input heap; there is deliberately no unconditional allocation triple
from `emp`. -/

@[expose] public section

namespace Aeneas.Std

namespace Heap

theorem createRepr.enabled (s : Heap) (block : Block)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize)
    (hl : block.repr.length < 2 ^ UScalarTy.numBits .Usize)
    (hf : s.allocations s.next = none) :
    ∃ base s', s.createRepr block = some (base, s') := by
  exact ⟨s.next, ⟨update s.allocations s.next (some block),
    ⟨BitVec.ofNat _ (s.next.val + 1)⟩⟩, by simp [createRepr, hc, hl, hf]⟩

theorem createRepr.success {s s' : Heap} {block : Block} {base : BasePtr}
    (h : s.createRepr block = some (base, s')) :
    base = s.next ∧ s.allocations s.next = none ∧
      s'.allocations = update s.allocations s.next (some block) ∧
      s'.next.val = s.next.val + 1 := by
  unfold createRepr at h
  split at h
  · rename_i hc
    split at h
    · rename_i hf
      have he := Option.some.inj h
      cases he
      refine ⟨rfl, hf, rfl, ?_⟩
      exact Nat.mod_eq_of_lt hc.1
    · cases h
  · cases h

theorem createRepr.inv {s s' : Heap} {block : Block} {base : BasePtr}
    (hi : s.Inv) (h : s.createRepr block = some (base, s')) : s'.Inv := by
  obtain ⟨_, _, ha, hn⟩ := createRepr.success h
  intro other ho
  have hne : other ≠ s.next := by
    intro he
    rw [he, hn] at ho
    grind
  rw [ha]
  simp only [update, ite_eq_right hne]
  apply hi other
  rw [hn] at ho
  grind

theorem newBlock.enabled (repr : Repr ty) (data : List (Vector U8 repr.size))
    (own : Bool) (s : Heap) (hi : s.Inv)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize)
    (hl : data.length * repr.size < 2 ^ UScalarTy.numBits .Usize) :
    ∃ p s', newBlock repr data own s = some (p, s') := by
  obtain ⟨base, s', hs⟩ := createRepr.enabled s
    ⟨(repr.create (data.toArray.toVector.map (Cell.shared 0 ∘ some))).toList, repr.align, own⟩
    hc (by simpa only [Vector.length_toList, List.size_toArray] using hl) (hi s.next (Nat.le_refl _))
  exact ⟨⟨base, ⟨0⟩⟩, s', by simp only [newBlock, hs]⟩

theorem newBlock.inv {repr : Repr ty} {data : List (Vector U8 repr.size)}
    {own : Bool} {s s' : Heap} {p : RawPtr ty}
    (hi : s.Inv) (h : newBlock repr data own s = some (p, s')) : s'.Inv := by
  unfold newBlock at h
  split at h
  · rename_i base actual hs
    have he := Option.some.inj h
    cases he
    exact createRepr.inv hi hs
  · cases h

end Heap

namespace SepLogic

theorem matches_create_frame {s s' : Heap} {F : Fragment} {block : Block} {base : BasePtr}
    (hi : s.Inv) (hm : Fragment.Matches s F) (h : s.createRepr block = some (base, s')) :
    Fragment.Matches s' F := by
  obtain ⟨_, _, ha, _⟩ := Heap.createRepr.success h
  intro resource hr
  have hh := hm resource hr
  obtain ⟨actual, hl⟩ := hh.live
  have hne : resource.base ≠ s.next := by
    intro he
    have hn := hi s.next (Nat.le_refl _)
    rw [he, hn] at hl
    cases hl
  cases resource
  · rename_i other index alignment value
    obtain ⟨actual, hl, halign, hv⟩ := hh
    change other ≠ s.next at hne
    exact ⟨actual, by simpa [ha, update, hne] using hl, halign, hv⟩
  · rename_i other size alignment own
    obtain ⟨actual, hl, hn, halign, ho⟩ := hh
    change other ≠ s.next at hne
    exact ⟨actual, by simpa [ha, update, hne] using hl, hn, halign, ho⟩

theorem fresh_disjoint {s : Heap} {F h : Fragment}
    (hi : s.Inv) (hm : Fragment.Matches s F)
    (hfresh : ∀ r, h r → r.base = s.next) : h.Disjoint F := by
  intro r hr other ho
  obtain ⟨actual, hl⟩ := (hm other ho).live
  have hlt := hi.base_lt hl
  left
  intro he
  have hval := congrArg UScalar.val (he ▸ hfresh r hr)
  grind

theorem newBlock_single.resources {repr : Repr ty} {data : Vector U8 repr.size}
    {own : Bool} {s s' : Heap} {p : RawPtr ty}
    (h : Heap.newBlock repr [data] own s = some (p, s')) :
    p.base = s.next ∧ p.byteOffset.val = 0 ∧ s'.next.val = s.next.val + 1 ∧
      Fragment.Matches s'
        (allocHeap repr p.base 1 own ∪
          cellsHeap repr.align p.base 0 (data.map (Cell.shared 0 ∘ some)).toList) := by
  unfold Heap.newBlock at h
  split at h
  · rename_i base actual hs
    have he := Option.some.inj h
    cases he
    obtain ⟨hbase, _, ha, hn⟩ := Heap.createRepr.success hs
    subst base
    have hb : (repr.create ([data].toArray.toVector.map (Cell.shared 0 ∘ some))).toList =
        (data.map (Cell.shared 0 ∘ some)).toList := by
      simpa using Repr.create_single repr data 0
    let blk : Block :=
      ⟨(repr.create ([data].toArray.toVector.map (Cell.shared 0 ∘ some))).toList, repr.align, own⟩
    have hlookup : s'.allocations s.next = some blk := by simp [ha, update, blk]
    refine ⟨rfl, rfl, hn, (Fragment.matches_union _ _ _).mpr ⟨?_, ?_⟩⟩
    · apply (Fragment.matches_single _ _).mpr
      refine ⟨blk, hlookup, ?_, rfl, rfl⟩
      simp only [blk, Vector.length_toList, List.size_toArray, List.length_cons, List.length_nil]
    · rw [matches_cellsHeap]
      intro i hi
      exact ⟨blk, hlookup, Nat.dvd_refl _,
        by simpa only [blk, hb, Nat.zero_add] using List.getElem?_eq_getElem hi⟩
  · cases h

theorem newBlock_single.frame {repr : Repr ty} {data : Vector U8 repr.size}
    {own : Bool} {s s' : Heap} {p : RawPtr ty} {F : Fragment}
    (hi : s.Inv) (hm : Fragment.Matches s F)
    (h : Heap.newBlock repr [data] own s = some (p, s')) :
    Fragment.Matches s' F := by
  unfold Heap.newBlock at h
  split at h
  · rename_i base actual hs
    have he := Option.some.inj h
    cases he
    exact matches_create_frame hi hm hs
  · cases h

theorem matches_remove_frame {s : Heap} {F : Fragment} (base : BasePtr)
    (hm : Fragment.Matches s F) (hne : ∀ r, F r → r.base ≠ base) :
    Fragment.Matches (s.remove base) F := by
  intro resource hr
  have hh := hm resource hr
  have hb := hne resource hr
  cases resource
  · rename_i other index alignment value
    obtain ⟨actual, hl, ha, hv⟩ := hh
    change other ≠ base at hb
    exact ⟨actual, by simpa [hb] using hl, ha, hv⟩
  · rename_i other size alignment own
    obtain ⟨actual, hl, hn, ha, ho⟩ := hh
    change other ≠ base at hb
    exact ⟨actual, by simpa [hb] using hl, hn, ha, ho⟩

theorem whole_of_matches {s : Heap} {repr : Repr ty} {p : RawPtr ty}
    {cells : List (Cell U8)} {count : Nat} {own : Bool}
    (hoff : p.byteOffset.val = 0) (hlen : cells.length = count * repr.size)
    (ha : Fragment.Matches s (allocHeap repr p.base count own))
    (hc : Fragment.Matches s (cellsHeap repr.align p.base (p.byteOffset.val) cells)) :
    ∃ block, s.allocations p.base = some block ∧ block.repr = cells ∧
      block.alignment = repr.align ∧ block.owned = own := by
  obtain ⟨block, hl, hn, halign, ho⟩ := (Fragment.matches_single _ _).mp ha
  refine ⟨block, hl, ?_, halign, ho⟩
  apply List.ext_getElem (hn.trans hlen.symm)
  intro i hi hi'
  obtain ⟨actual, hs, _, hv⟩ := matches_cellsHeap.mp hc i hi'
  have he : actual = block := Option.some.inj (hs.symm.trans hl)
  subst actual
  simpa only [hoff, Nat.zero_mul, Nat.zero_add, List.getElem?_eq_getElem hi,
    Option.some.injEq] using hv

theorem frame_base_absent {s : Heap} {alignment : Alignment} {base : BasePtr}
    {cells : List (Cell U8)} {count : Nat} {own : Bool} {F : Fragment}
    (hd : (Fragment.single (.cleanup base count alignment own) ∪
      cellsHeap alignment base 0 cells).Disjoint F)
    (hm : Fragment.Matches s F) (hl : s.cells base = some cells) :
    ∀ r, F r → r.base ≠ base := by
  intro resource hr hb
  obtain ⟨ha, hc⟩ := Fragment.disjoint_union_left.mp hd
  cases resource
  · rename_i other index otherAlignment value
    obtain ⟨actual, hs, _, hv⟩ := hm _ hr
    change other = base at hb
    subst other
    have he : actual.repr = cells := by simpa [Heap.cells, hs] using hl
    have hi : index < cells.length := by
      have hx := (List.getElem?_eq_some_iff.mp hv).1
      simpa [he] using hx
    have hh := hc _ ⟨index, hi, rfl⟩ _ hr
    simp [Resource.Compatible, Resource.base, Resource.key] at hh
  · rename_i other size alignment own
    have hh := ha _ rfl _ hr
    change other = base at hb
    simp [Resource.Compatible, Resource.base, Resource.key, hb] at hh

theorem freeBlock.spec (repr : Repr ty) (p : RawPtr ty) (cells : List (Cell U8))
    (count : Nat) (own : Bool) (hlen : cells.length = count * repr.size)
    (hw : ∀ c ∈ cells, c.writable) :
    Triple (sep (alloc repr p count own) (block repr p cells))
      (fun s (_ : Unit) s' => Heap.freeBlock repr p count own s = some s')
      (fun _ => emp) := by
  intro h F s hp hd hm hi
  obtain ⟨a, b, _, he, ⟨hoff, ha⟩, hb⟩ := hp
  obtain ⟨_, hb⟩ := hb
  subst h a b
  obtain ⟨hab, hF⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨ha, hc⟩ := (Fragment.matches_union _ _ _).mp hab
  obtain ⟨block, hl, hb, halign, ho⟩ := whole_of_matches hoff hlen ha hc
  have hw' : block.repr.all (fun c => c.depth == some 0) = true := by
    rw [hb, List.all_eq_true]
    intro c hc
    exact beq_iff_eq.mpr (hw c hc)
  have hrun : Heap.freeBlock repr p count own s = some (s.remove p.base) := by
    have hlen' : block.repr.length = count * repr.size := hb ▸ hlen
    have hg : p.byteOffset.val = 0 ∧ block.owned = own ∧
        repr.align.val ∣ block.alignment.val ∧ block.repr.length = count * repr.size ∧
        block.repr.all (fun c => c.depth == some 0) = true :=
      ⟨hoff, ho, halign ▸ Nat.dvd_refl _, hlen', hw'⟩
    simp only [Heap.freeBlock, hl, hg, and_self, ite_true]
  refine ⟨⟨(), _, hrun⟩, ?_⟩
  rintro _ s' hs'
  have he := Option.some.inj (hrun.symm.trans hs')
  subst s'
  have hd' : (Fragment.single (.cleanup p.base (count * repr.size) repr.align own) ∪
      cellsHeap repr.align p.base 0 cells).Disjoint F := by simpa [allocHeap, hoff] using hd
  have hcells : s.cells p.base = some cells := by simp [Heap.cells, hl, hb]
  exact ⟨∅, Fragment.disjoint_empty_left _,
    by simpa using matches_remove_frame p.base hF (frame_base_absent hd' hF hcells),
    hi.remove _, rfl⟩

theorem free_pointsTo.spec (repr : Repr ty) (p : RawPtr ty) (value : ty) (own : Bool) :
    Triple (sep (alloc repr p 1 own) (pointsTo repr p value))
      (fun s (_ : Unit) s' => Heap.freeBlock repr p 1 own s = some s') (fun _ => emp) := by
  intro h F s hp hd hm hi
  obtain ⟨a, b, hab, he, ha, data, _, hb⟩ := hp
  have hlen : (data.map (Cell.shared 0 ∘ some)).toList.length = 1 * repr.size := by simp
  have hw : ∀ c ∈ (data.map (Cell.shared 0 ∘ some)).toList, c.writable := by
    intro c hc
    rw [Vector.toList_map] at hc
    obtain ⟨byte, _, rfl⟩ := List.mem_map.mp hc
    rfl
  exact freeBlock.spec repr p _ 1 own hlen hw h F s ⟨a, b, hab, he, ha, hb⟩ hd hm hi

end SepLogic
end Aeneas.Std
