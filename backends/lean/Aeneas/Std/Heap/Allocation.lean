module

public import Aeneas.Std.Heap.Specs

/-! Fresh view creation and whole-view retirement. Placement feasibility is an
input-state obligation; indexed cleanup resources do not imply root authority
or absence of active aliases. Retirement does not kill the physical root. -/

@[expose] public section

namespace Aeneas.Std

namespace Heap

theorem createRepr.enabled (s : Heap) (blk : Block) (hf : s.allocations s.next = none)
    (valid : (Heap.mk (update s.allocations s.next (some blk)) (s.next + 1)).check = true) :
    s.createRepr blk = some (s.next, ⟨update s.allocations s.next (some blk), s.next + 1⟩) := by
  simp [createRepr, hf, commit, valid]

theorem createRepr.success {s s' : Heap} {blk : Block} {base : Nat}
    (h : s.createRepr blk = some (base, s')) :
    base = s.next ∧
      s' = ⟨update s.allocations s.next (some blk), s.next + 1⟩ := by
  unfold createRepr at h
  split at h
  · obtain ⟨result, hc, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hb, hs⟩ := Prod.mk.inj he
    exact ⟨hb.symm, hs ▸ (commit_success _ _ hc).1⟩
  · contradiction

theorem live_create {s : Heap} {blk fresh : Block} {s' : Heap} {id : Nat}
    (hinv : s.Inv) (hlive : s.live blk = true)
    (hcreate : s.createRepr fresh = some (id, s')) : s'.live blk = true := by
  obtain ⟨_, rfl⟩ := createRepr.success hcreate
  cases hr : s.allocations blk.root
  · simp [live, hr] at hlive
  · have hne : blk.root ≠ s.next := by have := hinv.base_lt hr; grind
    simpa [live, update, hne, hr] using hlive

theorem retire_support (s : Heap) (id : Nat) (hinv : s.Inv) (hid : id < s.next) :
    ∀ j, (s.retire id).next ≤ j → (s.retire id).allocations j = none := by
  intro j hj
  have hne : j ≠ id := by change s.next ≤ j at hj; grind
  simpa [retire, update, hne] using hinv.1 j hj

end Heap

namespace SepLogic

theorem matches_create_frame {s s' : Heap} {F : Fragment} {blk : Block} {base : Nat}
    (hi : s.Inv) (hm : Fragment.Matches s F)
    (h : s.createRepr blk = some (base, s')) : Fragment.Matches s' F := by
  have he := (Heap.createRepr.success h).2
  intro resource hr
  have hh := hm resource hr
  obtain ⟨actual, hl⟩ := hh.live
  have hne : resource.base ≠ s.next := by have := hi.base_lt hl; grind
  cases resource
  · obtain ⟨actual, hl, hlive, ha, hv⟩ := hh
    simp only [Resource.base] at hne
    refine ⟨actual, ?_, Heap.live_create hi hlive h, ha, hv⟩
    simpa [he, update, Resource.base, hne] using hl
  · obtain ⟨actual, hl, hn, hlive, ha, ho⟩ := hh
    simp only [Resource.base] at hne
    refine ⟨actual, ?_, hn, Heap.live_create hi hlive h, ha, ho⟩
    simpa [he, update, Resource.base, hne] using hl

theorem fresh_disjoint {s : Heap} {F h : Fragment}
    (hi : s.Inv) (hm : Fragment.Matches s F)
    (hfresh : ∀ r, h r → r.base = s.next) : h.Disjoint F := by
  intro r hr other ho
  obtain ⟨actual, hl⟩ := (hm other ho).live
  have hlt := hi.base_lt hl
  left
  rw [hfresh r hr]
  grind

/-- Creation may alias another view physically; its fresh ghost ID gives linear
resource disjointness, while the checked invariant gives physical compatibility. -/
theorem createRepr.spec (s : Heap) (blk : Block)
    (valid : (Heap.mk (update s.allocations s.next (some blk)) (s.next + 1)).check = true)
    (live : (Heap.mk (update s.allocations s.next (some blk)) (s.next + 1)).live blk = true) :
    TripleAt emp (fun s base s' => s.createRepr blk = some (base, s'))
      (fun base h => base = s.next ∧
        h = Fragment.single (.cleanup base blk.repr.length blk.bptr blk.owned) ∪
          cellsHeap blk.bptr base 0 blk.repr) s := by
  rintro h F rfl hd hm hinv
  have old := (Fragment.matches_union _ _ _).mp hm |>.2
  have hrun := Heap.createRepr.enabled s blk (Heap.fresh s hinv) valid
  refine ⟨⟨s.next, _, hrun⟩, ?_⟩
  intro base s' hs'
  obtain ⟨rfl, rfl⟩ := Heap.createRepr.success hs'
  let resource := Fragment.single (.cleanup s.next blk.repr.length blk.bptr blk.owned) ∪
    cellsHeap blk.bptr s.next 0 blk.repr
  have fresh : ∀ r, resource r → r.base = s.next := by
    rintro r (rfl | ⟨i, hi, rfl⟩)
    · rfl
    · rfl
  refine ⟨resource, fresh_disjoint hinv old fresh, ?_,
    Heap.createRepr_Inv s blk _ _ hinv hrun, rfl, rfl⟩
  apply (Fragment.matches_union _ _ _).mpr
  refine ⟨?_, matches_create_frame hinv old hrun⟩
  apply (Fragment.matches_union _ _ _).mpr
  constructor
  · exact (Fragment.matches_single _ _).mpr
      ⟨blk, by simp [update], rfl, live, rfl, rfl⟩
  · rw [matches_cellsHeap]
    intro i hi
    exact ⟨blk, by simp [update], live, rfl, by simp [List.getElem?_eq_getElem hi]⟩

theorem matches_retire_frame {s : Heap} {F : Fragment} {base : Nat}
    (hm : Fragment.Matches s F) (hne : ∀ r, F r → r.base ≠ base) :
    Fragment.Matches (s.retire base) F := by
  intro resource hr
  have hh := hm resource hr
  have hne' := hne resource hr
  have hlive : ∀ blk, s.live blk = true → (s.retire base).live blk = true := by
    intro blk hv
    by_cases he : blk.root = base
    · simpa [Heap.live, Heap.retire, update, he, Option.map_map, Function.comp_def] using hv
    · simpa [Heap.live, Heap.retire, update, he] using hv
  cases resource
  · obtain ⟨blk, hl, hv, ha, hc⟩ := hh
    simp only [Resource.base] at hne'
    exact ⟨blk, by simpa [Heap.retire, update, Resource.base, hne'] using hl,
      hlive blk hv, ha, hc⟩
  · obtain ⟨blk, hl, hn, hv, ha, ho⟩ := hh
    simp only [Resource.base] at hne'
    exact ⟨blk, by simpa [Heap.retire, update, Resource.base, hne'] using hl,
      hn, hlive blk hv, ha, ho⟩

/-- Whole indexed ownership excludes same-view resources from the frame.
It says nothing about different-view aliases of that root. -/
theorem frame_base_absent {s : Heap} {base : Nat} {blk : Block} {F : Fragment}
    (hl : s.allocations base = some blk)
    (hd : (Fragment.single (.cleanup base blk.repr.length blk.bptr blk.owned) ∪
      cellsHeap blk.bptr base 0 blk.repr).Disjoint F)
    (hm : Fragment.Matches s F) : ∀ r, F r → r.base ≠ base := by
  intro resource hr hb
  obtain ⟨ha, hc⟩ := Fragment.disjoint_union_left.mp hd
  cases resource
  · rename_i other index bptr value
    obtain ⟨actual, hs, _, _, hv⟩ := hm _ hr
    change other = base at hb
    subst other
    have he : actual = blk := Option.some.inj (hs.symm.trans hl)
    subst actual
    have hi := List.getElem?_eq_some_iff.mp hv |>.1
    have hh := hc (.cell base index blk.bptr blk.repr[index])
      ⟨index, hi, by simp⟩ (.cell base index bptr value) hr
    simp [Resource.Compatible, Resource.base, Resource.key] at hh
  · rename_i other size bptr own
    change other = base at hb
    subst other
    have hh := ha _ rfl _ hr
    simp [Resource.Compatible, Resource.base, Resource.key] at hh

/-- Reusable retirement contract. Concrete runtime guards still belong to the
operation-specific theorem; no claim of physical death or safe return authority. -/
theorem retire.spec (s : Heap) (base : Nat) (blk : Block)
    (hl : s.allocations base = some blk) (valid : (s.retire base).check = true) :
    TripleAt
      (fun h => h = Fragment.single (.cleanup base blk.repr.length blk.bptr blk.owned) ∪
        cellsHeap blk.bptr base 0 blk.repr)
      (fun s (_ : Unit) s' => Heap.commit (s.retire base) = some s')
      (fun _ => emp) s := by
  rintro h F rfl hd hm hinv
  have old := (Fragment.matches_union _ _ _).mp hm |>.2
  have hr : Heap.commit (s.retire base) = some (s.retire base) := by
    simp [Heap.commit, valid]
  refine ⟨⟨(), _, hr⟩, ?_⟩
  intro _ s' he
  have he := Option.some.inj (hr.symm.trans he)
  subst s'
  exact ⟨∅, Fragment.disjoint_empty_left _,
    by simpa using matches_retire_frame old (frame_base_absent hl hd old),
    Heap.commit_Inv _ _ (Heap.retire_support s base hinv (hinv.base_lt hl)) hr, rfl⟩

end SepLogic
end Aeneas.Std
