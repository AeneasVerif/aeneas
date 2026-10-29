module

public import Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

@[expose] public section

namespace Aeneas.Std.SepLogic

universe u w

theorem replaceRange.length {s s' : Heap Std.Block.{u}} {p : RawPtr ty}
    {old new : List (Cell ty)} (h : Heap.replaceRange s p old new s') :
    old.length = new.length := by
  by_cases he : old = []
  · obtain ⟨hn, _⟩ := (ite_eq_left he).mp h
    simp [he, hn]
  · exact ((ite_eq_right he).mp h).1

theorem replaceRange.exists {s : Heap Std.Block.{u}} {p : RawPtr ty} {old new : List (Cell ty)}
    (hl : old.length = new.length) (hm : Fragment.Matches s (cellsHeap p old)) :
    ∃ s', Heap.replaceRange s p old new s' := by
  by_cases he : old = []
  · have hn : new = [] := List.length_eq_zero_iff.mp (by simpa [he] using hl.symm)
    exact ⟨s, by simp [Heap.replaceRange, he, hn]⟩
  · obtain ⟨r, hs, ha, hv⟩ := views_of_matches he hm
    obtain ⟨r', hu⟩ := Std.Block.Updates.exists ty p.index new r (by simpa [hl] using hv.bound he)
    exact ⟨s.storeRepr p.base r', (ite_eq_right he).mpr ⟨hl, r, r', hs, ha, hv, hu, rfl⟩⟩

theorem replaceRange.old_eq {s s' : Heap Std.Block.{u}} {p : RawPtr ty}
    {owned old new : List (Cell ty)} (hm : Fragment.Matches s (cellsHeap p owned))
    (hl : owned.length = old.length) (hu : Heap.replaceRange s p old new s') :
    owned = old := by
  by_cases he : old = []
  · have ho : owned = [] := List.length_eq_zero_iff.mp (by simpa [he] using hl)
    simp [he, ho]
  · obtain ⟨_, r, _, hs, _, hv, _⟩ := (ite_eq_right he).mp hu
    exact views_unique hm hl hs hv

/-- Local list rules are proved from composed single-cell updates, not whole-block encoding. -/
theorem triple_replaceRange {p : RawPtr ty} {old new : List (Cell ty)}
    {op : Cmd α} {P : α → Prop}
    (hsafe : ∀ s, Fragment.Matches s (cellsHeap p old) → ∃ x s', op s x s')
    (hpost : ∀ s x s', Fragment.Matches s (cellsHeap p old) → op s x s' →
      P x ∧ Heap.replaceRange s p old new s') :
    Triple (block p old) op (fun x h => P x ∧ block p new h) := by
  intro h F s rfl hd hm hi
  obtain ⟨hown, hF⟩ := (Fragment.matches_union _ _ _).mp hm
  refine ⟨hsafe s hown, fun x s' hrun => ?_⟩
  obtain ⟨hp, hu⟩ := hpost s x s' hown hrun
  have hl := replaceRange.length hu
  refine ⟨cellsHeap p new, disjoint_cellsHeap_congr hl hd, ?_, hu.inv hi, hp, rfl⟩
  apply (Fragment.matches_union _ _ _).mpr
  by_cases he : old = []
  · obtain ⟨hn, rfl⟩ := (ite_eq_left he).mp hu
    exact ⟨by simp [hn], hF⟩
  · obtain ⟨_, r, r', hs, ha, _, hupdates, rfl⟩ := (ite_eq_right he).mp hu
    exact ⟨matches_views p new (by simp [hs]) (by simpa using ha) hupdates.views,
      matches_updates_frame he hl hs hupdates hd hF⟩

theorem replaceRange.spec (p : RawPtr ty) (old new : List (Cell ty))
    (hl : old.length = new.length) :
    Triple (block p old)
      (fun s (_ : Unit) s' => Heap.replaceRange s p old new s') (fun _ => block p new) :=
  Triple.conseq (fun _ h => h) (fun _ _ h => h.2)
    (triple_replaceRange
      (fun _ hm => by
        obtain ⟨s', hs⟩ := replaceRange.exists hl hm
        exact ⟨(), s', hs⟩)
      (fun _ _ _ _ hu => ⟨True.intro, hu⟩))

theorem read.spec (p : RawPtr ty) (value : ty) (depth : Nat) :
    Triple (block p [.shared depth (some value)]) (Heap.read p)
      (fun x h => x = value ∧ block p [.shared depth (some value)] h) := by
  intro h F s rfl hd hm hi
  obtain ⟨hown, _⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨r, hs, ha, hv⟩ := matches_cellsHeap.mp hown 0 (by simp)
  have hv' : Std.Block.view ty r p.index (.shared depth (some value)) := by simpa using hv
  refine ⟨⟨value, s, ⟨r, depth, hs, ha, hv'⟩, rfl⟩, ?_⟩
  rintro x s' ⟨⟨r', depth', hs', _, hv'⟩, rfl⟩
  have he : r' = r := Option.some.inj (hs'.symm.trans hs)
  subst r'
  have hx := (Cell.shared.inj (Std.Block.view_unique ty r _ _ _ hv' ‹Std.Block.view ty r p.index
    (.shared depth (some value))›)).2
  exact ⟨_, hd, hm, hi, Option.some.inj hx, rfl⟩

theorem write.spec (p : RawPtr ty) (old : Cell ty) (value : ty) (hw : old.writable) :
    Triple (block p [old]) (Heap.write p value) (fun _ => pointsTo p value) := by
  apply Triple.conseq (P' := block p [old])
    (Q' := fun (_ : Unit) h => True ∧ pointsTo p value h)
    (fun _ h => h) (fun _ _ h => h.2)
  apply triple_replaceRange (old := [old]) (new := [.shared 0 (some value)]) (P := fun _ => True)
  · intro s hm
    obtain ⟨r, hs, ha, hv⟩ := matches_cellsHeap.mp hm 0 (by simp)
    have hv' : Std.Block.view ty r p.index old := by simpa using hv
    have hwrite := Heap.writable_of_view hv' hw
    obtain ⟨r', hu⟩ := Std.Block.set_exists ty p.index r hwrite.1 (.shared 0 (some value))
    exact ⟨(), _, r, r', hs, ha, hwrite, hu, rfl⟩
  · rintro s _ s' hm ⟨r, r', hs, halign, _, hu, rfl⟩
    obtain ⟨actual, ha, _, hv⟩ := matches_cellsHeap.mp hm 0 (by simp)
    have he : actual = r := Option.some.inj (ha.symm.trans hs)
    subst actual
    refine ⟨trivial, (ite_eq_right (by simp)).mpr ⟨rfl, r, r', hs, halign, ?_, ?_, rfl⟩⟩
    · intro i hi
      have he : i = 0 := by simpa using hi
      subst i
      simpa using hv
    · exact .cons hu (.nil _ _)

end Aeneas.Std.SepLogic
