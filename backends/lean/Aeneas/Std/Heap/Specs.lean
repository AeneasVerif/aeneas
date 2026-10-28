module

public import Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

@[expose] public section

namespace Aeneas.Std.SepLogic

universe u w

variable {m : Layout.{u}}

theorem replaceRange.length {s s' : Heap m.Repr} {p : RawPtr ty}
    {old new : List (Cell ty)} (h : Heap.replaceRange m s p old new s') :
    old.length = new.length := by
  by_cases he : old = []
  · obtain ⟨hn, _⟩ := (ite_eq_left he).mp h
    simp [he, hn]
  · exact ((ite_eq_right he).mp h).1

theorem replaceRange.exists {s : Heap m.Repr} {p : RawPtr ty} {old new : List (Cell ty)}
    (hl : old.length = new.length) (hm : Fragment.Matches m s (cellsHeap p old)) :
    ∃ s', Heap.replaceRange m s p old new s' := by
  by_cases he : old = []
  · have hn : new = [] := List.length_eq_zero_iff.mp (by simpa [he] using hl.symm)
    exact ⟨s, by simp [Heap.replaceRange, he, hn]⟩
  · obtain ⟨before, after, hoff, hs⟩ := segment_of_matches he hm
    exact ⟨_, by
      simp only [Heap.replaceRange, he, ↓reduceIte]
      exact ⟨hl, before, after, hoff, hs, rfl⟩⟩

theorem replaceRange.old_eq {s s' : Heap m.Repr} {p : RawPtr ty}
    {owned old new : List (Cell ty)} (hm : Fragment.Matches m s (cellsHeap p owned))
    (hl : owned.length = old.length) (hu : Heap.replaceRange m s p old new s') :
    owned = old := by
  by_cases he : old = []
  · have ho : owned = [] := List.length_eq_zero_iff.mp (by simpa [he] using hl)
    simp [he, ho]
  · obtain ⟨before, after, hoff, hs, _⟩ := hu.load he
    exact segment_unique hm hl hoff hs

/-- Local update rule, including the empty-range no-op. Its hypotheses describe only the
owned cells; the proof supplies all disjoint-frame and demonic-successor obligations. -/
theorem triple_replaceRange {p : RawPtr ty} {old new : List (Cell ty)}
    {op : Cmd m α} {P : α → Prop}
    (hsafe : ∀ s, Fragment.Matches m s (cellsHeap p old) → ∃ x s', op s x s')
    (hpost : ∀ s x s', Fragment.Matches m s (cellsHeap p old) → op s x s' →
      P x ∧ Heap.replaceRange m s p old new s') :
    Triple m (block p old) op (fun x h => P x ∧ block p new h) := by
  intro h F s rfl hd hm hi
  obtain ⟨hown, hF⟩ := (Fragment.matches_union _ _ _ _).mp hm
  refine ⟨hsafe s hown, fun x s' hrun => ?_⟩
  obtain ⟨hp, hu⟩ := hpost s x s' hown hrun
  have hl := replaceRange.length hu
  refine ⟨cellsHeap p new, disjoint_cellsHeap_congr hl hd, ?_, hu.inv hi, hp, rfl⟩
  apply (Fragment.matches_union _ _ _ _).mpr
  by_cases he : old = []
  · obtain ⟨hn, rfl⟩ := (ite_eq_left he).mp hu
    exact ⟨by simp [hn], hF⟩
  · obtain ⟨_, before, after, hoff, hs, rfl⟩ := (ite_eq_right he).mp hu
    exact ⟨matches_segment p before new after hoff (Heap.load_store _ _ _ _),
      matches_store_frame he hl hoff hs hd hF⟩

theorem replaceRange.spec (p : RawPtr ty) (old new : List (Cell ty))
    (hl : old.length = new.length) :
    Triple m (block p old)
      (fun s (_ : Unit) s' => Heap.replaceRange m s p old new s') (fun _ => block p new) :=
  Triple.conseq (fun _ h => h) (fun _ _ h => h.2)
    (triple_replaceRange
      (fun _ hm => by
        obtain ⟨s', hs⟩ := replaceRange.exists hl hm
        exact ⟨(), s', hs⟩)
      (fun _ _ _ _ hu => ⟨True.intro, hu⟩))

theorem read.spec (p : RawPtr ty) (value : ty) (fraction : Nat) :
    Triple m (block p [.val (some fraction) value]) (Heap.read m p)
      (fun x h => x = value ∧ block p [.val (some fraction) value] h) := by
  intro h F s rfl hd hm hi
  obtain ⟨hown, hF⟩ := (Fragment.matches_union _ _ _ _).mp hm
  obtain ⟨before, after, hoff, hs⟩ := segment_of_matches (by simp) hown
  refine ⟨⟨value, s, ⟨before, after, fraction, hoff, hs⟩, rfl⟩, ?_⟩
  rintro x s' ⟨⟨before', after', f', hoff', hs'⟩, rfl⟩
  have he := segment_unique hown (by simp) hoff' hs'
  have hx : x = value := by
    have hh : f' = fraction ∧ x = value := by simpa using he.symm
    exact hh.2
  exact ⟨_, hd, (Fragment.matches_union _ _ _ _).mpr ⟨hown, hF⟩, hi, hx, rfl⟩

theorem write.spec (p : RawPtr ty) (old : Cell ty) (value : ty) (hw : old.writable) :
    Triple m (block p [old]) (Heap.write m p value) (fun _ => pointsTo p value) := by
  refine Triple.conseq (P' := block p [old])
    (Q' := fun (_ : Unit) h => True ∧ pointsTo p value h)
    (fun _ h => h) (fun _ _ h => h.2) ?_
  apply triple_replaceRange (old := [old]) (new := [.val (some 0) value])
    (P := fun _ => True)
  · intro s hm
    obtain ⟨s', hu⟩ := replaceRange.exists (new := [.val (some 0) value]) (by simp) hm
    exact ⟨(), s', old, hw, hu⟩
  · rintro s _ s' hm ⟨other, _, hu⟩
    obtain ⟨before, after, hoff, hs, _⟩ := hu.load (by simp)
    have he := segment_unique hm (by simp) hoff hs
    have hold : old = other := by simpa using he
    subst other
    exact ⟨trivial, hu⟩

end Aeneas.Std.SepLogic
