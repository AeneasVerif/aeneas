module

public import Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Model

@[expose] public section

namespace Aeneas.Std.SepLogic

universe u

def cellsHeap (p : RawPtr ty) (cs : List (Cell ty)) : Fragment :=
  fun r => ∃ (i : Nat) (hi : i < cs.length), r = .cell ty (⟨p.base, p.index + i⟩) cs[i]

def allocHeap (ty : Type u) (base : BasePtr) (count : Nat) (own : Bool) : Fragment :=
  Fragment.single (.cleanup ty base count own)

def block (p : RawPtr ty) (cs : List (Cell ty)) : Assertion :=
  fun h => h = cellsHeap p cs

def alloc (p : RawPtr ty) (count : Nat) (own : Bool) : Assertion :=
  fun h => p.index = 0 ∧ h = allocHeap ty p.base count own

abbrev pointsTo (p : RawPtr ty) (value : ty) : Assertion :=
  block p [.shared 0 value]

@[simp] theorem cellsHeap_nil (p : RawPtr ty) : cellsHeap p [] = ∅ := by
  funext r
  change (∃ (i : Nat) (hi : i < 0), r = .cell ty (⟨p.base, p.index + i⟩) [][i]) = False
  apply propext
  constructor
  · rintro ⟨i, hi, _⟩
    exact (Nat.not_lt_zero i hi).elim
  · exact False.elim

theorem cellsHeap_append (p : RawPtr ty) (a b : List (Cell ty)) :
    cellsHeap p (a ++ b) = cellsHeap p a ∪ cellsHeap (⟨p.base, p.index + a.length⟩) b := by
  funext r
  apply propext
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases ha : i < a.length
    · left
      exact ⟨i, ha, by simp [List.getElem_append_left ha]⟩
    · right
      have hb : i - a.length < b.length := by simp only [List.length_append] at hi; grind
      refine ⟨i - a.length, hb, ?_⟩
      have he : a.length + (i - a.length) = i := by grind
      simp [Nat.add_assoc, he, List.getElem_append_right (Nat.le_of_not_gt ha)]
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, by simp; grind, by simp [List.getElem_append_left hi]⟩
    · refine ⟨a.length + i, by simp; grind, ?_⟩
      simp [Nat.add_assoc]

theorem disjoint_cellsHeap_append (p : RawPtr ty) (a b : List (Cell ty)) :
    (cellsHeap p a).Disjoint (cellsHeap (⟨p.base, p.index + a.length⟩) b) := by
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  right
  refine ⟨rfl, ?_⟩
  simp only [Resource.key]
  grind

theorem block_append (p : RawPtr ty) (a b : List (Cell ty)) (h : Fragment) :
    block p (a ++ b) h ↔ sep (block p a) (block (⟨p.base, p.index + a.length⟩) b) h := by
  constructor
  · intro he
    exact ⟨_, _, disjoint_cellsHeap_append p a b, he.trans (cellsHeap_append p a b), rfl, rfl⟩
  · rintro ⟨_, _, _, rfl, rfl, rfl⟩
    exact (cellsHeap_append p a b).symm

theorem disjoint_alloc_cells (p : RawPtr ty) (n : Nat) (own : Bool)
    (cs : List (Cell ty)) :
    (allocHeap ty p.base n own).Disjoint (cellsHeap p cs) := by
  rintro _ rfl _ ⟨i, hi, rfl⟩
  exact .inr ⟨rfl, by simp [Resource.key]⟩

theorem matches_cellsHeap {m : Layout.{u}} {s : Heap m.Repr}
    {p : RawPtr ty} {cs : List (Cell ty)} :
    Fragment.Matches m s (cellsHeap p cs) ↔
      ∀ (i : Nat) (hi : i < cs.length),
        ∃ r, s.cells p.base = some r ∧ m.view ty r (p.index + i) cs[i] := by
  constructor
  · intro h i hi
    exact h _ ⟨i, hi, rfl⟩
  · rintro h _ ⟨i, hi, rfl⟩
    exact h i hi

theorem matches_views {m : Layout.{u}} {s : Heap m.Repr}
    (p : RawPtr ty) (cs : List (Cell ty)) {r : m.Repr}
    (hs : s.cells p.base = some r) (hv : m.Views ty r p.index cs) :
    Fragment.Matches m s (cellsHeap p cs) := by
  rw [matches_cellsHeap]
  intro i hi
  exact ⟨r, hs, hv i hi⟩

theorem views_unique {m : Layout.{u}} {s : Heap m.Repr}
    {p : RawPtr ty} {cs other : List (Cell ty)} {r : m.Repr}
    (hm : Fragment.Matches m s (cellsHeap p cs)) (hl : cs.length = other.length)
    (hs : s.cells p.base = some r) (hv : m.Views ty r p.index other) : cs = other := by
  apply List.ext_getElem hl
  intro i hi hi'
  obtain ⟨actual, ha, hv⟩ := matches_cellsHeap.mp hm i hi
  have he : actual = r := Option.some.inj (ha.symm.trans hs)
  subst actual
  exact m.view_unique ty r _ _ _ hv (‹m.Views ty r p.index other› i hi')

theorem disjoint_cellsHeap_congr {p : RawPtr ty} {a b : List (Cell ty)} {F : Fragment}
    (hl : a.length = b.length) (hd : (cellsHeap p a).Disjoint F) :
    (cellsHeap p b).Disjoint F := by
  rintro _ ⟨i, hi, rfl⟩ r hr
  have hi' : i < a.length := by grind
  exact hd _ ⟨i, hi', rfl⟩ r hr

/-- Nonempty logical ranges identify one live representation and its local observations. -/
theorem views_of_matches {m : Layout.{u}} {s : Heap m.Repr}
    {p : RawPtr ty} {cs : List (Cell ty)} (hne : cs ≠ [])
    (hm : Fragment.Matches m s (cellsHeap p cs)) :
    ∃ r, s.cells p.base = some r ∧ m.Views ty r p.index cs := by
  have hp : 0 < cs.length := List.length_pos_iff.mpr hne
  obtain ⟨r, hs, _⟩ := matches_cellsHeap.mp hm 0 hp
  refine ⟨r, hs, fun i hi => ?_⟩
  obtain ⟨r', hs', hv⟩ := matches_cellsHeap.mp hm i hi
  have he : r' = r := Option.some.inj (hs'.symm.trans hs)
  simpa [he] using hv

theorem matches_updates_frame {m : Layout.{u}} {s : Heap m.Repr}
    {p : RawPtr ty} {old new : List (Cell ty)} {r r' : m.Repr} {F : Fragment.{u}}
    (hne : old ≠ []) (hl : old.length = new.length)
    (hs : s.cells p.base = some r) (hu : m.Updates ty p.index new r r')
    (hd : (cellsHeap p old).Disjoint F) (hm : Fragment.Matches m s F) :
    Fragment.Matches m (s.storeRepr p.base r') F := by
  intro resource hr
  have hhold := hm resource hr
  by_cases hb : resource.base = p.base
  · obtain ⟨i, hi⟩ : ∃ i, i < old.length := ⟨0, List.length_pos_iff.mpr hne⟩
    have hc := hd _ ⟨i, hi, rfl⟩ resource hr
    have ht : ty = resource.ty := by
      rcases hc with hb' | ⟨ht, _⟩
      · exact (hb' hb.symm).elim
      · exact ht
    cases resource
    · rename_i otherTy q value
      change ty = otherTy at ht
      subst otherTy
      obtain ⟨actual, ha, hv⟩ := hhold
      have hqb : q.base = p.base := hb
      have he : actual = r := by
        rw [hqb] at ha
        exact Option.some.inj (ha.symm.trans hs)
      have hout : q.index < p.index ∨ p.index + old.length ≤ q.index := by
        by_cases hleft : q.index < p.index
        · exact .inl hleft
        right
        apply Nat.le_of_not_gt
        intro hright
        have hidx : q.index - p.index < old.length := by grind
        have hc' := hd _ ⟨q.index - p.index, hidx, rfl⟩ _ hr
        simp [Resource.Compatible, Resource.base, Resource.ty, Resource.key, hqb] at hc'
        grind
      subst actual
      exact ⟨r', by simp [hqb], (hu.outside (by simpa [hl] using hout) value).mpr hv⟩
    · rename_i otherTy base count own
      change ty = otherTy at ht
      subst otherTy
      change base = p.base at hb
      obtain ⟨ha, actual, hs', hn, hbytes⟩ := hhold
      have he : actual = r := by
        rw [hb] at hs'
        exact Option.some.inj (hs'.symm.trans hs)
      exact ⟨ha, r', by simp [hb], by simpa [hu.extent ty, he] using hn,
        by simpa [hu.bytes_length, he] using hbytes⟩
  · cases resource
    · rename_i otherTy q value
      change q.base ≠ p.base at hb
      obtain ⟨actual, ha, hv⟩ := hhold
      exact ⟨actual, by simpa [Heap.storeRepr, update, hb] using ha, hv⟩
    · rename_i otherTy base count own
      change base ≠ p.base at hb
      obtain ⟨ha, actual, hs', hn⟩ := hhold
      exact ⟨ha, actual, by simpa [Heap.storeRepr, update, hb] using hs', hn⟩

end Aeneas.Std.SepLogic
