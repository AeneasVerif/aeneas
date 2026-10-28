module

public import Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Model

@[expose] public section

namespace Aeneas.Std.SepLogic

universe u

def cellsHeap (p : RawPtr ty) (cs : List (Cell ty)) : Fragment :=
  fun r => ∃ (i : Nat) (hi : i < cs.length), r = .cell ty (p.shift i) cs[i]

def allocHeap (ty : Type u) (base : BasePtr) (count : Nat) (own : Bool) : Fragment :=
  Fragment.single (.cleanup ty base count own)

def block (p : RawPtr ty) (cs : List (Cell ty)) : Assertion :=
  fun h => h = cellsHeap p cs

def alloc (p : RawPtr ty) (count : Nat) (own : Bool) : Assertion :=
  fun h => p.offset = 0 ∧ h = allocHeap ty p.base count own

abbrev pointsTo (p : RawPtr ty) (value : ty) : Assertion :=
  block p [.val (some 0) value]

@[simp] theorem cellsHeap_nil (p : RawPtr ty) : cellsHeap p [] = ∅ := by
  funext r
  change (∃ (i : Nat) (hi : i < 0), r = .cell ty (p.shift i) [][i]) = False
  apply propext
  constructor
  · rintro ⟨i, hi, _⟩
    exact (Nat.not_lt_zero i hi).elim
  · exact False.elim

theorem cellsHeap_append (p : RawPtr ty) (a b : List (Cell ty)) :
    cellsHeap p (a ++ b) = cellsHeap p a ∪ cellsHeap (p.shift a.length) b := by
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
      simp [RawPtr.shift_shift, he, List.getElem_append_right (Nat.le_of_not_gt ha)]
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, by simp; grind, by simp [List.getElem_append_left hi]⟩
    · refine ⟨a.length + i, by simp; grind, ?_⟩
      simp [RawPtr.shift_shift]

theorem disjoint_cellsHeap_append (p : RawPtr ty) (a b : List (Cell ty)) :
    (cellsHeap p a).Disjoint (cellsHeap (p.shift a.length) b) := by
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  right
  refine ⟨rfl, ?_⟩
  simp only [Resource.key, RawPtr.offset_shift]
  grind

theorem block_append (p : RawPtr ty) (a b : List (Cell ty)) (h : Fragment) :
    block p (a ++ b) h ↔ sep (block p a) (block (p.shift a.length) b) h := by
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
        ∃ actual, s.load m.interpret ty p.base = some actual ∧
          actual[p.offset + i]? = some cs[i] := by
  constructor
  · intro h i hi
    exact h _ ⟨i, hi, rfl⟩
  · rintro h _ ⟨i, hi, rfl⟩
    exact h i hi

theorem matches_segment {m : Layout.{u}} {s : Heap m.Repr}
    (p : RawPtr ty) (before cs after : List (Cell ty)) (hoff : before.length = p.offset)
    (hs : s.load m.interpret ty p.base = some (before ++ cs ++ after)) :
    Fragment.Matches m s (cellsHeap p cs) := by
  rw [matches_cellsHeap]
  intro i hi
  refine ⟨_, hs, ?_⟩
  rw [← hoff]
  simp [List.getElem?_append_right, List.getElem?_append_left hi]

theorem segment_unique {m : Layout.{u}} {s : Heap m.Repr}
    {p : RawPtr ty} {cs other before after : List (Cell ty)}
    (hm : Fragment.Matches m s (cellsHeap p cs)) (hl : cs.length = other.length)
    (hoff : before.length = p.offset)
    (hs : s.load m.interpret ty p.base = some (before ++ other ++ after)) : cs = other := by
  apply List.ext_getElem hl
  intro i hi hi'
  obtain ⟨actual, ha, hv⟩ := matches_cellsHeap.mp hm i hi
  have he : actual = before ++ other ++ after := Option.some.inj (ha.symm.trans hs)
  have hother : (before ++ other ++ after)[p.offset + i]? = some other[i] := by
    rw [← hoff]
    simp [List.getElem?_append_right, List.getElem?_append_left hi']
  rw [he, hother] at hv
  exact (Option.some.inj hv).symm

theorem disjoint_cellsHeap_congr {p : RawPtr ty} {a b : List (Cell ty)} {F : Fragment}
    (hl : a.length = b.length) (hd : (cellsHeap p a).Disjoint F) :
    (cellsHeap p b).Disjoint F := by
  rintro _ ⟨i, hi, rfl⟩ r hr
  have hi' : i < a.length := by grind
  exact hd _ ⟨i, hi', rfl⟩ r hr

theorem list_segment {α : Type u} (actual cs : List α) (offset : Nat)
    (hlen : offset + cs.length ≤ actual.length)
    (hc : ∀ (i : Nat) (hi : i < cs.length), actual[offset + i]? = some cs[i]) :
    actual = actual.take offset ++ cs ++ actual.drop (offset + cs.length) := by
  have he : (actual.drop offset).take cs.length = cs := by
    apply List.ext_getElem
    · simp [List.length_take, List.length_drop]
      grind
    · intro i hi hi'
      have hv := hc i hi'
      simp only [List.getElem?_eq_some_iff] at hv
      obtain ⟨hb, hv⟩ := hv
      simpa using hv
  calc
    actual = actual.take offset ++ actual.drop offset :=
      (List.take_append_drop offset actual).symm
    _ = actual.take offset ++
        ((actual.drop offset).take cs.length ++ (actual.drop offset).drop cs.length) :=
      congrArg (actual.take offset ++ ·) (List.take_append_drop cs.length _).symm
    _ = _ := by
      rw [he, List.drop_drop, Nat.add_comm offset cs.length, List.append_assoc]

/-- Nonempty logical ranges reconstruct a typed segment without splitting `Repr`. -/
theorem segment_of_matches {m : Layout.{u}} {s : Heap m.Repr}
    {p : RawPtr ty} {cs : List (Cell ty)} (hne : cs ≠ [])
    (hm : Fragment.Matches m s (cellsHeap p cs)) :
    ∃ before after, before.length = p.offset ∧
      s.load m.interpret ty p.base = some (before ++ cs ++ after) := by
  have hp : 0 < cs.length := List.length_pos_iff.mpr hne
  obtain ⟨actual, hs, _⟩ := matches_cellsHeap.mp hm 0 hp
  have hc : ∀ (i : Nat) (hi : i < cs.length), actual[p.offset + i]? = some cs[i] := by
    intro i hi
    obtain ⟨actual', hs', hv⟩ := matches_cellsHeap.mp hm i hi
    have he : actual' = actual := Option.some.inj (hs'.symm.trans hs)
    simpa [he] using hv
  have hb : p.offset + cs.length ≤ actual.length := by
    have hlast := hc (cs.length - 1) (by grind)
    have := (List.getElem?_eq_some_iff.mp hlast).1
    grind
  have hoff : p.offset ≤ actual.length := by grind
  exact ⟨actual.take p.offset, actual.drop (p.offset + cs.length),
    by simp [List.length_take, Nat.min_eq_left hoff],
    by rw [← list_segment actual cs p.offset hb hc]; exact hs⟩

theorem matches_store_frame {m : Layout.{u}} {s : Heap m.Repr}
    {p : RawPtr ty} {old new before after : List (Cell ty)} {F : Fragment.{u}}
    (hne : old ≠ []) (hl : old.length = new.length) (hoff : before.length = p.offset)
    (hs : s.load m.interpret ty p.base = some (before ++ old ++ after))
    (hd : (cellsHeap p old).Disjoint F) (hm : Fragment.Matches m s F) :
    Fragment.Matches m (s.store m.represent ty p.base (before ++ new ++ after)) F := by
  intro r hr
  have hhold := hm r hr
  by_cases hb : r.base = p.base
  · obtain ⟨i, hi⟩ : ∃ i, i < old.length := ⟨0, List.length_pos_iff.mpr hne⟩
    have hc := hd _ ⟨i, hi, rfl⟩ r hr
    have ht : ty = r.ty := by
      rcases hc with hb' | ⟨ht, _⟩
      · exact (hb' hb.symm).elim
      · exact ht
    cases r
    · rename_i otherTy q value
      change ty = otherTy at ht
      subst otherTy
      obtain ⟨actual, ha, hv⟩ := hhold
      have hqb : q.base = p.base := hb
      have he : actual = before ++ old ++ after := by
        rw [hqb] at ha
        exact Option.some.inj (ha.symm.trans hs)
      have hout : q.offset < p.offset ∨ p.offset + old.length ≤ q.offset := by
        by_cases hleft : q.offset < p.offset
        · exact .inl hleft
        right
        apply Nat.le_of_not_gt
        intro hright
        have hidx : q.offset - p.offset < old.length := by grind
        have hc' := hd _ ⟨q.offset - p.offset, hidx, rfl⟩ _ hr
        simp [Resource.Compatible, Resource.base, Resource.ty, Resource.key, hqb] at hc'
        grind
      refine ⟨before ++ new ++ after, by simp [hqb], ?_⟩
      subst actual
      rcases hout with hleft | hright
      · simpa [List.getElem?_append_left, hoff, hleft] using hv
      · have ho : (before ++ old).length ≤ q.offset := by simp; grind
        have hn : (before ++ new).length ≤ q.offset := by simp; grind
        rw [List.getElem?_append_right ho] at hv
        rw [List.getElem?_append_right hn]
        simpa [hl] using hv
    · rename_i otherTy base count own
      change ty = otherTy at ht
      subst otherTy
      change base = p.base at hb
      obtain ⟨ha, actual, hs', hn⟩ := hhold
      have he : actual = before ++ old ++ after := by
        rw [hb] at hs'
        exact Option.some.inj (hs'.symm.trans hs)
      exact ⟨ha, before ++ new ++ after, by simp [hb],
        by simpa [he, hl] using hn⟩
  · cases r
    · rename_i otherTy q value
      obtain ⟨actual, ha, hv⟩ := hhold
      exact ⟨actual, (Heap.load_store_other s ty otherTy p.base q.base _ hb).trans ha, hv⟩
    · rename_i otherTy base count own
      obtain ⟨ha, actual, hs', hn⟩ := hhold
      exact ⟨ha, actual, (Heap.load_store_other s ty otherTy p.base base _ hb).trans hs', hn⟩

end Aeneas.Std.SepLogic
