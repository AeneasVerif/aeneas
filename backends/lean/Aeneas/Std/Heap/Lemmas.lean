module

public import Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Model

@[expose] public section

namespace Aeneas.Std

universe u v

namespace Layout

variable {m : Layout.{u}}

theorem Views.bound {ty : Type u} {r : m.Repr} {start : Nat} {cs : List (Cell ty)}
    (h : m.Views ty r start cs) (hne : cs ≠ []) :
    start + cs.length ≤ m.extent ty r := by
  have hp := List.length_pos_iff.mpr hne
  have hi : cs.length - 1 < cs.length := by grind
  have hb := m.view_bound ty r _ _ (h _ hi)
  grind

theorem Views.unique {ty : Type u} {r : m.Repr} {start : Nat}
    {a b : List (Cell ty)} (ha : m.Views ty r start a) (hb : m.Views ty r start b)
    (hl : a.length = b.length) : a = b := by
  apply List.ext_getElem hl
  intro i hi hi'
  exact m.view_unique ty r _ _ _ (ha i hi) (hb i hi')

theorem Updates.extent {ty : Type u} {start : Nat} {cs : List (Cell ty)}
    {r r' : m.Repr} (h : m.Updates ty start cs r r') (U : Type u) :
    m.extent U r' = m.extent U r := by
  induction h
  · rfl
  · rename_i hs ht ih
    exact ih.trans (m.set_extent _ _ _ _ _ hs U)

theorem Updates.bytes_length {ty : Type u} {start : Nat} {cs : List (Cell ty)}
    {r r' : m.Repr} (h : m.Updates ty start cs r r') :
    (m.bytes r').length = (m.bytes r).length := by
  induction h
  · rfl
  · rename_i hs ht ih
    exact ih.trans (m.set_bytes_length _ _ _ _ _ hs)

theorem Updates.frame {ty U : Type u} {start j : Nat} {cs : List (Cell ty)}
    {r r' : m.Repr} (h : m.Updates ty start cs r r')
    (hd : ∀ i, i < cs.length → CellsDisjoint m.byteLength ty (start + i) U j)
    (value : Cell U) : m.view U r' j value ↔ m.view U r j value := by
  induction h
  · rfl
  · rename_i i c cs r r₁ r₂ hs ht ih
    have hhead := hd 0 (by simp)
    have htail : ∀ k, k < cs.length →
        CellsDisjoint m.byteLength ty (i + 1 + k) U j := by
      intro k hk
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using hd (k + 1) (by simp; grind)
    exact (ih htail).trans (m.set_frame _ _ _ _ _ hs U j (by simpa using hhead) value)

theorem Updates.outside {ty : Type u} {start j : Nat} {cs : List (Cell ty)}
    {r r' : m.Repr} (h : m.Updates ty start cs r r')
    (hout : j < start ∨ start + cs.length ≤ j) (value : Cell ty) :
    m.view ty r' j value ↔ m.view ty r j value := by
  apply h.frame
  intro i hi
  exact m.disjoint_same ty (by grind)

theorem Updates.views {ty : Type u} {start : Nat} {cs : List (Cell ty)}
    {r r' : m.Repr} (h : m.Updates ty start cs r r') : m.Views ty r' start cs := by
  induction h
  · intro i hi
    simp at hi
  · rename_i i c cs r r₁ r₂ hs ht ih
    intro j hj
    cases j
    · simpa using (ht.outside (Or.inl (Nat.lt_succ_self i)) c).mpr
        (m.set_view _ _ _ _ _ hs)
    · rename_i j
      have hj' : j < cs.length := by simpa using hj
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using ih j hj'

theorem Updates.exists (ty : Type u) (start : Nat) (cs : List (Cell ty)) (r : m.Repr)
    (hb : start + cs.length ≤ m.extent ty r) :
    ∃ r', m.Updates ty start cs r r' := by
  induction cs generalizing start r
  · exact ⟨r, .nil start r⟩
  · rename_i c cs ih
    have hi : start < m.extent ty r := by simp only [List.length_cons] at hb; grind
    obtain ⟨r₁, hs⟩ := m.set_exists ty start r hi c
    have hb' : start + 1 + cs.length ≤ m.extent ty r₁ := by
      rw [m.set_extent _ _ _ _ _ hs ty]
      simp only [List.length_cons] at hb
      grind
    obtain ⟨r₂, ht⟩ := ih (start + 1) r₁ hb'
    exact ⟨r₂, .cons hs ht⟩

end Layout

namespace Heap

variable {Repr : Type v} {m : Layout.{u}}

theorem inv_empty : (empty : Heap Repr).Inv := fun _ _ => ⟨rfl, rfl⟩

@[simp] theorem cells_storeRepr (s : Heap Repr) (base : BasePtr) (r : Repr) :
    (s.storeRepr base r).cells base = some r := by simp [storeRepr, update]

@[simp] theorem cells_remove (s : Heap Repr) (base : BasePtr) :
    (s.remove base).cells base = none := by simp [remove, update]

theorem Inv.base_lt {s : Heap Repr} (h : s.Inv) {base : BasePtr} {r : Repr}
    (hc : s.cells base = some r) : base < s.next := by
  apply Nat.lt_of_not_ge
  intro hn
  have hf := (h base hn).1
  simp [hf] at hc

theorem Inv.storeRepr {s : Heap Repr} (h : s.Inv)
    (base : BasePtr) (r : Repr) (hb : base < s.next) : (s.storeRepr base r).Inv := by
  intro other ho
  change s.next ≤ other at ho
  have hne : other ≠ base := by grind
  simpa [Heap.storeRepr, update, hne] using h other ho

theorem Inv.createRepr {s : Heap Repr} (h : s.Inv) (r : Repr) (own : Bool) :
    (s.createRepr r own).Inv := by
  intro base hb
  change s.next + 1 ≤ base at hb
  have hne : base ≠ s.next := by grind
  have hle : s.next ≤ base := by grind
  simpa [Heap.createRepr, update, hne] using h base hle

theorem Inv.remove {s : Heap Repr} (h : s.Inv) (base : BasePtr) :
    (s.remove base).Inv := by
  intro other ho
  change s.next ≤ other at ho
  by_cases he : other = base
  · simp [Heap.remove, update, he]
  · simpa [Heap.remove, update, he] using h other ho

theorem writable_of_view {ty : Type u} {r : m.Repr} {i : Nat} {c : Cell ty}
    (hv : m.view ty r i c) (hw : c.writable) : Writable m ty r i := by
  refine ⟨m.view_bound _ _ _ _ hv, ?_, ?_⟩
  · intro b hlo hhi
    exact ⟨c.permission, m.view_permission _ _ _ _ hv b hlo hhi, hw⟩
  · intro other ho
    have he := m.view_unique _ _ _ _ _ ho hv
    simpa [he] using hw

theorem replaceRange.inv {s s' : Heap m.Repr} {p : RawPtr ty}
    {old new : List (Cell ty)} (h : replaceRange m s p old new s') (hi : s.Inv) :
    s'.Inv := by
  by_cases he : old = []
  · have hs : s' = s := ((ite_eq_left he).mp h).2
    simpa [hs] using hi
  · obtain ⟨_, r, r', hs, _, _, rfl⟩ := (ite_eq_right he).mp h
    exact hi.storeRepr _ _ (hi.base_lt hs)

theorem newCells.exists (cs : List (Cell ty)) (own : Bool)
    (s : Heap m.Repr) (hi : s.Inv) : ∃ p s', newCells m cs own s p s' := by
  obtain ⟨r, hr⟩ := m.create_exists ty cs
  exact ⟨⟨s.next, 0⟩, s.createRepr r own, hi, rfl, r, hr, rfl⟩

end Heap
end Aeneas.Std
