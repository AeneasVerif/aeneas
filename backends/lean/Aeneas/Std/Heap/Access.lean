module

public import Aeneas.Std.Heap.Borrowing
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

/-! Cross-type safety follows from canonical byte permissions. Layout framing concerns
disjoint byte intervals, not equality of differently typed indices. -/

@[expose] public section

namespace Aeneas.Std

universe u

namespace Heap

variable {m : Layout.{u}}

theorem decode_none_of_permission_conflict {ty : Type u} {r : m.Repr}
    {i a b : Nat}
    (ha : i * m.byteLength ty ≤ a ∧ a < (i + 1) * m.byteLength ty)
    (hb : i * m.byteLength ty ≤ b ∧ b < (i + 1) * m.byteLength ty)
    (hp : m.permission r a ≠ m.permission r b) :
    m.decode ty r i = none := by
  cases he : m.decode ty r i
  · rfl
  · rename_i c
    have hv := Layout.decode_eq_some.mp he
    exact (hp ((m.view_permission _ _ _ _ hv a ha.1 ha.2).trans
      (m.view_permission _ _ _ _ hv b hb.1 hb.2).symm)).elim

theorem read_iff_observe {s s' : Heap m.Repr} {p : RawPtr ty} {value : ty} :
    read m p s value s' ↔
      ((observe m s p).bind Cell.read = some value) ∧ s' = s := by
  constructor
  · rintro ⟨⟨r, depth, hs, hv⟩, rfl⟩
    have hd := Layout.decode_eq_some.mpr hv
    exact ⟨by simp [observe, hs, hd, Cell.read], rfl⟩
  · rintro ⟨hv, rfl⟩
    obtain ⟨c, hc, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨r, hs, hc⟩ := Option.bind_eq_some_iff.mp hc
    have hcell := Layout.decode_eq_some.mp hc
    cases c
    · rename_i depth x _
      have he := Option.some.inj hv
      subst x
      exact ⟨⟨r, depth, hs, hcell⟩, rfl⟩
    · simp [Cell.read] at hv
    · simp [Cell.read] at hv

theorem read.bytes {s s' : Heap m.Repr} {p : RawPtr ty} {value : ty}
    (hr : read m p s value s') (codec : ByteCodec ty) (hc : m.Realizes ty codec) :
    ∃ r, s.cells p.base = some r ∧ codec.supports value ∧
      ((m.bytes r).drop (p.index * codec.byteLength)).take codec.byteLength =
        codec.encode value := by
  obtain ⟨⟨r, depth, hs, hv⟩, _⟩ := hr
  exact ⟨r, hs, hc.2 r p.index depth value hv⟩

theorem write.bytes {s s' : Heap m.Repr} {p : RawPtr ty} {value : ty}
    (hw : write m p value s () s') (codec : ByteCodec ty) (hc : m.Realizes ty codec) :
    ∃ r, s'.cells p.base = some r ∧ codec.supports value ∧
      ((m.bytes r).drop (p.index * codec.byteLength)).take codec.byteLength =
        codec.encode value := by
  obtain ⟨r, r', _, _, hu, rfl⟩ := hw
  exact ⟨r', by simp, hc.2 r' p.index 0 value (m.set_view _ _ _ _ _ hu)⟩

@[simp] theorem writeBack_none (p : RawPtr ty) (s s' : Heap m.Repr) :
    writeBack m p none s s' ↔ s' = s := Iff.rfl

/-- Even a same-value write is denied if any byte in its footprint is protected. -/
theorem write.denied_by_byte {s s' : Heap m.Repr} {p : RawPtr ty} {r : m.Repr}
    (hs : s.cells p.base = some r) (b : Nat)
    (hlo : p.index * m.byteLength ty ≤ b) (hhi : b < (p.index + 1) * m.byteLength ty)
    (permission : Permission) (hp : m.permission r b = some permission)
    (hn : ¬ permission.writable) (value : ty) : ¬ write m p value s () s' := by
  rintro ⟨r₀, _, hs₀, hw, _⟩
  have he : r₀ = r := Option.some.inj (hs₀.symm.trans hs)
  subst r₀
  obtain ⟨p', hp', hw'⟩ := hw.2.1 b hlo hhi
  have he := Option.some.inj (hp'.symm.trans hp)
  exact hn (he ▸ hw')

theorem read.denied_by_byte {s s' : Heap m.Repr} {p : RawPtr ty} {r : m.Repr}
    (hs : s.cells p.base = some r) (b : Nat)
    (hlo : p.index * m.byteLength ty ≤ b) (hhi : b < (p.index + 1) * m.byteLength ty)
    (permission : Permission) (hp : m.permission r b = some permission)
    (hn : ∀ depth, permission ≠ .shared depth) (value : ty) :
    ¬ read m p s value s' := by
  rintro ⟨⟨r₀, depth, hs₀, hv⟩, _⟩
  have he : r₀ = r := Option.some.inj (hs₀.symm.trans hs)
  subst r₀
  have hp' := m.view_permission _ _ _ _ hv b hlo hhi
  exact hn depth (Option.some.inj (hp.symm.trans hp'))

theorem write.preserves_disjoint {s s' : Heap m.Repr} {p : RawPtr T} {value : T}
    (hw : write m p value s () s') (q : RawPtr U)
    (hd : p.base ≠ q.base ∨ CellsDisjoint m.byteLength T p.index U q.index) :
    observe m s' q = observe m s q := by
  obtain ⟨r, r', hs, _, hu, rfl⟩ := hw
  by_cases hb : q.base = p.base
  · have hdis : CellsDisjoint m.byteLength T p.index U q.index := by
      rcases hd with hne | hdis
      · exact (hne hb.symm).elim
      · exact hdis
    simpa [observe, storeRepr, update, hb, hs] using Layout.set_decode_frame hu hdis
  · simp [observe, storeRepr, update, hb]

/-- Integer stores invalidate overlapping pointer observations, independently of bit equality. -/
theorem write.invalidates_pointer {s s' : Heap m.Repr} {p : RawPtr T} {value : T}
    (hw : write m p value s () s') (q : RawPtr U) (hb : q.base = p.base)
    (hint : m.kind T = .integer) (hptr : m.kind U = .pointer)
    (hoverlap : ¬ CellsDisjoint m.byteLength T p.index U q.index) :
    observe m s' q = none := by
  obtain ⟨r, r', _, _, hu, rfl⟩ := hw
  have hn : m.decode U r' q.index = none := by
    cases he : m.decode U r' q.index
    · rfl
    · rename_i c
      exact (m.set_integer_pointer _ _ _ _ _ _ hu hint U q.index hptr hoverlap c
        (Layout.decode_eq_some.mp he)).elim
  simp [observe, storeRepr, update, hb, hn]

/-- A borrowed marker cannot be decoded and restored through an overlapping different type. -/
theorem endBorrowRange.denied_other_type {s s' : Heap m.Repr}
    {T U : Type u} {i : Nat} {r r' : m.Repr}
    (hu : m.setCell T i (some .borrowed) r r') (q : RawPtr U)
    (hs : s.cells q.base = some r') (ht : T ≠ U)
    (hoverlap : ¬ CellsDisjoint m.byteLength T i U q.index)
    (values : List U) (hne : values ≠ []) :
    ¬ endBorrowRange m q values s () s' := by
  have ho : List.replicate values.length (.borrowed : Cell U) ≠ [] := by simpa using hne
  rintro h
  obtain ⟨_, actual, _, ha, hv, _⟩ := (ite_eq_right ho).mp h
  have he : actual = r' := Option.some.inj (ha.symm.trans hs)
  subst actual
  have hi : 0 < (List.replicate values.length (.borrowed : Cell U)).length := by
    simpa using List.length_pos_iff.mpr hne
  have hv₀ := hv 0 hi
  exact m.set_borrow_type _ _ _ _ hu U q.index ht hoverlap .borrowed (by simpa using hv₀)

theorem freeBlock.denied_by_byte {s s' : Heap m.Repr} {p : RawPtr ty} {r : m.Repr}
    (hs : s.cells p.base = some r) (b : Nat) (hb : b < (m.bytes r).length)
    (permission : Permission) (hp : m.permission r b = some permission)
    (hn : ¬ permission.writable) (count : Nat) (own : Bool) :
    ¬ freeBlock m p count own s () s' := by
  rintro ⟨_, _, ⟨cs, ⟨r', hs', _, hv, hbytes⟩, _, hw⟩, _⟩
  have he : r' = r := Option.some.inj (hs'.symm.trans hs)
  subst r'
  have hsize : 0 < m.byteLength ty := by grind
  have hi : b / m.byteLength ty < cs.length :=
    (Nat.div_lt_iff_lt_mul hsize).mpr (by simpa [hbytes] using hb)
  have hv₀ := hv (b / m.byteLength ty) hi
  have hlo : (b / m.byteLength ty) * m.byteLength ty ≤ b := Nat.div_mul_le_self _ _
  have hhi : b < (b / m.byteLength ty + 1) * m.byteLength ty := by
    have hmod := Nat.mod_lt b hsize
    have hdiv := Nat.mod_add_div b (m.byteLength ty)
    grind
  have hp' := m.view_permission _ _ _ _ hv₀ b (by simpa using hlo) (by simpa using hhi)
  have he := Option.some.inj (hp.symm.trans hp')
  exact hn (he.symm ▸ hw cs[b / m.byteLength ty] (List.getElem_mem hi))

end Heap

namespace SepLogic

variable {m : Layout.{u}}

theorem read.denied {s s' : Heap m.Repr} {p : RawPtr ty} {cell : Cell ty}
    (hm : Fragment.Matches m s (cellsHeap p [cell])) (hc : cell.read = none)
    (value : ty) : ¬ Heap.read m p s value s' := by
  obtain ⟨r, hs, hv⟩ := matches_cellsHeap.mp hm 0 (by simp)
  rintro ⟨⟨r', depth, hs', hv'⟩, _⟩
  have he : r' = r := Option.some.inj (hs'.symm.trans hs)
  subst r'
  have hv₀ : m.view ty r p.index cell := by simpa using hv
  have hcell := m.view_unique _ _ _ _ _ hv₀ hv'
  simp [hcell, Cell.read] at hc

theorem write.denied {s s' : Heap m.Repr} {p : RawPtr ty} {cell : Cell ty}
    (hm : Fragment.Matches m s (cellsHeap p [cell])) (hc : ¬ cell.writable)
    (value : ty) : ¬ Heap.write m p value s () s' := by
  obtain ⟨r, hs, hv⟩ := matches_cellsHeap.mp hm 0 (by simp)
  rintro ⟨r', _, hs', hw, _⟩
  have he : r' = r := Option.some.inj (hs'.symm.trans hs)
  subst r'
  exact hc (hw.2.2 cell (by simpa using hv))

theorem freeBlock.denied {s s' : Heap m.Repr} {p q : RawPtr ty} {cell : Cell ty}
    (hm : Fragment.Matches m s (cellsHeap p [cell])) (hc : ¬ cell.writable)
    (hb : q.base = p.base) (count : Nat) (own : Bool) :
    ¬ Heap.freeBlock m q count own s () s' := by
  obtain ⟨r, hs, hv⟩ := matches_cellsHeap.mp hm 0 (by simp)
  have hv₀ : m.view ty r p.index cell := by simpa using hv
  rintro ⟨_, _, ⟨cs, ⟨r', hs', hn, hcs, _⟩, _, hw⟩, _⟩
  have he : r' = r := by
    rw [hb] at hs'
    exact Option.some.inj (hs'.symm.trans hs)
  subst r'
  have hi : p.index < cs.length := by simpa [hn] using m.view_bound _ _ _ _ hv₀
  have hv' : m.view ty r p.index cs[p.index] := by simpa using hcs p.index hi
  have he := m.view_unique _ _ _ _ _ hv₀ hv'
  exact hc (he ▸ hw cs[p.index] (List.getElem_mem hi))

end SepLogic
end Aeneas.Std
