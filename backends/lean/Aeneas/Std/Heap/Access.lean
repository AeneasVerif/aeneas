module

public import Aeneas.Std.Heap.Borrowing
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

/-! Cross-type safety follows from canonical byte permissions. Framing concerns
disjoint byte intervals, not equality of differently typed indices. -/

@[expose] public section

namespace Aeneas.Std

universe u

namespace Heap

theorem decode_none_of_depth_conflict {ty : Type u} {r : Std.Block.{u}}
    {i a b : Nat}
    (ha : i * Heap.size ty ≤ a ∧ a < (i + 1) * Heap.size ty)
    (hb : i * Heap.size ty ≤ b ∧ b < (i + 1) * Heap.size ty)
    (hp : ((Std.Block.bytes r)[a]?).map Cell.depth ≠ ((Std.Block.bytes r)[b]?).map Cell.depth) :
    Std.Block.decode ty r i = none := by
  cases he : Std.Block.decode ty r i
  · rfl
  · rename_i c
    have hv := Std.Block.decode_eq_some.mp he
    exact (hp ((Std.Block.view_depth hv ha.1 ha.2).trans
      (Std.Block.view_depth hv hb.1 hb.2).symm)).elim

theorem read_iff_observe {s s' : Heap Std.Block.{u}} {p : RawPtr ty} {value : ty} :
    read p s value s' ↔
      ((observe s p).bind Cell.read = some value) ∧ s' = s := by
  constructor
  · rintro ⟨⟨r, depth, hs, ha, hv⟩, rfl⟩
    have hd := Std.Block.decode_eq_some.mpr hv
    exact ⟨by simp [observe, hs, ha, hd, Cell.read], rfl⟩
  · rintro ⟨hv, he⟩
    subst s'
    classical
    have ha : Aligned ty s p.base := by
      by_cases ha : Aligned ty s p.base
      · exact ha
      · simp [observe, ha] at hv
    have hv : ((s.cells p.base).bind fun r => Std.Block.decode ty r p.index).bind Cell.read =
        some value := by simpa [observe, ha] using hv
    obtain ⟨c, hc, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨r, hs, hc⟩ := Option.bind_eq_some_iff.mp hc
    have hcell := Std.Block.decode_eq_some.mp hc
    cases c
    · rename_i depth x _
      change x = some value at hv
      subst x
      exact ⟨⟨r, depth, hs, ha, hcell⟩, rfl⟩
    · simp [Cell.read] at hv

theorem read.bytes {s s' : Heap Std.Block.{u}} {p : RawPtr ty} {value : ty}
    (hr : read p s value s') (hc : Std.Block.Realizes ty) :
    ∃ r, s.cells p.base = some r ∧ (repr ty).supports value ∧
      (((Std.Block.bytes r).drop (p.index * size ty)).take (size ty)).map Cell.read =
        ((repr ty).encode value).map some := by
  obtain ⟨⟨r, depth, hs, _, hv⟩, _⟩ := hr
  exact ⟨r, hs, hc r p.index depth value hv⟩

theorem write.bytes {s s' : Heap Std.Block.{u}} {p : RawPtr ty} {value : ty}
    (hw : write p value s () s') (hc : Std.Block.Realizes ty) :
    ∃ r, s'.cells p.base = some r ∧ (repr ty).supports value ∧
      (((Std.Block.bytes r).drop (p.index * size ty)).take (size ty)).map Cell.read =
        ((repr ty).encode value).map some := by
  obtain ⟨r, r', hs, _, _, hu, rfl⟩ := hw
  exact ⟨r', by simp [hs], hc r' p.index 0 value (Std.Block.set_view _ _ _ _ _ hu)⟩

@[simp] theorem writeBack_none (p : RawPtr ty) (s s' : Heap Std.Block.{u}) :
    writeBack p none s s' ↔ s' = s := Iff.rfl

/-- Even a same-value write is denied if any byte in its footprint is protected. -/
theorem write.denied_by_byte {s s' : Heap Std.Block.{u}} {p : RawPtr ty} {r : Std.Block.{u}}
    (hs : s.cells p.base = some r) (b : Nat)
    (hlo : p.index * Heap.size ty ≤ b) (hhi : b < (p.index + 1) * Heap.size ty)
    (byte : Cell U8) (hp : (Std.Block.bytes r)[b]? = some byte)
    (hn : ¬ byte.writable) (value : ty) : ¬ write p value s () s' := by
  rintro ⟨r₀, _, hs₀, _, hw, _⟩
  have he : r₀ = r := Option.some.inj (hs₀.symm.trans hs)
  subst r₀
  obtain ⟨p', hp', hw'⟩ := hw.2.1 b hlo hhi
  have he := Option.some.inj (hp'.symm.trans hp)
  exact hn (he ▸ hw')

theorem read.denied_by_byte {s s' : Heap Std.Block.{u}} {p : RawPtr ty} {r : Std.Block.{u}}
    (hs : s.cells p.base = some r) (b : Nat)
    (hlo : p.index * Heap.size ty ≤ b) (hhi : b < (p.index + 1) * Heap.size ty)
    (byte : Cell U8) (hp : (Std.Block.bytes r)[b]? = some byte)
    (hn : byte.read = none) (value : ty) :
    ¬ read p s value s' := by
  rintro ⟨⟨r₀, depth, hs₀, _, hv⟩, _⟩
  have he : r₀ = r := Option.some.inj (hs₀.symm.trans hs)
  subst r₀
  obtain ⟨byte', hp', _, hread⟩ := Std.Block.view_bytes _ _ _ _ hv b hlo hhi
  have he : byte' = byte := Option.some.inj (hp'.symm.trans hp)
  subst byte'
  exact hread (by simp [Cell.read]) hn

theorem write.preserves_disjoint {s s' : Heap Std.Block.{u}} {p : RawPtr T} {value : T}
    (hw : write p value s () s') (q : RawPtr U)
    (hd : p.base ≠ q.base ∨ CellsDisjoint T p.index U q.index) :
    observe s' q = observe s q := by
  obtain ⟨r, r', hs, _, _, hu, rfl⟩ := hw
  have halign := propext (aligned_storeRepr s p.base q.base r' U)
  unfold observe
  rw [halign]
  by_cases hb : q.base = p.base
  · have hdis : CellsDisjoint T p.index U q.index := by
      rcases hd with hne | hdis
      · exact (hne hb.symm).elim
      · exact hdis
    have he := Std.Block.set_decode_frame hu hdis
    simp [hb, hs, he]
  · simp [hb]

/-- Differently typed stores invalidate overlapping pointer views, independently of bit equality. -/
theorem write.invalidates_pointer {s s' : Heap Std.Block.{u}} {p : RawPtr T} {value : T}
    (hw : write p value s () s') (q : RawPtr (RawPtr U)) (hb : q.base = p.base)
    (ht : T ≠ RawPtr U)
    (hoverlap : ¬ CellsDisjoint T p.index (RawPtr U) q.index) :
    observe s' q = none := by
  obtain ⟨r, r', hs, _, _, hu, rfl⟩ := hw
  have hn : Std.Block.decode (RawPtr U) r' q.index = none := by
    cases he : Std.Block.decode (RawPtr U) r' q.index
    · rfl
    · rename_i c
      exact (Std.Block.set_pointer _ _ _ _ _ hu U q.index ht hoverlap c
        (Std.Block.decode_eq_some.mp he)).elim
  simp [observe, hb, hs, hn]

/-- A borrowed marker cannot be decoded and restored through an overlapping different type. -/
theorem endBorrowRange.denied_other_type {s s' : Heap Std.Block.{u}}
    {T U : Type u} {i : Nat} {r r' : Std.Block.{u}}
    (hu : Std.Block.setCell T i (some .borrowed) r r') (q : RawPtr U)
    (hs : s.cells q.base = some r') (ht : T ≠ U)
    (hoverlap : ¬ CellsDisjoint T i U q.index)
    (values : List U) (hne : values ≠ []) :
    ¬ endBorrowRange q values s () s' := by
  have ho : List.replicate values.length (.borrowed : Cell U) ≠ [] := by simpa using hne
  rintro h
  obtain ⟨_, actual, _, ha, _, hv, _⟩ := (ite_eq_right ho).mp h
  have he : actual = r' := Option.some.inj (ha.symm.trans hs)
  subst actual
  have hi : 0 < (List.replicate values.length (.borrowed : Cell U)).length := by
    simpa using List.length_pos_iff.mpr hne
  have hv₀ := hv 0 hi
  exact Std.Block.set_borrow_type _ _ _ _ hu U q.index ht hoverlap .borrowed (by simpa using hv₀)

theorem freeBlock.denied_by_byte {s s' : Heap Std.Block.{u}} {p : RawPtr ty} {r : Std.Block.{u}}
    (hs : s.cells p.base = some r) (b : Nat) (hb : b < (Std.Block.bytes r).length)
    (byte : Cell U8) (hp : (Std.Block.bytes r)[b]? = some byte)
    (hn : ¬ byte.writable) (count : Nat) (own : Bool) :
    ¬ freeBlock p count own s () s' := by
  rintro ⟨_, _, ⟨cs, ⟨r', hs', _, _, hv, hbytes⟩, _, hw⟩, _⟩
  have he : r' = r := Option.some.inj (hs'.symm.trans hs)
  subst r'
  have hsize : 0 < Heap.size ty := by grind
  have hi : b / Heap.size ty < cs.length :=
    (Nat.div_lt_iff_lt_mul hsize).mpr (by simpa [hbytes] using hb)
  have hv₀ := hv (b / Heap.size ty) hi
  have hlo : (b / Heap.size ty) * Heap.size ty ≤ b := Nat.div_mul_le_self _ _
  have hhi : b < (b / Heap.size ty + 1) * Heap.size ty := by
    have hmod := Nat.mod_lt b hsize
    have hdiv := Nat.mod_add_div b (Heap.size ty)
    grind
  obtain ⟨byte', hp', hd, _⟩ := Std.Block.view_bytes _ _ _ _ hv₀ b
    (by simpa using hlo) (by simpa using hhi)
  have he : byte' = byte := Option.some.inj (hp'.symm.trans hp)
  subst byte'
  exact hn (hd.trans (hw cs[b / Heap.size ty] (List.getElem_mem hi)))

end Heap

namespace SepLogic

theorem read.denied {s s' : Heap Std.Block.{u}} {p : RawPtr ty} {cell : Cell ty}
    (hm : Fragment.Matches s (cellsHeap p [cell])) (hc : cell.read = none)
    (value : ty) : ¬ Heap.read p s value s' := by
  obtain ⟨r, hs, _, hv⟩ := matches_cellsHeap.mp hm 0 (by simp)
  rintro ⟨⟨r', depth, hs', _, hv'⟩, _⟩
  have he : r' = r := Option.some.inj (hs'.symm.trans hs)
  subst r'
  have hv₀ : Std.Block.view ty r p.index cell := by simpa using hv
  have hcell := Std.Block.view_unique _ _ _ _ _ hv₀ hv'
  simp [hcell, Cell.read] at hc

theorem write.denied {s s' : Heap Std.Block.{u}} {p : RawPtr ty} {cell : Cell ty}
    (hm : Fragment.Matches s (cellsHeap p [cell])) (hc : ¬ cell.writable)
    (value : ty) : ¬ Heap.write p value s () s' := by
  obtain ⟨r, hs, _, hv⟩ := matches_cellsHeap.mp hm 0 (by simp)
  rintro ⟨r', _, hs', _, hw, _⟩
  have he : r' = r := Option.some.inj (hs'.symm.trans hs)
  subst r'
  exact hc (hw.2.2 cell (by simpa using hv))

theorem freeBlock.denied {s s' : Heap Std.Block.{u}} {p q : RawPtr ty} {cell : Cell ty}
    (hm : Fragment.Matches s (cellsHeap p [cell])) (hc : ¬ cell.writable)
    (hb : q.base = p.base) (count : Nat) (own : Bool) :
    ¬ Heap.freeBlock q count own s () s' := by
  obtain ⟨r, hs, _, hv⟩ := matches_cellsHeap.mp hm 0 (by simp)
  have hv₀ : Std.Block.view ty r p.index cell := by simpa using hv
  rintro ⟨_, _, ⟨cs, ⟨r', hs', _, hn, hcs, _⟩, _, hw⟩, _⟩
  have he : r' = r := by
    rw [hb] at hs'
    exact Option.some.inj (hs'.symm.trans hs)
  subst r'
  have hi : p.index < cs.length := by simpa [hn] using Std.Block.view_bound _ _ _ _ hv₀
  have hv' : Std.Block.view ty r p.index cs[p.index] := by simpa using hcs p.index hi
  have he := Std.Block.view_unique _ _ _ _ _ hv₀ hv'
  exact hc (he ▸ hw cs[p.index] (List.getElem_mem hi))

end SepLogic
end Aeneas.Std
