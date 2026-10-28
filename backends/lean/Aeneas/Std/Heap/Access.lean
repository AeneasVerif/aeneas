module

public import Aeneas.Std.Heap.Borrowing
public import Mathlib.Data.List.Forall2
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

/-! Observable consequences of the cross-view laws and access-denial checks.
No concrete representation, type-size function, or cross-type index correspondence
is used. The laws concern raw data updates, not privileged permission restoration. -/

@[expose] public section

namespace Aeneas.Std

universe u

theorem Cell.readEquivalent_refl (c : Cell ty) : c.ReadEquivalent c := by
  cases c
  · rename_i fraction value
    cases fraction
    · trivial
    · exact ⟨rfl, rfl⟩
  · trivial

namespace Heap

variable {m : Layout.{u}}

/-- Authorized heap observation, with missing, out-of-bounds, and unreadable cells hidden. -/
def observe (m : Layout.{u}) (s : Heap m.Repr) (p : RawPtr ty) : Option ty :=
  (s.load m.interpret ty p.base).bind fun cs => cs[p.offset]?.bind Cell.read

open SepLogic in
theorem read_iff_observe {s s' : Heap m.Repr} {p : RawPtr ty} {value : ty} :
    read m p s value s' ↔ observe m s p = some value ∧ s' = s := by
  constructor
  · rintro ⟨⟨before, after, f, hoff, hs⟩, rfl⟩
    have hm := matches_segment p before [.val (some f) value] after hoff hs
    obtain ⟨actual, ha, hv⟩ := matches_cellsHeap.mp hm 0 (by simp)
    have hv' : actual[p.offset]? = some (.val (some f) value) := by simpa using hv
    exact ⟨by simp [observe, ha, hv', Cell.read], rfl⟩
  · rintro ⟨hv, hstate⟩
    subst s'
    obtain ⟨cs, hcs, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨cell, hcell, hv⟩ := Option.bind_eq_some_iff.mp hv
    cases cell
    · rename_i fraction x
      cases fraction
      · simp [Cell.read] at hv
      · rename_i f
        have hx : x = value := Option.some.inj hv
        subst x
        have hm : Fragment.Matches m s (cellsHeap p [.val (some f) value]) := by
          apply matches_cellsHeap.mpr
          intro i hi
          have he : i = 0 := by simp at hi; grind
          subst i
          exact ⟨cs, hcs, by simpa using hcell⟩
        obtain ⟨before, after, hoff, hs⟩ := segment_of_matches (by simp) hm
        exact ⟨⟨before, after, f, hoff, hs⟩, rfl⟩
    · simp [Cell.read] at hv

theorem replaceRange.hidden_reads {s s' : Heap m.Repr} {p : RawPtr T}
    {old new : List (Cell T)} (he : List.Forall₂ Cell.ReadEquivalent old new)
    (hu : replaceRange m s p old new s') (q : RawPtr U) (hb : q.base = p.base) :
    observe m s q = observe m s' q := by
  by_cases hn : old = []
  · have hs : s' = s := ((ite_eq_left hn).mp hu).2
    rw [hs]
  · obtain ⟨_, before, after, _, hs, rfl⟩ := (ite_eq_right hn).mp hu
    have hbefore := List.forall₂_same.mpr (fun c (_ : c ∈ before) => Cell.readEquivalent_refl c)
    have hafter := List.forall₂_same.mpr (fun c (_ : c ∈ after) => Cell.readEquivalent_refl c)
    have hall := List.rel_append (List.rel_append hbefore he) hafter
    cases hr : s.cells p.base
    · simp [Heap.load, hr] at hs
    · rename_i r
      have hs' : m.interpret T r = some (before ++ old ++ after) := by
        simpa [Heap.load, hr] using hs
      have hread := m.readLaw T r _ _ hs' hall U q.offset
      simpa [observe, Heap.load, store, update, hb, hr, readCell] using hread

theorem replaceRange.hidden_read_iff {s s' : Heap m.Repr} {p : RawPtr T}
    {old new : List (Cell T)} (he : List.Forall₂ Cell.ReadEquivalent old new)
    (hu : replaceRange m s p old new s') (q : RawPtr U) (hb : q.base = p.base)
    (value : U) : read m q s value s ↔ read m q s' value s' := by
  simp [read_iff_observe, hu.hidden_reads he q hb]

/-- A raw write through `U` cannot change a protected `T` cell at the same base. -/
theorem write.preserves_protected {s s' : Heap m.Repr} {p : RawPtr U} {value : U}
    {T : Type u} {cs : List (Cell T)}
    (hs : s.load m.interpret T p.base = some cs)
    (index : Nat) (hi : index < cs.length) (hp : ¬ cs[index].writable)
    (hw : write m p value s () s') :
    (s'.load m.interpret T p.base).bind (fun updated => updated[index]?) = some cs[index] := by
  obtain ⟨old, hwrite, hu⟩ := hw
  obtain ⟨_, before, after, _, hU, rfl⟩ := (ite_eq_right (by simp)).mp hu
  have hbefore : List.Forall₂ Cell.WriteCompatible before before :=
    List.forall₂_same.mpr (fun _ _ => Or.inr rfl)
  have hafter : List.Forall₂ Cell.WriteCompatible after after :=
    List.forall₂_same.mpr (fun _ _ => Or.inr rfl)
  have hcell : Cell.WriteCompatible old (.val (some 0) value) := .inl hwrite
  have hall := List.rel_append
    (List.rel_append hbefore (List.Forall₂.cons hcell .nil)) hafter
  cases hr : s.cells p.base
  · simp [Heap.load, hr] at hs
  · rename_i r
    have hT : m.interpret T r = some cs := by simpa [Heap.load, hr] using hs
    have hU' : m.interpret U r = some (before ++ [old] ++ after) := by
      simpa [Heap.load, hr] using hU
    have hprotected := m.writeLaw U r _ _ hU' hall T cs hT index hi hp
    simpa [Heap.load, store, update] using hprotected

end Heap

namespace SepLogic

variable {m : Layout.{u}}

theorem read.denied {s s' : Heap m.Repr} {p : RawPtr ty} {cell : Cell ty}
    (hm : Fragment.Matches m s (cellsHeap p [cell])) (hc : cell.read = none)
    (value : ty) : ¬ Heap.read m p s value s' := by
  rintro ⟨⟨before, after, f, hoff, hs⟩, _⟩
  have he := segment_unique hm (by simp) hoff hs
  have hcell : cell = .val (some f) value := (List.cons.inj he).1
  simp [hcell, Cell.read] at hc

theorem write.denied {s s' : Heap m.Repr} {p : RawPtr ty} {cell : Cell ty}
    (hm : Fragment.Matches m s (cellsHeap p [cell])) (hc : ¬ cell.writable)
    (value : ty) : ¬ Heap.write m p value s () s' := by
  rintro ⟨old, hw, hu⟩
  have he := replaceRange.old_eq hm (by simp) hu
  have hcell : cell = old := (List.cons.inj he).1
  exact hc (by simpa [hcell] using hw)

theorem freeBlock.denied {s s' : Heap m.Repr} {p q : RawPtr ty} {cell : Cell ty}
    (hm : Fragment.Matches m s (cellsHeap p [cell])) (hc : ¬ cell.writable)
    (hb : q.base = p.base) (count : Nat) (own : Bool) :
    ¬ Heap.freeBlock m q count own s () s' := by
  rintro ⟨_, _, ⟨cs, hs, _, hw⟩, _⟩
  obtain ⟨actual, ha, hv⟩ := matches_cellsHeap.mp hm 0 (by simp)
  have he : actual = cs := by
    rw [hb] at hs
    exact Option.some.inj (ha.symm.trans hs)
  have hcell : cs[p.offset]? = some cell := by simpa [he] using hv
  obtain ⟨hi, hvalue⟩ := List.getElem?_eq_some_iff.mp hcell
  exact hc (hw cell (hvalue ▸ List.getElem_mem hi))

end SepLogic
end Aeneas.Std
