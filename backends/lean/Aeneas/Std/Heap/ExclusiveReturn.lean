module

public import Aeneas.Std.Heap.RangeRestoration
public import Aeneas.Std.Heap.Allocation
import all Aeneas.Std.Heap.Lemmas
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Allocation
import all Aeneas.Std.Heap.RangeRestoration

@[expose] public section

namespace Aeneas.Std.Heap

/-- Active views of distinct physical roots cannot overlap. -/
theorem Inv.separate_roots {s : Heap} (hi : s.Inv)
    {i j : Nat} {a b : Block} (ha : s.allocations i = some a)
    (hb : s.allocations j = some b) (activeA : a.active = true)
    (activeB : b.active = true) (different : a.root ≠ b.root) :
    a.bptr.val + a.repr.length ≤ b.bptr.val ∨
      b.bptr.val + b.repr.length ≤ a.bptr.val := by
  have va := hi.validBlock ha
  have vb := hi.validBlock hb
  cases hra : s.allocations a.root
  · simp [Heap.validBlock, hra] at va
  · rename_i ra
    cases hrb : s.allocations b.root
    · simp [Heap.validBlock, hrb] at vb
    · rename_i rb
      simp only [Heap.validBlock, hra, hrb, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq, activeA, activeB, Bool.not_true, Bool.false_or] at va vb
      have row := List.all_eq_true.mp hi.2 a.root (List.mem_range.mpr (hi.base_lt hra))
      simp only [hra, Bool.and_eq_true] at row
      have pair := List.all_eq_true.mp row.2 b.root (List.mem_range.mpr (hi.base_lt hrb))
      simp [different, hrb, overlaps] at pair
      grind

theorem storeRepr_exclusive_Inv {s : Heap} {id : Nat} {blk : Block}
    (hi : s.Inv) (hl : s.allocations id = some blk)
    (active : blk.active = true) (aliases : s.noAliases id blk.root = true)
    (bytes : List Cell) (length : bytes.length = blk.repr.length)
    (valid : ∀ depth byte, Cell.shared depth byte ∈ bytes → validByte s byte = true) :
    (s.storeRepr id bytes).Inv := by
  have length' : ∀ old, s.allocations id = some old → bytes.length = old.repr.length := by
    intro old ho
    have he := Option.some.inj (ho.symm.trans hl)
    simpa [he] using length
  have vb : validBlock s { blk with repr := bytes } = true := by
    have original := hi.validBlock hl
    simp only [validBlock, Bool.and_eq_true] at original ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [bounded, length] using original.1.1
    · simpa [length] using original.1.2
    · apply List.all_eq_true.mpr
      intro cell hc
      cases cell
      · exact valid _ _ hc
      · rfl
  have compat : ∀ otherId other, s.allocations otherId = some other → otherId ≠ id →
      compatible { blk with repr := bytes } other = true := by
    intro otherId other lookup different
    rw [compatible_iff]
    cases act : other.active
    · exact .inr (.inl rfl)
    · have roots : blk.root ≠ other.root := by
        intro same
        exact different (hi.noAliases_unique aliases lookup act same.symm)
      have separate := hi.separate_roots hl lookup active act roots
      refine .inr (.inr ?_)
      intro i boundI j boundJ address
      simp only [length] at boundI
      grind
  refine ⟨storeRepr_support s id bytes hi (hi.base_lt hl), ?_⟩
  apply List.all_eq_true.mpr
  intro i memI
  have row := List.all_eq_true.mp hi.2 i memI
  cases ha : s.allocations i
  · simp [ha] at row
  · rename_i a
    simp only [ha, Bool.and_eq_true] at row
    have vi : validBlock (s.storeRepr id bytes)
        (if i = id then { a with repr := bytes } else a) = true := by
      rw [validBlock_storeRepr _ _ _ _ length']
      split
      · rename_i he
        have he' : a = blk := Option.some.inj ((he ▸ ha).symm.trans hl)
        simpa [he'] using vb
      · exact row.1
    by_cases he : i = id
    · have he' : a = blk := Option.some.inj ((he ▸ ha).symm.trans hl)
      subst i
      subst a
      simp only [allocations_storeRepr, ↓reduceIte, hl, Option.map_some, Bool.and_eq_true]
      refine ⟨by simpa using vi, ?_⟩
      apply List.all_eq_true.mpr
      intro j memJ
      by_cases same : id = j
      · simp [same]
      · have pair := List.all_eq_true.mp row.2 j memJ
        cases hb : s.allocations j
        · simp [same, hb] at pair
        · rename_i b
          simp only [same, ↓reduceIte, hb, Bool.and_eq_true] at pair
          simpa [same, Ne.symm same, hb, length, overlaps] using
            And.intro pair.1 (compat j b hb (Ne.symm same))
    · simp only [allocations_storeRepr, he, ↓reduceIte, ha, Bool.and_eq_true]
      refine ⟨by simpa [he] using vi, ?_⟩
      apply List.all_eq_true.mpr
      intro j memJ
      by_cases same : i = j
      · simp [same]
      · have pair := List.all_eq_true.mp row.2 j memJ
        cases hb : s.allocations j
        · simp [same, hb] at pair
        · rename_i b
          simp only [same, ↓reduceIte, hb, Bool.and_eq_true] at pair
          by_cases atId : j = id
          · have eq : b = blk := Option.some.inj ((atId ▸ hb).symm.trans hl)
            subst j
            subst b
            have hc := compat i a ha he
            rw [compatible_symm] at hc
            simpa [same, hl, length, overlaps] using And.intro pair.1 hc
          · simpa [same, atId, hb] using pair

end Aeneas.Std.Heap

namespace Aeneas.Std.HeapWP

open SepLogic

/-- A full-root owner with no active aliases may finish a suspended borrow.
    Unlike the captured-state rule, this remains usable after nested exposures
    have been retired. Borrowed cells alone still do not suffice. -/
theorem endBorrowRange_exclusive.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (s : Heap) (authority : RootReturn s p.provenance)
    (noPointers : ∀ i : Fin count, ∀ q, ¬ repr.Carries values[i.val] q)
    (hcount : 0 < count) (hsize : 0 < repr.size) :
    TripleAt (block repr p bptr (List.replicate (count * repr.size) .borrowed))
      (RawPtr.endBorrowRange repr p values.toList)
      (fun _ => pointsToRange repr p bptr values) s := by
  intro h F hp hd hm hi
  obtain ⟨lower, aligned, hh⟩ := hp
  have matched : Fragment.Matches s
      (cellsHeap bptr p.provenance (p.offsetFrom bptr)
        (Vector.replicate (count * repr.size) Cell.borrowed).toList) := by
    simpa [hh] using ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨blk, hb, hl, live, base, selected⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
      (Nat.mul_pos hcount hsize) matched
  subst bptr
  change p.offsetFrom blk.bptr + count * repr.size ≤ blk.repr.length at hb
  change s.allocations p.provenance = some blk at hl
  change (repr.region count).select blk.bytes (p.offsetFrom blk.bptr) hb =
    Vector.replicate (count * repr.size) Cell.borrowed at selected
  obtain ⟨root, hr, rootBase, rootLength, aliases⟩ := authority blk hl
  have active : blk.active = true := by
    simp only [Heap.live, Bool.and_eq_true] at live
    exact live.1
  obtain ⟨encodings, encoded⟩ := repr.encodeList_complete values.toList
  have length : encodings.length = count := by
    simpa using encodeList_length repr values.toList encodings encoded
  let data : Vector (Vector Byte repr.size) count := ⟨encodings.toArray, by simp [length]⟩
  have dataList : data.toList = encodings := by simp [data]
  have each : ∀ i : Fin count, repr.encode values[i.val] data[i.val] := by
    intro i
    simpa [data] using encodeList_get repr values.toList encodings encoded i.val
      (by simp) (by simp [length])
  let new := data.flatMap (fun bytes => bytes.map (Cell.shared 0))
  let restored := (repr.region count).update blk.bytes (p.offsetFrom blk.bptr) hb new
  have newValid : ∀ cell ∈ new.toList, match cell with
      | .borrowed => True
      | .shared _ byte => s.validByte byte = true := by
    intro cell member
    obtain ⟨i, bound, rfl⟩ := List.getElem_of_mem member
    have bound' : i < count * repr.size := by simpa [new] using bound
    have outer : i / repr.size < count :=
      Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using bound')
    have inner : i % repr.size < repr.size := Nat.mod_lt _ hsize
    simp only [Vector.getElem_toList, new, Vector.getElem_flatMap, Vector.getElem_map]
    exact valid_encoding (each ⟨i / repr.size, outer⟩)
      (fun q carried => (noPointers ⟨i / repr.size, outer⟩ q carried).elim) _ inner
  have valid : (s.storeRepr p.provenance restored.toList).Inv := by
    apply Heap.storeRepr_exclusive_Inv hi hl active aliases restored.toList (by simp [restored])
    intro depth byte member
    let cell := Cell.shared depth byte
    change cell ∈ ((repr.region count).update blk.bytes (p.offsetFrom blk.bptr) hb new).toList at member
    have updated := Repr.update_toList (repr.region count) blk.bytes (p.offsetFrom blk.bptr) hb new
    have member := (congrArg (fun cells => cell ∈ cells) updated).mp member
    simp only [List.mem_append] at member
    rcases member with (old | replacement) | old
    · have mem := List.mem_of_mem_take old
      obtain ⟨i, bound, eq⟩ := List.getElem_of_mem mem
      have vc := hi.validCell hl i (by simpa [Block.bytes] using bound)
      have hc : blk.repr[i] = Cell.shared depth byte := by
        change blk.repr[i] = Cell.shared depth byte at eq
        exact eq
      simpa only [hc] using vc
    · exact newValid cell replacement
    · have mem := List.mem_of_mem_drop old
      obtain ⟨i, bound, eq⟩ := List.getElem_of_mem mem
      have vc := hi.validCell hl i (by simpa [Block.bytes] using bound)
      have hc : blk.repr[i] = Cell.shared depth byte := by
        change blk.repr[i] = Cell.shared depth byte at eq
        exact eq
      simpa only [hc] using vc
  have run : Heap.endBorrowRange repr p encodings s =
      some (s.storeRepr p.provenance restored.toList) := by
    rw [← dataList]
    simp [Heap.endBorrowRange, Heap.modify, hl, live, lower, aligned, hsize, hb]
    rw [endBorrowRange_update repr data blk.bytes _ hb selected hsize]
    exact show Heap.commit (s.storeRepr p.provenance restored.toList) = _ from by
      simp [Heap.commit, valid.2]
  exact endBorrowRange.spec repr p blk.bptr values s hcount hsize
    ⟨_, encodings, encoded, run⟩ h F ⟨lower, aligned, hh⟩ hd hm hi

end Aeneas.Std.HeapWP
