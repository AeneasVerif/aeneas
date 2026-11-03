module

public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Heap.Allocation
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Separation

@[expose] public section

namespace Aeneas.Std

namespace Heap

/-- Physical death retains provenance metadata; it is not view retirement. -/
def killRoot (s : Heap) (root : Nat) : Heap :=
  let allocations := update s.allocations root
    ((s.allocations root).map fun block => { block with alive := false })
  { s with allocations }

@[simp] theorem validByte_killRoot (s : Heap) (root : Nat) (byte : Byte) :
    (s.killRoot root).validByte byte = s.validByte byte := by
  cases byte
  · rfl
  · rfl
  · rename_i p lane
    by_cases he : p.provenance = root
    · simp [validByte, killRoot, update, he]
    · simp [validByte, killRoot, update, he]

theorem killRoot_validBlock (s : Heap) (root : Nat) (blk : Block)
    (valid : s.validBlock blk = true)
    (inactive : blk.root = root → blk.active = false) :
    (s.killRoot root).validBlock blk = true := by
  unfold validBlock at *
  simp only [validByte_killRoot]
  by_cases same : blk.root = root
  · have off := inactive same
    cases hr : s.allocations root
    · simp [same, hr] at valid
    · simpa [killRoot, update, same, off, hr] using valid
  · simpa [killRoot, update, same] using valid

theorem killRoot_Inv {s : Heap} (hi : s.Inv) (root : Nat)
    (inactive : ∀ id blk, s.allocations id = some blk → blk.root = root → blk.active = false) :
    (s.killRoot root).Inv := by
  have lookup (id : Nat) : (s.killRoot root).allocations id =
      (s.allocations id).map (fun blk => if id = root then { blk with alive := false } else blk) := by
    by_cases same : id = root
    · simp [killRoot, update, same]
    · simp [killRoot, update, same]
  constructor
  · intro id bound
    rw [lookup, hi.1 id bound]
    rfl
  · apply List.all_eq_true.mpr
    intro id hid
    have row := List.all_eq_true.mp hi.2 id hid
    cases hl : s.allocations id
    · simp [hl] at row
    · rename_i a
      simp only [hl, Bool.and_eq_true] at row
      rw [lookup, hl]
      simp only [Option.map_some, Bool.and_eq_true]
      constructor
      · have valid := killRoot_validBlock s root a row.1 (inactive id a hl)
        by_cases same : id = root
        · simpa [same, validBlock, bounded] using valid
        · simpa [same] using valid
      · apply List.all_eq_true.mpr
        intro j hj
        by_cases self : id = j
        · simp [self]
        · have entry := List.all_eq_true.mp row.2 j hj
          cases hr : s.allocations j
          · simp [self, hr] at entry
          · rename_i b
            rw [lookup, hr]
            simp only [self, ↓reduceIte, hr, Option.map_some, Bool.and_eq_true] at entry ⊢
            have ca : compatible
                (if id = root then { a with alive := false } else a)
                (if j = root then { b with alive := false } else b) = compatible a b := by
              split
              · split
                · rfl
                · rfl
              · split
                · rfl
                · rfl
            rw [ca]
            refine ⟨?_, entry.2⟩
            by_cases ha : id = root
            · simp [ha]
            · by_cases hb : j = root
              · simp [ha, hb]
              · simpa [ha, hb] using entry.1

theorem noAliases_retire_inactive {s : Heap} (hi : s.Inv) (owner root : Nat)
    (aliases : s.noAliases owner root = true) :
    ∀ id blk, (s.retire owner).allocations id = some blk →
      blk.root = root → blk.active = false := by
  intro id blk hl sameRoot
  by_cases same : id = owner
  · subst id
    cases old : s.allocations owner
    · simp [retire, update, old] at hl
    · simp only [retire, update, ↓reduceIte, old, Option.map_some, Option.some.injEq] at hl
      exact hl ▸ rfl
  · have old : s.allocations id = some blk := by simpa [retire, update, same] using hl
    have allowed := List.all_eq_true.mp aliases id (List.mem_range.mpr (hi.base_lt old))
    simpa [old, same, sameRoot] using allowed

theorem alloc_single_eq (repr : Repr T) (bptr : BasePtr) (s : Heap) :
    Heap.alloc repr 1 bptr s =
      newBlock repr [Vector.replicate repr.size .uninit] true bptr none s := by
  simp [Heap.alloc, newBlock, Repr.create]

theorem returnOwned_retire {repr : Repr T} {p : RawPtr T} {count : Nat} {s₀ s₁ : Heap}
    (run : returnOwned repr p count s₀ = some s₁) : s₁ = s₀.retire p.provenance := by
  unfold returnOwned at run
  cases hl : s₀.allocations p.provenance
  · simp [hl] at run
  · simp only [hl, Bind.bind, Option.bind] at run
    rename_i blk
    cases hr : s₀.allocations blk.root
    · simp [hr] at run
    · simp only [hr] at run
      split at run
      · exact (commit_success _ _ run).1
      · contradiction

/-- Deallocation really marks the physical root dead, while retaining its record. -/
theorem dealloc_kills {repr : Repr T} {p : RawPtr T} {count : Nat} {s₀ s₁ : Heap}
    (run : dealloc repr p count s₀ = some s₁) :
    ∃ view root, s₀.allocations p.provenance = some view ∧
      s₁.allocations view.root = some root ∧ root.alive = false ∧
      s₁.live view = false := by
  unfold dealloc at run
  cases hl : s₀.allocations p.provenance
  · simp [hl] at run
  · rename_i view
    simp only [hl, Bind.bind, Option.bind] at run
    cases returned : returnOwned repr p count s₀
    · simp [returned] at run
    · rename_i s₂
      simp only [returned] at run
      have hs := returnOwned_retire returned
      subst s₂
      have final := (commit_success _ _ run).1
      subst s₁
      have existsRoot : ∃ root, s₀.allocations view.root = some root := by
        unfold returnOwned at returned
        simp only [hl, Bind.bind, Option.bind] at returned
        cases hr : s₀.allocations view.root
        · simp [hr] at returned
        · exact ⟨_, rfl⟩
      obtain ⟨root, hr⟩ := existsRoot
      by_cases same : view.root = p.provenance
      · refine ⟨view, { root with active := false, alive := false }, rfl, ?_, rfl, ?_⟩
        · simp [retire, update, same, show s₀.allocations p.provenance = some root from same ▸ hr]
        · simp [live, retire, update, same, hl]
      · refine ⟨view, { root with alive := false }, rfl, ?_, rfl, ?_⟩
        · simp [retire, update, same, hr]
        · simp [live, retire, update, same, hr]

theorem dealloc_read_rejected {repr : Repr T} {p : RawPtr T} {count : Nat} {s₀ s₁ : Heap}
    (run : dealloc repr p count s₀ = some s₁) (readRepr : Repr U) :
    Heap.read readRepr (p.cast U) s₁ = none := by
  unfold dealloc at run
  cases hl : s₀.allocations p.provenance
  · simp [hl] at run
  · rename_i view
    simp only [hl, Bind.bind, Option.bind] at run
    cases returned : returnOwned repr p count s₀
    · simp [returned] at run
    · rename_i s₂
      simp only [returned] at run
      have hs := returnOwned_retire returned
      subst s₂
      have final := (commit_success _ _ run).1
      subst s₁
      by_cases same : p.provenance = view.root
      · have hl' : s₀.allocations view.root = some view := same ▸ hl
        simp [Heap.read, RawPtr.cast, live, retire, update, same, hl']
      · simp [Heap.read, RawPtr.cast, live, retire, update, same, hl]

end Heap

open SepLogic

namespace SepLogic

theorem matches_killRoot {s : Heap} {root : Nat} {F : Fragment}
    (hm : Fragment.Matches s F)
    (rootSelf : ∀ blk, s.allocations root = some blk → blk.root = root)
    (inactive : ∀ id blk, s.allocations id = some blk → blk.root = root → blk.active = false) :
    Fragment.Matches (s.killRoot root) F := by
  have preserve (id : Nat) (blk : Block) (hl : s.allocations id = some blk)
      (live : s.live blk = true) :
      (s.killRoot root).allocations id = some blk ∧ (s.killRoot root).live blk = true := by
    have active : blk.active = true := by
      simp only [Heap.live, Bool.and_eq_true] at live
      exact live.1
    have different : blk.root ≠ root := by
      intro same
      cases active.symm.trans (inactive id blk hl same)
    have idDifferent : id ≠ root := by
      intro same
      subst id
      exact different (rootSelf blk hl)
    exact ⟨by simpa [Heap.killRoot, update, idDifferent] using hl,
      by simpa [Heap.live, Heap.killRoot, update, different] using live⟩
  intro r hr
  cases r
  · obtain ⟨blk, hl, live, base, cell⟩ := hm _ hr
    obtain ⟨hl', live'⟩ := preserve _ _ hl live
    exact ⟨blk, hl', live', base, cell⟩
  · obtain ⟨blk, hl, len, live, base, owned⟩ := hm _ hr
    obtain ⟨hl', live'⟩ := preserve _ _ hl live
    exact ⟨blk, hl', len, live', base, owned⟩

end SepLogic

namespace HeapWP

/-- A successful physical allocation supplies uninitialized writable bytes,
    cleanup ownership, and root-return authority, but no readable value. -/
theorem allocUninitialized.spec (repr : Repr T) (s₀ : Heap) (F : Fragment)
    (hi : s₀.Inv) (hm : Fragment.Matches s₀ F)
    (feasible : ∃ p s₁, State.allocUninitialized repr 1 s₀ p s₁) :
    Spec (Result.checkedModify (State.allocUninitialized repr 1))
      (fun p s₁ => RootReturn s₁ p.provenance ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧
          sep (alloc repr p p.address 1 true)
            (block repr p p.address (List.replicate repr.size (.shared 0 .uninit))) h) s₀ := by
  apply Spec.checkedModify.mpr
  refine ⟨feasible, ?_⟩
  rintro p s₁ ⟨bptr, run⟩
  rw [Heap.alloc_single_eq] at run
  obtain ⟨_, h, hd, hm₁, hi₁, hp⟩ := newBlock_single.resources repr
    (Vector.replicate repr.size .uninit) true bptr none hi hm run
  exact ⟨owned_newBlock_root hi run, h, hd, hm₁, hi₁, by simpa using hp⟩

/-- Physically deallocate a whole initialized owned view. Root authority excludes
    live aliases; dangling pointer payloads in the frame remain valid metadata. -/
theorem dealloc.spec (repr : Repr T) (p : RawPtr T) (base : BasePtr) (value : T)
    (s₀ : Heap) (hsize : 0 < repr.size) (authority : RootReturn s₀ p.provenance) :
    TripleAt (sep (alloc repr p base 1 true) (pointsTo repr p base value))
      (Result.checkedModify (State.dealloc repr p 1))
      (fun _ => emp) s₀ := by
  intro h F hp hd hm hi
  have hpRead := sep_mono (fun _ hp => hp) (fun _ => pointsTo_readable) hp
  obtain ⟨blk, hl, live, address, aligned, owned, len, depths, shape⟩ :=
    whole_readable hsize hpRead ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨root, hr, rootBase, rootLen, aliases⟩ := authority blk hl
  have rootSelf : root.root = blk.root := by
    have valid := hi.validBlock hl
    simp [Heap.validBlock, hr] at valid
    exact valid.1.2.1.1.1
  have retired := Heap.retire_Inv hi p.provenance
  have inactive := Heap.noAliases_retire_inactive hi p.provenance blk.root aliases
  have dead := Heap.killRoot_Inv retired blk.root inactive
  have returned : Heap.returnOwned repr p 1 s₀ = some (s₀.retire p.provenance) := by
    have commit : Heap.commit (s₀.retire p.provenance) = some (s₀.retire p.provenance) := by
      simp [Heap.commit, retired.2]
    simp only [Heap.returnOwned, hl, Bind.bind, Option.bind, hr]
    have depth : ∀ cell ∈ blk.repr, cell.depth = some 0 := by
      simpa [-Cell.depth] using depths
    have equalBase : (blk.bptr == root.bptr) = true := by
      change (blk.bptr.bv == root.bptr.bv) = true
      simp [rootBase]
    simp [-Cell.depth, live, owned, address, aligned, len, ← rootLen, aliases, commit]
    exact ⟨equalBase, depth⟩
  have run : Heap.dealloc repr p 1 s₀ =
      some ((s₀.retire p.provenance).killRoot blk.root) := by
    simp only [Heap.dealloc, hl, Bind.bind, Option.bind, returned]
    change Heap.commit ((s₀.retire p.provenance).killRoot blk.root) = _
    simp [Heap.commit, dead.2]
  have oldFrame := ((Fragment.matches_union _ _ _).mp hm).2
  have absent := frame_base_absent hl (shape ▸ hd) oldFrame
  have frame := matches_retire_frame oldFrame absent
  have rootSelf' : ∀ actual, (s₀.retire p.provenance).allocations blk.root = some actual →
      actual.root = blk.root := by
    intro actual lookup
    by_cases same : blk.root = p.provenance
    · have parent : s₀.allocations p.provenance = some root := same ▸ hr
      have he : actual = { root with active := false } := by
        simpa [Heap.retire, update, same, parent] using lookup.symm
      simpa [he] using rootSelf
    · have he : actual = root := by
        simpa [Heap.retire, update, same, hr] using lookup.symm
      simpa [he] using rootSelf
  have finalFrame := matches_killRoot frame rootSelf' inactive
  apply Spec.checkedModify.mpr
  refine ⟨⟨(), _, run⟩, ?_⟩
  intro _ s₁ step
  have he := Option.some.inj (step.symm.trans run)
  subst s₁
  exact ⟨∅, Fragment.disjoint_empty_left _, by simpa using finalFrame, dead, rfl⟩

end HeapWP
end Aeneas.Std
