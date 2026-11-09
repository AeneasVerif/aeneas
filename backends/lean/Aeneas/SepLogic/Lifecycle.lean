module

public import Aeneas.SepLogic.Specs
public import Aeneas.SepLogic.Allocation
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
public import Aeneas.SepLogic.Local

@[expose] public section

namespace Aeneas.Std

open Aeneas.SepLogic

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

open Bytes Aeneas.SepLogic

namespace Bytes

open Aeneas.SepLogic

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

end Bytes

end Aeneas.Std
