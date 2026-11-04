module

public import RawMemoryViews.ByteStorage
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Slice
import all Aeneas.Std.Heap.Allocation
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Primitives

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_memory_views

set_option maxHeartbeats 1000000

def fill_safe_loop (bytes : Slice U8) (value : U8) (i : Usize) : Result (Slice U8) := do
  if i < Slice.len bytes then
    let updated ← Slice.update bytes i value
    let next ← i + 1#usize
    fill_safe_loop updated value next
  else .ok bytes
partial_fixpoint

def fill_safe (bytes : Slice U8) (value : U8) : Result (Slice U8) :=
  fill_safe_loop bytes value 0#usize

@[step]
theorem fill_safe_loop.spec (bytes : Slice U8) (value : U8) (i : Usize)
    (bound : i.val ≤ bytes.length)
    (done : ∀ j, j < i.val → bytes[j]! = value) :
    fill_safe_loop bytes value i ⦃ (result : Slice U8) =>
      result.val = List.replicate bytes.length value ⦄ := by
  unfold fill_safe_loop
  step*
  · intro j hj
    by_cases eq : j = i.val
    · subst j
      simp_lists [*]
    · have before : j < i.val := by agrind
      have old := done j before
      simp_lists [*]
      simpa [Slice.getElem!_Nat_eq, show j < bytes.val.length from by agrind] using old
  · apply List.ext_getElem
    · simp
    · intro j hj hk
      have before : j < i.val := by agrind
      have eq := done j before
      simpa [hj] using eq
termination_by bytes.length - i.val
decreasing_by agrind

@[step]
theorem fill_safe.spec (bytes : Slice U8) (value : U8) :
    fill_safe bytes value ⦃ (result : Slice U8) =>
      result.val = List.replicate bytes.length value ⦄ := by
  unfold fill_safe
  step*

/- This is the smaller as_mut_ptr exposure and its effectful backward return,
   not an assumption that a callback still works in an unrelated later heap. -/
def fill_exposed (values : Vector U8 4) : Result (Vector U8 4) := do
  let (p, back) ← core.ptr.from_mut (byteVectorRepr 4) values
  fill_raw (p.cast U8) 4#usize 3#u8
  back

private theorem end_exposed.spec (p : RawPtr (Vector U8 4)) (values : Vector U8 4)
    (h F : Fragment) (s₀ : Heap)
    (hp : (alloc (byteVectorRepr 4) p p.address 1 false ∗
      pointsTo (byteVectorRepr 4) p p.address values) h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s₀ (h ∪ F)) (hi : s₀.Inv) :
    HeapWP.Spec (core.ptr.end_from_mut (byteVectorRepr 4) p)
      (fun result s₁ => result = values ∧ s₁ = s₀.retire p.provenance ∧
        Fragment.Matches s₁ F ∧ s₁.Inv) s₀ := by
  obtain ⟨a, b, apart, joined, owner, point⟩ := hp
  have localMatch : Fragment.Matches s₀ b := by
    rw [joined, Fragment.matches_union, Fragment.matches_union] at hm
    exact hm.1.2
  have read := read_of_pointsTo (by decide : 0 < (byteVectorRepr 4).size) point localMatch
  have reading : HeapWP.Spec (RawPtr.read (byteVectorRepr 4) p)
      (fun result s₁ => result = values ∧ s₁ = s₀) s₀ := by
    apply HeapWP.Spec.checkedModify.mpr
    refine ⟨⟨values, s₀, read, rfl⟩, ?_⟩
    rintro result s₁ ⟨run, rfl⟩
    exact ⟨Option.some.inj (run.symm.trans read), rfl⟩
  unfold core.ptr.end_from_mut
  apply HeapWP.Spec.bind reading
  rintro result s₁ ⟨resultEq, same⟩
  subst result
  subst s₁
  have returning := SepLogic.returnView.spec (byteVectorRepr 4) p p.address values false
    s₀ (by decide) (by simp) h F
    ⟨a, b, apart, joined, owner, pointsTo_readable point⟩ hd hm hi
  obtain ⟨enabled, post⟩ := returning
  change ∃ (_ : Unit) (s₂ : Heap), Heap.endExposureAt (byteVectorRepr 4) p 1 0 s₀ = some s₂ at enabled
  change ∀ (_ : Unit) (s₂ : Heap), Heap.endExposureAt (byteVectorRepr 4) p 1 0 s₀ = some s₂ → _ at post
  have ending := HeapWP.Spec.checkedModify.mpr
    ⟨enabled, fun result s₂ (run : State.removeExposure (byteVectorRepr 4) p 1 s₀ result s₂) =>
      And.intro (Heap.endExposure_retire run) (post result s₂ run)⟩
  apply HeapWP.Spec.bind ending
  rintro _ s₂ ⟨retired, h₂, _, hm₂, hi₂, rfl⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨rfl, retired, by simpa using hm₂, hi₂⟩

/-- A complete nested raw exposure executes four raw writes and retires only
    its fresh view. In particular, every existing outer-view record is retained. -/
theorem fill_exposed.spec (values : Vector U8 4) (s₀ : Heap) (F : Fragment)
    (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec (fill_exposed values)
      (fun result s₁ => result = Vector.replicate 4 3#u8 ∧ Heap.NewView s₀ s₁ ∧
        (∀ blk, s₁.allocations s₀.next = some blk → blk.active = false) ∧
        Fragment.Matches s₁ F ∧ s₁.Inv) s₀ := by
  simp only [fill_exposed, core.ptr.from_mut, Aeneas.Std.bind_assoc, bind_ok]
  have exposed := HeapWP.allocExposure_encoded.spec (byteVectorRepr 4) values
    (byteVectorRepr_calibrated values) s₀ F hi hm
  have post := HeapWP.Spec.allocatingModify.mp exposed
  have exposed' := HeapWP.Spec.allocatingModify.mpr
    (fun p s₁ run => And.intro
      (show p.provenance = s₀.next ∧ Heap.NewView s₀ s₁ from by
        obtain ⟨data, base, root, _, created⟩ := run
        exact Heap.newBlock_newView created)
      (post p s₁ run))
  apply HeapWP.Spec.bind exposed'
  rintro p s₁ ⟨⟨fresh, scope⟩, _, h₁, hd₁, hm₁, hi₁, a, b, apart, joined, owner, point⟩
  have bytes := (byteVector_pointsTo p p.address values b).mp point
  have matchBytes : Fragment.Matches s₁ b := by
    rw [joined, Fragment.matches_union, Fragment.matches_union] at hm₁
    exact hm₁.1.2
  have fits := writableBytes_fits (p.cast U8) p.address
    (values.map Aeneas.Std.Byte.data) b s₁ bytes matchBytes hi₁
  have framedMatch : Fragment.Matches s₁ (b ∪ (a ∪ F)) := by
    simp only [joined, Fragment.matches_union] at hm₁ ⊢
    tauto
  have framedDisjoint : b.Disjoint (a ∪ F) :=
    Fragment.disjoint_union_right.mpr
      ⟨apart.symm, (Fragment.disjoint_union_left.mp (joined ▸ hd₁)).2⟩
  apply HeapWP.Spec.bind (fill_raw_loop.spec (p.cast U8) 4#usize 3#u8 0#usize p.address
    (values.map Aeneas.Std.Byte.data) (by simp) fits b (a ∪ F) s₁ bytes
    framedDisjoint framedMatch hi₁)
  rintro _ s₂ ⟨stable, b₂, hd₂, hm₂, hi₂, bytes₂⟩
  have filled : filledFrom (values.map Aeneas.Std.Byte.data) 3#u8 (0#usize).val =
      (Vector.replicate 4 3#u8).map Aeneas.Std.Byte.data := by
    apply Vector.ext
    intro j hj
    simp [filledFrom]
  have point₂ := (byteVector_pointsTo p p.address (Vector.replicate 4 3#u8) b₂).mpr
    (filled ▸ bytes₂)
  have heap₂ : Fragment.Matches s₂ ((a ∪ b₂) ∪ F) := by
    simp only [Fragment.matches_union] at hm₂ ⊢
    tauto
  have sep₂ : (alloc (byteVectorRepr 4) p p.address 1 false ∗
      pointsTo (byteVectorRepr 4) p p.address (Vector.replicate 4 3#u8)) (a ∪ b₂) :=
    ⟨a, b₂, (Fragment.disjoint_union_right.mp hd₂).1.symm, rfl, owner, point₂⟩
  apply HeapWP.Spec.mono (end_exposed.spec p (Vector.replicate 4 3#u8) (a ∪ b₂) F s₂ sep₂
    (Fragment.disjoint_union_left.mpr
      ⟨(Fragment.disjoint_union_left.mp (joined ▸ hd₁)).1,
        (Fragment.disjoint_union_right.mp hd₂).2⟩) heap₂ hi₂)
  rintro result s₃ ⟨resultEq, retired, frame, inv⟩
  have changes : Heap.StableExcept s₀.next s₁ s₃ := by
    rw [retired]
    have all := stable.trans (Heap.retire_stable s₂ p.provenance)
    simpa [RawPtr.cast, fresh] using all
  refine ⟨resultEq, scope.modify changes, ?_, frame, inv⟩
  intro blk lookup
  rw [retired, ← fresh] at lookup
  simp only [Heap.retire, update, ↓reduceIte] at lookup
  obtain ⟨old, _, rfl⟩ := Option.map_eq_some_iff.mp lookup
  rfl

def prepare_middle (middle : Slice U8) : Result (Slice U8 × (Slice U8 → Slice U8)) := do
  let filled ← fill_safe middle 2#u8
  core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) filled
    { start := 3#usize, «end» := 7#usize }

@[step]
theorem prepare_middle.spec (middle : Slice U8) (length : middle.length = 12) :
    prepare_middle middle ⦃ (smaller : Slice U8) (back : Slice U8 → Slice U8) =>
      smaller.val = List.replicate 4 2#u8 ∧
      ∀ replacement : Slice U8, replacement.length = 4 →
        (back replacement).val =
          List.replicate 3 2#u8 ++ replacement.val ++ List.replicate 5 2#u8 ⦄ := by
  unfold prepare_middle
  step*
  · simp_lists [*]
    constructor
    · decide
    · intro replacement replacementLength
      simp [List.setSlice!, replacementLength]

def finish_middle (middle : Slice U8) : Result (Slice U8) := do
  let (tail, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeFromUsizeSlice U8) middle { start := 10#usize }
  let filled ← fill_safe tail 4#u8
  pure (back filled)

@[step]
theorem finish_middle.spec (middle : Slice U8) (length : middle.length = 12) :
    finish_middle middle ⦃ (result : Slice U8) =>
      result.val = middle.val.take 10 ++ List.replicate 2 4#u8 ⦄ := by
  unfold finish_middle
  step*
  · simp_lists [*]
    simp [List.setSlice!, show middle.val.length = 12 from length]

def middleResult : Vector U8 12 :=
  #v[2#u8, 2#u8, 2#u8, 3#u8, 3#u8, 3#u8, 3#u8, 2#u8, 2#u8, 2#u8, 4#u8, 4#u8]

/- The length check only converts the emitted dynamically-sized subslice to
   the concrete four-byte descriptor; its failure is proved unreachable. -/
def update_middle (middle : Slice U8) : Result (Slice U8) := do
  let prepared ← prepare_middle middle
  let smaller := prepared.1
  let back := prepared.2
  if length : smaller.val.length = 4 then
    let values : Vector U8 4 := ⟨smaller.val.toArray, by simp [length]⟩
    let updated ← fill_exposed values
    finish_middle (back (.from updated.toList (by scalar_tac)))
  else .fail .panic

theorem update_middle.spec (middle : Slice U8) (length : middle.length = 12)
    (s₀ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec (update_middle middle)
      (fun result s₁ => result.val = middleResult.toList ∧ Heap.NewView s₀ s₁ ∧
        (∀ blk, s₁.allocations s₀.next = some blk → blk.active = false) ∧
        Fragment.Matches s₁ F ∧ s₁.Inv) s₀ := by
  unfold update_middle
  apply HeapWP.Spec.bind (HeapWP.Spec.of_spec (prepare_middle.spec middle length) s₀)
  rintro ⟨smaller, back⟩ s₁ ⟨⟨small, returns⟩, same⟩
  subst s₁
  have size : smaller.val.length = 4 := by simp [small]
  dsimp only
  erw [dite_eq_left size]
  have vector : (⟨smaller.val.toArray, by simp [size]⟩ : Vector U8 4) =
      Vector.replicate 4 2#u8 := by
    apply Vector.toList_inj.mp
    simp [small]
  rw [vector]
  apply HeapWP.Spec.bind (fill_exposed.spec _ s₀ F hi hm)
  rintro updated s₂ ⟨rfl, scope, inactive, frame, inv⟩
  have restored := returns (Slice.from (Vector.replicate 4 3#u8).toList (by scalar_tac)) (by simp)
  have restoredLength :
      (back (Slice.from (Vector.replicate 4 3#u8).toList (by scalar_tac))).length = 12 := by
    change (back _).val.length = 12
    rw [restored]
    simp
  apply HeapWP.Spec.mono (HeapWP.Spec.of_spec (finish_middle.spec _ restoredLength) s₂)
  rintro result s₃ ⟨resultEq, same⟩
  subst s₃
  refine ⟨?_, scope, inactive, frame, inv⟩
  rw [resultEq, restored]
  change (List.replicate 3 2#u8 ++ (Vector.replicate 4 3#u8).toList ++
    List.replicate 5 2#u8).take 10 ++ List.replicate 2 4#u8 = middleResult.toList
  decide

def update_middle_raw (p : MutRawPtr U8) : Result Unit := do
  let (middle, back) ← core.slice.raw.from_raw_parts_mut Aeneas.Std.Repr.u8 p 12#usize
  let updated ← update_middle middle
  back updated

/-- The outer mutable borrow remains returnable after a real inner exposure,
    writes, and retirement. The arbitrary frame includes neighboring bytes
    and the original Box's allocation ownership. -/
theorem update_middle_raw.spec (p : RawPtr U8) (base : BasePtr) (initial : Vector U8 12)
    (h F : Fragment) (s₀ : Heap) (hp : pointsToRange Aeneas.Std.Repr.u8 p base initial 0 h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s₀ (h ∪ F)) (hi : s₀.Inv)
    (authority : RootReturn s₀ p.provenance) :
    HeapWP.Spec (update_middle_raw p)
      (fun _ s₁ => RootReturn s₁ p.provenance ∧
        ∃ h₁, h₁.Disjoint F ∧ Fragment.Matches s₁ (h₁ ∪ F) ∧ s₁.Inv ∧
          pointsToRange Aeneas.Std.Repr.u8 p base middleResult 0 h₁) s₀ := by
  unfold update_middle_raw core.slice.raw.from_raw_parts_mut RawPtr.borrowSlice
  simp only [bind_tc_eq, bind_ok, Aeneas.Std.bind_assoc]
  have countEq : (12#usize).val = 12 := by simp
  rw [countEq]
  have borrow := HeapWP.borrowRange.spec Aeneas.Std.Repr.u8 p base initial
    (by decide) (by decide) h F s₀ hp hd hm hi
  obtain ⟨enabled, post⟩ := HeapWP.Spec.checkedModify.mp borrow
  have borrowed := HeapWP.Spec.checkedModify.mpr
    ⟨enabled, fun values s₁ (run : State.borrowRange Aeneas.Std.Repr.u8 p 12 s₀ values s₁) =>
      And.intro run (And.intro
        (show RootReturn s₁ p.provenance from by
          have changed := run.2.2
          unfold Heap.borrowRange Heap.modifyRange at changed
          exact authority.modify changed)
        (post values s₁ run))⟩
  apply HeapWP.Spec.bind borrowed
  rintro values s₁ ⟨run, authority₁, h₁, hd₁, hm₁, hi₁, valuesEq, hp₁⟩
  rw [valuesEq]
  have lengthFits : initial.toList.length ≤ Usize.max := by scalar_tac
  simp only [dite_eq_left lengthFits, bind_ok]
  have issued : p.provenance < s₁.next := by
    obtain ⟨_, _, cells⟩ := hp₁
    have matching := ((Fragment.matches_union _ _ _).mp hm₁).1
    rw [cells] at matching
    obtain ⟨blk, lookup, _⟩ := matches_cellsHeap.mp matching 0 (by decide)
    exact hi₁.base_lt lookup
  apply HeapWP.Spec.bind (update_middle.spec (Slice.from initial.toList lengthFits) (by simp)
    s₁ (h₁ ∪ F) hi₁ hm₁)
  rintro updated s₂ ⟨updatedEq, scope, inactive, frame, inv⟩
  have authority₂ := authority₁.after_scoped_view hi₁ issued scope inactive
  have updatedLength : updated.length = (12#usize).val := by
    change updated.val.length = (12#usize).val
    rw [updatedEq]
    simp
  unfold core.slice.raw.from_raw_parts_mut.back
  rw [ite_eq_left updatedLength, updatedEq]
  have returns := HeapWP.endBorrowRange_exclusive.spec Aeneas.Std.Repr.u8 p base middleResult s₂
    authority₂ (fun _ => Aeneas.Std.Repr.u8_noPointers _) (by decide) (by decide)
    h₁ F hp₁ hd₁ frame inv
  obtain ⟨enabled, post⟩ := HeapWP.Spec.checkedModify.mp returns
  apply HeapWP.Spec.checkedModify.mpr
  refine ⟨enabled, ?_⟩
  intro result s₃ run₃
  have authority₃ : RootReturn s₃ p.provenance := by
    obtain ⟨data, _, ending⟩ := run₃
    unfold Heap.endBorrowRange at ending
    exact authority₂.modify ending
  exact ⟨authority₃, post result s₃ run₃⟩

end raw_memory_views
