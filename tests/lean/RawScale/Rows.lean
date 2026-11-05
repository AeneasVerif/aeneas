module

public import RawScale.Wrappers
public import Aeneas.Std.Heap.SliceExposure
import all RawScale.Funs
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Array.ArraySlice
import all Aeneas.Std.Slice

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_scale

set_option maxHeartbeats 1000000

local macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| agrind)

private theorem row_fit (p : RawPtr Row15) (base : BasePtr) (row : Row15)
    (depth : Nat) (h : Fragment) (s : Heap) (hp : readable rowRepr p base row depth h)
    (hm : Fragment.Matches s h) (hi : s.Inv) :
    ∀ i, i < 16 →
      p.address.val + i * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize := by
  have bound := readableRange_bound raw_box.u32Repr (p.cast U32) base
    (rowWords row) depth (by decide) (by decide) h s
    (readable_row_to_words p base row depth h hp) hm hi
  intro i hi
  change p.address.val + 16 * 4 < _ at bound
  change p.address.val + i * 4 < _
  agrind

theorem scale_row_raw.in_place_spec (k : U32) (p : RawPtr Row15)
    (base : BasePtr) (row : Row15) :
    ⦃ pointsTo rowRepr p base row ⦄
    scale_raw 16#usize k (p.cast U32) (p.cast U32)
    ⦃ _ => pointsTo rowRepr p base (scaledRow k row) ⦄ := by
  intro h F s₀ hp hd hm hi
  have aligned : 32 ∣ p.address.val := by obtain ⟨_, _, _, ha, _⟩ := hp; exact ha
  have fit := row_fit p base row 0 h s₀ (pointsTo_readable hp)
    ((Fragment.matches_union _ _ _).mp hm).1 hi
  apply HeapWP.Spec.mono (scale_raw.in_place_spec 16#usize k (p.cast U32) base
    (rowWords row) fit h F s₀ (row_to_words p base row 0 h hp) hd hm hi)
  rintro _ s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  exact ⟨h₁, hd₁, hm₁, hi₁, words_to_row p base _ 0 h₁ aligned hp₁⟩

theorem scale_row_raw.disjoint_spec (k : U32) (p q : RawPtr Row15)
    (srcBase dstBase : BasePtr) (src dst : Row15) (depth : Nat) :
    ⦃ readable rowRepr p srcBase src depth ∗ pointsTo rowRepr q dstBase dst ⦄
    scale_raw 16#usize k (p.cast U32) (q.cast U32)
    ⦃ _ => readable rowRepr p srcBase src depth ∗
      pointsTo rowRepr q dstBase (scaledRow k src) ⦄ := by
  intro h F s₀ hp hd hm hi
  obtain ⟨a, b, hab, hh, ha, hb⟩ := hp
  have matched := ((Fragment.matches_union _ _ _).mp hm).1
  rw [hh, Fragment.matches_union] at matched
  have srcFit := row_fit p srcBase src depth a s₀ ha matched.1 hi
  have dstFit := row_fit q dstBase dst 0 b s₀ (pointsTo_readable hb) matched.2 hi
  have aligned : 32 ∣ q.address.val := by obtain ⟨_, _, _, ha, _⟩ := hb; exact ha
  apply HeapWP.Spec.mono
    (scale_raw.disjoint_readable_spec 16#usize k (p.cast U32) (q.cast U32)
      srcBase dstBase (rowWords src) (rowWords dst) depth
      (readable rowRepr p srcBase src depth) (readable_row_to_words p srcBase src depth)
      srcFit dstFit h F s₀ ⟨a, b, hab, hh, ha, row_to_words q dstBase dst 0 b hb⟩ hd hm hi)
  rintro _ s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  exact ⟨h₁, hd₁, hm₁, hi₁, sep_mono (fun _ hp => hp)
    (words_to_row q dstBase _ 0 · aligned) hp₁⟩

def rowStep (k : U32) (src dst : RawPtr Row15) (i : Usize) : Result Unit := do
  let p ← RawPtr.add rowRepr src i
  let p1 ← ext.cast U32 p
  let q ← RawPtr.add rowRepr dst i
  let q1 ← ext.cast U32 q
  scale_raw 16#usize k p1 q1

theorem rowStep.in_place_spec (k : U32) (p : RawPtr Row15)
    (base : BasePtr) (rows : Vector Row15 count) (i : Usize) (hlt : i.val < count) :
    ⦃ pointsToRange rowRepr p base rows ⦄ rowStep k p p i
    ⦃ _ => pointsToRange rowRepr p base
      (rows.set i.val (scaledRow k rows[i.val]) hlt) ⦄ := by
  unfold rowStep
  step with add_readable_range.spec rowRepr p base rows 0 _
    (fun _ => pointsToRange_readable) i (by agrind) (by decide) (by agrind)
    as ⟨q, h, hprov, haddr, hp⟩
  simp only [ext.cast, bind_ok]
  step with add_readable_range.spec rowRepr p base rows 0 _
    (fun _ => pointsToRange_readable) i (by agrind) (by decide) (by agrind)
    as ⟨q₁, h₁, hprov₁, haddr₁, hp₁⟩
  have same : q₁ = q := by
    cases q
    cases q₁
    simp only [RawPtr.mk.injEq]
    constructor
    · agrind
    · apply UScalar.eq_of_val_eq
      agrind
  subst q₁
  step with modify_range.spec rowRepr p q base rows ⟨i.val, hlt⟩
    (scaledRow k rows[i.val]) (by decide) hprov haddr _
    (scale_row_raw.in_place_spec k q base rows[i.val])
  assumption

theorem rowStep.disjoint_spec (k : U32) (src dst : RawPtr Row15)
    (srcBase dstBase : BasePtr) (source target : Vector Row15 count)
    (depth : Nat) (i : Usize) (hlt : i.val < count) :
    ⦃ readableRange rowRepr src srcBase source depth ∗
      pointsToRange rowRepr dst dstBase target ⦄ rowStep k src dst i
    ⦃ _ => readableRange rowRepr src srcBase source depth ∗
      pointsToRange rowRepr dst dstBase
        (target.set i.val (scaledRow k source[i.val]) hlt) ⦄ := by
  intro h F s₀ hp hd hm hi
  unfold rowStep
  have srcAdd := HeapWP.frame (R := pointsToRange rowRepr dst dstBase target)
    (add_readable_range.spec rowRepr src srcBase source depth _ (fun _ hp => hp)
      i (by agrind) (by decide) (by agrind))
  apply HeapWP.Spec.bind (srcAdd h F s₀ hp hd hm hi)
  rintro p s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  obtain ⟨hprov, haddr, hp₁⟩ :
      p.provenance = src.provenance ∧ p.address.val = src.address.val + i.val * rowRepr.size ∧
      (readableRange rowRepr src srcBase source depth ∗
        pointsToRange rowRepr dst dstBase target) h₁ := by
    simpa only [sep_and_left] using hp₁
  simp only [ext.cast, bind_ok]
  have dstAdd := HeapWP.frame (R := readableRange rowRepr src srcBase source depth)
    (add_readable_range.spec rowRepr dst dstBase target 0 _
      (fun _ => pointsToRange_readable) i (by agrind) (by decide) (by agrind))
  apply HeapWP.Spec.bind (dstAdd h₁ F s₁ ((sep_comm _ _ _).mp hp₁) hd₁ hm₁ hi₁)
  rintro q s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
  obtain ⟨hprov₁, haddr₁, hp₂⟩ :
      q.provenance = dst.provenance ∧ q.address.val = dst.address.val + i.val * rowRepr.size ∧
      (pointsToRange rowRepr dst dstBase target ∗
        readableRange rowRepr src srcBase source depth) h₂ := by
    simpa only [sep_and_left] using hp₂
  exact modify_ranges.spec rowRepr src dst p q srcBase dstBase source target depth
    ⟨i.val, hlt⟩ (scaledRow k source[i.val]) (by decide) hprov haddr hprov₁ haddr₁ _
    (scale_row_raw.disjoint_spec k p q srcBase dstBase source[i.val] target[i.val] depth)
    h₂ F s₂ ((sep_comm _ _ _).mp hp₂) hd₂ hm₂ hi₂

private theorem fold_rowStep (k : U32) (src dst : RawPtr Row15) (i : Usize)
    (next : Result Unit) :
    (do let p ← RawPtr.add rowRepr src i
        let p1 ← ext.cast U32 p
        let q ← RawPtr.add rowRepr dst i
        let q1 ← ext.cast U32 q
        scale_raw 16#usize k p1 q1
        next) = (do rowStep k src dst i; next) := by
  simp only [rowStep, bind_tc_eq, Aeneas.Std.bind_assoc]

theorem scale_rows_raw_loop.rule {R : Usize} (factors : Array U32 R)
    (src dst : RawPtr Row15) (iter : core.ops.range.Range Usize)
    (I : Nat → Assertion) (hend : iter.end = R) (hle : iter.start.val ≤ R.val)
    (body : ∀ i : Usize, (hlt : i.val < R.val) →
      HeapWP.Triple (I i.val) (rowStep factors.val[i.val] src dst i)
        (fun _ => I (i.val + 1))) :
    HeapWP.Triple (I iter.start.val) (scale_rows_raw_loop iter factors src dst)
      (fun _ => I R.val) := by
  intro h F s₀ hp hd hm hi
  unfold scale_rows_raw_loop
  by_cases hlt : iter.start.val < iter.end.val
  · apply HeapWP.Spec.bind
      (HeapWP.Spec.of_spec (core.iter.range.IteratorRange.next_Usize_some_spec iter hlt) s₀)
    rintro ⟨o, iter₁⟩ s₁ ⟨⟨ho, hstart, hend₁⟩, hs⟩
    subst o
    subst s₁
    apply HeapWP.Spec.bind
      (HeapWP.Spec.of_spec (Array.index_usize_spec factors iter.start (by agrind)) s₀)
    rintro k s₁ ⟨hk, hs⟩
    subst s₁
    have hk' : k = factors.val[iter.start.val] := hk
    subst k
    change HeapWP.Spec (do
      let p ← RawPtr.add rowRepr src iter.start
      let p1 ← ext.cast U32 p
      let q ← RawPtr.add rowRepr dst iter.start
      let q1 ← ext.cast U32 q
      scale_raw 16#usize factors.val[iter.start.val] p1 q1
      scale_rows_raw_loop iter₁ factors src dst) _ s₀
    have folded := fold_rowStep factors.val[iter.start.val] src dst iter.start
      (scale_rows_raw_loop iter₁ factors src dst)
    simp only [bind_tc_eq] at folded
    rw [folded]
    have ih := scale_rows_raw_loop.rule factors src dst iter₁ I (hend₁.trans hend)
      (by agrind) body
    have rest : HeapWP.Triple (I (iter.start.val + 1))
        (scale_rows_raw_loop iter₁ factors src dst) (fun _ => I R.val) := by
      simpa only [hstart] using ih
    exact HeapWP.Triple.bind (body iter.start (by agrind)) (fun _ => rest)
      h F s₀ hp hd hm hi
  · apply HeapWP.Spec.bind
      (HeapWP.Spec.of_spec (core.iter.range.IteratorRange.next_Usize_none_spec iter (by agrind)) s₀)
    rintro ⟨o, iter₁⟩ s₁ ⟨⟨ho, _⟩, hs⟩
    subst o
    subst s₁
    exact (HeapWP.Spec.pure () _ s₀).mpr
      ⟨h, hd, hm, hi, by simpa only [show iter.start.val = R.val by agrind] using hp⟩
termination_by R.val - iter.start.val
decreasing_by agrind

theorem scale_rows_raw.rule {R : Usize} (factors : Array U32 R)
    (src dst : RawPtr Row15) (I : Nat → Assertion)
    (body : ∀ i : Usize, (hlt : i.val < R.val) →
      HeapWP.Triple (I i.val) (rowStep factors.val[i.val] src dst i)
        (fun _ => I (i.val + 1))) :
    HeapWP.Triple (I 0) (scale_rows_raw factors src dst) (fun _ => I R.val) := by
  unfold scale_rows_raw
  simpa using scale_rows_raw_loop.rule factors src dst ⟨0#usize, R⟩ I rfl (by simp) body

def scaledRows {R : Usize} (factors : Array U32 R) (source : Vector Row15 R.val) :
    Vector Row15 R.val :=
  Vector.ofFn fun i => scaledRow factors.val[i.val] source[i.val]

private def rowsPrefix {R : Usize} (factors : Array U32 R)
    (source target : Vector Row15 R.val) (stop : Nat) : Vector Row15 R.val :=
  Vector.ofFn fun i => if i.val < stop then (scaledRows factors source)[i.val] else target[i.val]

private theorem rowsPrefix_zero {R : Usize} (factors : Array U32 R)
    (source target : Vector Row15 R.val) : rowsPrefix factors source target 0 = target := by
  apply Vector.ext
  intro i hi
  simp [rowsPrefix]

private theorem rowsPrefix_all {R : Usize} (factors : Array U32 R)
    (source target : Vector Row15 R.val) :
    rowsPrefix factors source target R.val = scaledRows factors source := by
  apply Vector.ext
  intro i hi
  simp [rowsPrefix]

private theorem rowsPrefix_next {R : Usize} (factors : Array U32 R)
    (source target : Vector Row15 R.val) (i : Fin R.val) :
    (rowsPrefix factors source target i.val).set i.val
      (scaledRow factors.val[i.val] source[i.val]) i.isLt =
      rowsPrefix factors source target (i.val + 1) := by
  apply Vector.ext
  intro j hj
  by_cases he : j = i.val
  · subst j
    simp [rowsPrefix, scaledRows]
  · rw [Vector.getElem_set_ne i.isLt hj (Ne.symm he)]
    have same : (j < i.val + 1) = (j < i.val) := by agrind
    simp only [rowsPrefix, Vector.getElem_ofFn, same]

/-- **Spec theorem for `raw_scale::scale_rows_raw` (equal pointers)**
    Each physical row is multiplied by its corresponding factor; arbitrary frames survive. -/
@[step]
theorem scale_rows_raw.in_place_spec {R : Usize} (factors : Array U32 R)
    (p : RawPtr Row15) (base : BasePtr) (rows : Vector Row15 R.val) :
    ⦃ pointsToRange rowRepr p base rows ⦄ scale_rows_raw factors p p
    ⦃ _ => pointsToRange rowRepr p base (scaledRows factors rows) ⦄ := by
  have loop := scale_rows_raw.rule factors p p
    (fun stop => pointsToRange rowRepr p base (rowsPrefix factors rows rows stop))
  simp only [rowsPrefix_zero, rowsPrefix_all] at loop
  apply loop
  intro i hlt
  have body := rowStep.in_place_spec factors.val[i.val] p base
    (rowsPrefix factors rows rows i.val) i hlt
  have current : (rowsPrefix factors rows rows i.val)[i.val] = rows[i.val] := by
    simp [rowsPrefix]
  simpa only [current, rowsPrefix_next factors rows rows ⟨i.val, hlt⟩] using body

/-- **Spec theorem for `raw_scale::scale_rows_raw` (disjoint pointers)**
    Preserve the source rows and replace every destination row by the exact scaled source. -/
@[step]
theorem scale_rows_raw.disjoint_spec {R : Usize} (factors : Array U32 R)
    (src dst : RawPtr Row15) (srcBase dstBase : BasePtr)
    (source target : Vector Row15 R.val) (depth : Nat) :
    ⦃ readableRange rowRepr src srcBase source depth ∗
      pointsToRange rowRepr dst dstBase target ⦄ scale_rows_raw factors src dst
    ⦃ _ => readableRange rowRepr src srcBase source depth ∗
      pointsToRange rowRepr dst dstBase (scaledRows factors source) ⦄ := by
  have loop := scale_rows_raw.rule factors src dst
    (fun stop => readableRange rowRepr src srcBase source depth ∗
      pointsToRange rowRepr dst dstBase (rowsPrefix factors source target stop))
  simp only [rowsPrefix_zero, rowsPrefix_all] at loop
  apply loop
  intro i hlt
  simpa only [rowsPrefix_next factors source target ⟨i.val, hlt⟩] using
    rowStep.disjoint_spec factors.val[i.val] src dst srcBase dstBase source
      (rowsPrefix factors source target i.val) depth i hlt

def rowArrayValues {R : Usize} (rows : Array Row15 R) : Vector Row15 R.val :=
  ⟨rows.val.toArray, by simp⟩

@[simp]
theorem rowArrayValues_toList {R : Usize} (rows : Array Row15 R) :
    (rowArrayValues rows).toList = rows.val := by simp [rowArrayValues]

private theorem end_rows (p : RawPtr Row15) (original : Array Row15 R)
    (values : Vector Row15 R.val) :
    ⦃ alloc rowRepr p p.address R.val false ∗ readableRange rowRepr p p.address values 0 ⦄
    Slice.end_as_mut_ptr rowRepr (Array.to_slice original) p
    ⦃ result => fun h => result.val = values.toList ∧ empty h ⦄ := by
  exact mutable_range_end.spec rowRepr p (Array.to_slice original) values
    (by simp [Array.to_slice]) (by decide)

private theorem scale_rows_in_place_tail (factors : Array U32 R)
    (p : RawPtr Row15) (rows : Array Row15 R) :
    ⦃ alloc rowRepr p p.address R.val false ∗ pointsToRange rowRepr p p.address (rowArrayValues rows) ⦄
    (do scale_rows_raw factors p p
        let result ← Slice.end_as_mut_ptr rowRepr (Array.to_slice rows) p
        pure (Array.from_slice rows result))
    ⦃ result => fun h => result.val = (scaledRows factors (rowArrayValues rows)).toList ∧ empty h ⦄ := by
  intro h F s hp hd hm hi
  have kernel := HeapWP.frame (R := alloc rowRepr p p.address R.val false)
    (scale_rows_raw.in_place_spec factors p p.address (rowArrayValues rows))
  apply HeapWP.Spec.bind (kernel h F s ((sep_comm _ _ _).mp hp) hd hm hi)
  rintro _ s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  have ready := (sep_comm _ _ _).mp (sep_mono (fun _ => pointsToRange_readable)
    (fun _ hp => hp) hp₁)
  apply HeapWP.Spec.bind (end_rows p rows _ h₁ F s₁ ready hd₁ hm₁ hi₁)
  rintro result s₂ ⟨h₂, hd₂, hm₂, hi₂, hv, hemp⟩
  have len : result.val.length = R.val := by simp [hv]
  exact (HeapWP.Spec.pure _ _ _).mpr
    ⟨h₂, hd₂, hm₂, hi₂, by simpa [Array.from_slice_val _ _ len] using hv, hemp⟩

/-- **Spec theorem for `raw_scale::scale_rows_in_place`**
    Each row is multiplied by its own factor, including the initialized padding.
    The exclusive exposure is retired on successful return, also for zero rows. -/
@[step]
theorem scale_rows_in_place.spec (factors : Array U32 R) (rows : Array Row15 R) :
    ⦃ empty ⦄ scale_rows_in_place factors rows
    ⦃ (result : Array Row15 R) => fun h =>
      result.val = (scaledRows factors (rowArrayValues rows)).toList ∧ empty h ⦄ := by
  intro h F s rfl _ hm hi
  simp only [Fragment.empty_union] at hm
  simp only [scale_rows_in_place, Array.to_slice_mut, lift, bind_ok,
    Slice.as_mut_ptr, Aeneas.Std.bind_assoc, ext.cast, Aeneas.Std.uncurry]
  simp only [Array.to_slice, Slice.from_val]
  have alloc := mutable_range_exposure.spec rowRepr (rowArrayValues rows)
    rowRepr_calibrated s F hi hm
  simp only [rowArrayValues_toList] at alloc
  apply HeapWP.Spec.bind alloc
  rintro p s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  exact scale_rows_in_place_tail factors p rows h₁ F s₁ hp₁ hd₁ hm₁ hi₁

private theorem scale_rows_into_tail (factors : Array U32 R)
    (p q : RawPtr Row15) (src dst : Array Row15 R) :
    ⦃ (alloc rowRepr p p.address R.val false ∗
        readableRange rowRepr p p.address (rowArrayValues src) 1) ∗
      (alloc rowRepr q q.address R.val false ∗
        pointsToRange rowRepr q q.address (rowArrayValues dst)) ⦄
    (do scale_rows_raw factors p q
        let result ← Slice.end_as_mut_ptr rowRepr (Array.to_slice dst) q
        Slice.end_as_ptr rowRepr (Array.to_slice src) p
        pure (Array.from_slice dst result))
    ⦃ result => fun h => result.val = (scaledRows factors (rowArrayValues src)).toList ∧ empty h ⦄ := by
  intro h F s hp hd hm hi
  have kernel := HeapWP.frame
    (R := alloc rowRepr p p.address R.val false ∗ alloc rowRepr q q.address R.val false)
    (scale_rows_raw.disjoint_spec factors p q p.address q.address
      (rowArrayValues src) (rowArrayValues dst) 1)
  have ready := (sep_comm _ _ _).mp ((sep_exchange _ _ _ _ h).mp hp)
  apply HeapWP.Spec.bind (kernel h F s ready hd hm hi)
  rintro _ s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  have restored := sep_mono (fun _ => sep_mono (fun _ hp => hp)
    (fun _ => pointsToRange_readable)) (fun _ hp => hp) hp₁
  have paired := (sep_exchange _ _ _ _ h₁).mpr ((sep_comm _ _ _).mp restored)
  have back := HeapWP.frame (R := alloc rowRepr p p.address R.val false ∗
    readableRange rowRepr p p.address (rowArrayValues src) 1)
    (end_rows q dst (scaledRows factors (rowArrayValues src)))
  apply HeapWP.Spec.bind (back h₁ F s₁ ((sep_comm _ _ _).mp paired) hd₁ hm₁ hi₁)
  rintro result s₂ ⟨h₂, hd₂, hm₂, hi₂, post⟩
  obtain ⟨hv, source⟩ : result.val = (scaledRows factors (rowArrayValues src)).toList ∧
      (alloc rowRepr p p.address R.val false ∗
        readableRange rowRepr p p.address (rowArrayValues src) 1) h₂ := by
    simpa only [sep_and_left, sep_empty_left] using post
  have cleanup := shared_range_end.spec rowRepr p (rowArrayValues src) (by decide)
  simp only [rowArrayValues_toList] at cleanup
  simp only [Slice.end_as_ptr, Array.to_slice, Slice.from_val]
  apply HeapWP.Spec.bind (cleanup h₂ F s₂ source hd₂ hm₂ hi₂)
  rintro _ s₃ ⟨h₃, hd₃, hm₃, hi₃, hemp⟩
  have len : result.val.length = R.val := by simp [hv]
  exact (HeapWP.Spec.pure _ _ _).mpr
    ⟨h₃, hd₃, hm₃, hi₃, by simpa [Array.from_slice_val _ _ len] using hv, hemp⟩

/-- **Spec theorem for `raw_scale::scale_rows_into`**
    The output is the factorwise-scaled source, independent of the old destination.
    Both matching backward computations run and retire their temporary exposures. -/
@[step]
theorem scale_rows_into.spec (factors : Array U32 R) (src dst : Array Row15 R) :
    ⦃ empty ⦄ scale_rows_into factors src dst
    ⦃ (result : Array Row15 R) => fun h =>
      result.val = (scaledRows factors (rowArrayValues src)).toList ∧ empty h ⦄ := by
  intro h F s rfl _ hm hi
  simp only [Fragment.empty_union] at hm
  simp only [scale_rows_into, Array.to_slice_mut, lift, bind_ok,
    Slice.as_ptr, Slice.as_mut_ptr, Aeneas.Std.bind_assoc, Aeneas.Std.uncurry]
  have source := shared_range_exposure.spec rowRepr (rowArrayValues src) s F hi hm
  simp only [rowArrayValues_toList] at source
  simp only [Array.to_slice, Slice.from_val]
  apply HeapWP.Spec.bind source
  rintro p s₁ ⟨a, haF, hm₁, hi₁, source⟩
  have target := mutable_range_exposure.spec rowRepr (rowArrayValues dst)
    rowRepr_calibrated s₁ (a ∪ F) hi₁ hm₁
  simp only [rowArrayValues_toList] at target
  apply HeapWP.Spec.bind target
  rintro q s₂ ⟨b, hb, hm₂, hi₂, target⟩
  obtain ⟨hba, hbF⟩ := Fragment.disjoint_union_right.mp hb
  have pre :
      ((alloc rowRepr p p.address R.val false ∗ readableRange rowRepr p p.address (rowArrayValues src) 1) ∗
        (alloc rowRepr q q.address R.val false ∗ pointsToRange rowRepr q q.address (rowArrayValues dst))) (b ∪ a) :=
    (sep_comm _ _ _).mp ⟨b, a, hba, rfl, target, source⟩
  have combined : Fragment.Matches s₂ ((b ∪ a) ∪ F) := by
    simpa only [Fragment.union_assoc] using hm₂
  exact scale_rows_into_tail factors p q src dst (b ∪ a) F s₂ pre
    (Fragment.disjoint_union_left.mpr ⟨hbF, haF⟩) combined hi₂

end raw_scale
