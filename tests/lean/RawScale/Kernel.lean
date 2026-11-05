module

public import RawScale.Properties
public import Aeneas.Std.Heap.RangeWrite
public import Aeneas.Std.Heap.Notation

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_scale

set_option maxHeartbeats 1000000

theorem scaleStep.in_place_spec (k : U32) (p : RawPtr U32) (base : BasePtr)
    (values : Vector U32 count) (i : Usize) (hlt : i.val < count)
    (hfit : p.address.val + i.val * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize) :
    ⦃ pointsToRange raw_box.u32Repr p base values ⦄
    scaleStep k p p i
    ⦃ _ => pointsToRange raw_box.u32Repr p base
      (values.set i.val (core.num.U32.wrapping_mul k values[i.val]) hlt) ⦄ := by
  intro h F s hp hd hm hi
  unfold scaleStep scale_one_raw
  apply HeapWP.Spec.bind
    (add_range.spec raw_box.u32Repr p base values 0 i (by agrind) (by decide)
      (by agrind) hfit h F s hp hd hm hi)
  rintro q s₁ ⟨h₁, hd₁, hm₁, hi₁, hprov, haddr, hp₁⟩
  apply HeapWP.Spec.bind
    (add_range.spec raw_box.u32Repr p base values 0 i (by agrind) (by decide)
      (by agrind) hfit h₁ F s₁ hp₁ hd₁ hm₁ hi₁)
  rintro q₁ s₂ ⟨h₂, hd₂, hm₂, hi₂, hprov₁, haddr₁, hp₂⟩
  apply HeapWP.Spec.bind
    (read_range.spec raw_box.u32Repr p q base values 0 ⟨i.val, hlt⟩
      (by decide) hprov haddr h₂ F s₂ hp₂ hd₂ hm₂ hi₂)
  rintro value s₃ ⟨h₃, hd₃, hm₃, hi₃, rfl, hp₃⟩
  simp only [lift, bind_ok]
  exact write_range.spec raw_box.u32Repr p q₁ base values ⟨i.val, hlt⟩ _
    (by decide) hprov₁ haddr₁ (raw_box.u32Repr_noPointers _) h₃ F s₃ hp₃ hd₃ hm₃ hi₃

def scaledPrefix (k : U32) (src dst : Vector U32 count) (stop : Nat) : Vector U32 count :=
  Vector.ofFn fun j => if j.val < stop then core.num.U32.wrapping_mul k src[j.val]
    else dst[j.val]

theorem scaledPrefix_zero (k : U32) (src dst : Vector U32 count) :
    scaledPrefix k src dst 0 = dst := by
  apply Vector.ext
  intro j hj
  simp [scaledPrefix]

theorem scaledPrefix_all (k : U32) (src dst : Vector U32 count) :
    scaledPrefix k src dst count = scaledWords k src := by
  apply Vector.ext
  intro j hj
  simp [scaledPrefix, scaledWords]

theorem scaledPrefix_next (k : U32) (src dst : Vector U32 count) (i : Fin count) :
    (scaledPrefix k src dst i.val).set i.val
      (core.num.U32.wrapping_mul k src[i.val]) i.isLt =
    scaledPrefix k src dst (i.val + 1) := by
  apply Vector.ext
  intro j hj
  by_cases he : j = i.val
  · subst j
    simp [scaledPrefix]
  · rw [Vector.getElem_set_ne i.isLt hj (Ne.symm he)]
    simp only [scaledPrefix, Vector.getElem_ofFn]
    have hlt : (j < i.val + 1) = (j < i.val) := by agrind
    simp only [hlt]

/-- **Spec theorem for in-place `raw_scale::scale_raw`**
    The extracted loop uses one exclusive range, not overlapping references.
    All words are updated and every disjoint frame is preserved. -/
theorem scale_raw.in_place_spec (N : Usize) (k : U32) (p : RawPtr U32)
    (base : BasePtr) (initial : Vector U32 N.val)
    (hfit : ∀ i, i < N.val →
      p.address.val + i * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize) :
    ⦃ pointsToRange raw_box.u32Repr p base initial ⦄
    scale_raw N k p p
    ⦃ _ => pointsToRange raw_box.u32Repr p base (scaledWords k initial) ⦄ := by
  have loop := scale_raw.rule N k p p
    (fun stop => pointsToRange raw_box.u32Repr p base
      (scaledPrefix k initial initial stop))
  simp only [scaledPrefix_zero, scaledPrefix_all] at loop
  apply loop
  intro i hlt
  have body := scaleStep.in_place_spec k p base
    (scaledPrefix k initial initial i.val) i hlt (hfit i.val hlt)
  have current : (scaledPrefix k initial initial i.val)[i.val] = initial[i.val] := by
    simp [scaledPrefix]
  simpa only [current, scaledPrefix_next k initial initial ⟨i.val, hlt⟩] using body

theorem scaleStep.disjoint_readable_spec (k : U32) (src dst : RawPtr U32)
    (srcBase dstBase : BasePtr) (source target : Vector U32 count) (depth : Nat)
    (sourceView : Assertion)
    (view : ∀ h, sourceView h → readableRange raw_box.u32Repr src srcBase source depth h)
    (i : Usize) (hlt : i.val < count)
    (srcFit : src.address.val + i.val * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize)
    (dstFit : dst.address.val + i.val * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize) :
    ⦃ sourceView ∗
      pointsToRange raw_box.u32Repr dst dstBase target ⦄
    scaleStep k src dst i
    ⦃ _ => sourceView ∗
      pointsToRange raw_box.u32Repr dst dstBase
        (target.set i.val (core.num.U32.wrapping_mul k source[i.val]) hlt) ⦄ := by
  intro h F s hp hd hm hi
  unfold scaleStep scale_one_raw
  have srcAdd := HeapWP.frame (R := pointsToRange raw_box.u32Repr dst dstBase target)
    (add_range_with.spec raw_box.u32Repr src srcBase source depth sourceView view i (by agrind) (by decide)
      (by agrind) srcFit)
  apply HeapWP.Spec.bind (srcAdd h F s hp hd hm hi)
  rintro q s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  obtain ⟨hprov, haddr, hp₁⟩ :
      q.provenance = src.provenance ∧ q.address.val = src.address.val + i.val * raw_box.u32Repr.size ∧
      sep sourceView
        (pointsToRange raw_box.u32Repr dst dstBase target) h₁ := by
    simpa only [sep_and_left] using hp₁
  have dstAdd := HeapWP.frame (R := sourceView)
    (add_range.spec raw_box.u32Repr dst dstBase target 0 i (by agrind) (by decide)
      (by agrind) dstFit)
  apply HeapWP.Spec.bind (dstAdd h₁ F s₁ ((sep_comm _ _ _).mp hp₁) hd₁ hm₁ hi₁)
  rintro q₁ s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
  obtain ⟨hprov₁, haddr₁, hp₂⟩ :
      q₁.provenance = dst.provenance ∧ q₁.address.val = dst.address.val + i.val * raw_box.u32Repr.size ∧
      sep (pointsToRange raw_box.u32Repr dst dstBase target)
        sourceView h₂ := by
    simpa only [sep_and_left] using hp₂
  have srcRead := HeapWP.frame (R := pointsToRange raw_box.u32Repr dst dstBase target)
    (read_range_with.spec raw_box.u32Repr src q srcBase source depth sourceView view ⟨i.val, hlt⟩
      (by decide) hprov haddr)
  apply HeapWP.Spec.bind (srcRead h₂ F s₂ ((sep_comm _ _ _).mp hp₂) hd₂ hm₂ hi₂)
  rintro value s₃ ⟨h₃, hd₃, hm₃, hi₃, hp₃⟩
  obtain ⟨hvalue, ranges₃⟩ :
      value = source[i.val] ∧ sep sourceView
        (pointsToRange raw_box.u32Repr dst dstBase target) h₃ := by
    simpa only [sep_and_left] using hp₃
  subst value
  simp only [lift, bind_ok]
  have dstWrite := HeapWP.frame (R := sourceView)
    (write_range.spec raw_box.u32Repr dst q₁ dstBase target ⟨i.val, hlt⟩
      (core.num.U32.wrapping_mul k source[i.val]) (by decide) hprov₁ haddr₁
      (raw_box.u32Repr_noPointers _))
  apply HeapWP.Spec.mono (dstWrite h₃ F s₃ ((sep_comm _ _ _).mp ranges₃) hd₃ hm₃ hi₃)
  rintro _ s₄ ⟨h₄, hd₄, hm₄, hi₄, hp₄⟩
  exact ⟨h₄, hd₄, hm₄, hi₄, (sep_comm _ _ _).mp hp₄⟩

theorem scaleStep.disjoint_spec (k : U32) (src dst : RawPtr U32)
    (srcBase dstBase : BasePtr) (source target : Vector U32 count) (depth : Nat)
    (i : Usize) (hlt : i.val < count)
    (srcFit : src.address.val + i.val * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize)
    (dstFit : dst.address.val + i.val * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize) :
    ⦃ pointsToRange raw_box.u32Repr src srcBase source depth ∗
      pointsToRange raw_box.u32Repr dst dstBase target ⦄
    scaleStep k src dst i
    ⦃ _ => pointsToRange raw_box.u32Repr src srcBase source depth ∗
      pointsToRange raw_box.u32Repr dst dstBase
        (target.set i.val (core.num.U32.wrapping_mul k source[i.val]) hlt) ⦄ :=
  scaleStep.disjoint_readable_spec k src dst srcBase dstBase source target depth _
    (fun _ => pointsToRange_readable) i hlt srcFit dstFit

/-- Read-only sources need decoding, not a canonical scalar write encoding.
    In particular, shared exposure may retain symbolic pointer lanes. -/
theorem scale_raw.disjoint_readable_spec (N : Usize) (k : U32) (src dst : RawPtr U32)
    (srcBase dstBase : BasePtr) (source target : Vector U32 N.val) (depth : Nat)
    (sourceView : Assertion)
    (view : ∀ h, sourceView h → readableRange raw_box.u32Repr src srcBase source depth h)
    (srcFit : ∀ i, i < N.val →
      src.address.val + i * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize)
    (dstFit : ∀ i, i < N.val →
      dst.address.val + i * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize) :
    ⦃ sourceView ∗ pointsToRange raw_box.u32Repr dst dstBase target ⦄
    scale_raw N k src dst
    ⦃ _ => sourceView ∗ pointsToRange raw_box.u32Repr dst dstBase (scaledWords k source) ⦄ := by
  have loop := scale_raw.rule N k src dst
    (fun stop => sep sourceView
      (pointsToRange raw_box.u32Repr dst dstBase (scaledPrefix k source target stop)))
  simp only [scaledPrefix_zero, scaledPrefix_all] at loop
  apply loop
  intro i hlt
  have body := scaleStep.disjoint_readable_spec k src dst srcBase dstBase source
    (scaledPrefix k source target i.val) depth sourceView view i hlt
    (srcFit i.val hlt) (dstFit i.val hlt)
  simpa only [scaledPrefix_next k source target ⟨i.val, hlt⟩] using body

/-- **Spec theorem for disjoint `raw_scale::scale_raw`**
    Preserves the source and scales every destination word. Separation is between
    byte ranges, not allocations; disjoint subranges of one allocation qualify. -/
theorem scale_raw.disjoint_spec (N : Usize) (k : U32) (src dst : RawPtr U32)
    (srcBase dstBase : BasePtr) (source target : Vector U32 N.val) (depth : Nat)
    (srcFit : ∀ i, i < N.val →
      src.address.val + i * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize)
    (dstFit : ∀ i, i < N.val →
      dst.address.val + i * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize) :
    ⦃ pointsToRange raw_box.u32Repr src srcBase source depth ∗
      pointsToRange raw_box.u32Repr dst dstBase target ⦄
    scale_raw N k src dst
    ⦃ _ => pointsToRange raw_box.u32Repr src srcBase source depth ∗
      pointsToRange raw_box.u32Repr dst dstBase (scaledWords k source) ⦄ := by
  have loop := scale_raw.rule N k src dst
    (fun stop => sep (pointsToRange raw_box.u32Repr src srcBase source depth)
      (pointsToRange raw_box.u32Repr dst dstBase (scaledPrefix k source target stop)))
  simp only [scaledPrefix_zero, scaledPrefix_all] at loop
  apply loop
  intro i hlt
  have body := scaleStep.disjoint_spec k src dst srcBase dstBase source
    (scaledPrefix k source target i.val) depth i hlt (srcFit i.val hlt) (dstFit i.val hlt)
  simpa only [scaledPrefix_next k source target ⟨i.val, hlt⟩] using body

/-- **Spec theorem for `raw_scale::scale_raw`**
    One calling convention covers an equal pair with one exclusive range, or
    two separated ranges with a preserved source. Neither case duplicates
    exclusive ownership; neither requires distinct allocations. -/
theorem scale_raw.spec (N : Usize) (k : U32) (src dst : RawPtr U32)
    (srcBase dstBase : BasePtr) (source target : Vector U32 N.val) (depth : Nat)
    (srcFit : ∀ i, i < N.val →
      src.address.val + i * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize)
    (dstFit : ∀ i, i < N.val →
      dst.address.val + i * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize) :
    ⦃ fun h => (src = dst ∧ pointsToRange raw_box.u32Repr src srcBase source 0 h) ∨
      (pointsToRange raw_box.u32Repr src srcBase source depth ∗
        pointsToRange raw_box.u32Repr dst dstBase target) h ⦄
    scale_raw N k src dst
    ⦃ _ => fun h =>
        (src = dst ∧ pointsToRange raw_box.u32Repr src srcBase (scaledWords k source) 0 h) ∨
        (pointsToRange raw_box.u32Repr src srcBase source depth ∗
          pointsToRange raw_box.u32Repr dst dstBase (scaledWords k source)) h ⦄ := by
  intro h F s hp hd hm hi
  rcases hp with ⟨same, hp⟩ | hp
  · subst dst
    apply HeapWP.Spec.mono (scale_raw.in_place_spec N k src srcBase source srcFit h F s hp hd hm hi)
    rintro _ s' ⟨h', hd', hm', hi', hp'⟩
    exact ⟨h', hd', hm', hi', Or.inl ⟨rfl, hp'⟩⟩
  · apply HeapWP.Spec.mono
      (scale_raw.disjoint_spec N k src dst srcBase dstBase source target depth
        srcFit dstFit h F s hp hd hm hi)
    rintro _ s' ⟨h', hd', hm', hi', hp'⟩
    exact ⟨h', hd', hm', hi', Or.inr hp'⟩

end raw_scale
