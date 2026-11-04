module

public import RawScale.Exposure
import all Aeneas.Std.Core.Ptr

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_scale

/- The opening paper example has no iterator, pointer arithmetic, or array layout.
   These framed heap contracts preserve arbitrary unrelated resources. OOM is
   accepted at safe-to-raw exposure; invalid reads and writes are still rejected. -/

/-- **Spec theorem for `raw_scale::scale_one_raw` (equal pointers)**
    One exclusive word is replaced by its wrapping product. -/
theorem scale_one_raw.in_place_spec (k : U32) (p : RawPtr U32)
    (base : BasePtr) (value : U32) :
    ⦃ readable raw_box.u32Repr p base value ⦄
    scale_one_raw k p p
    ⦃ _ => pointsTo raw_box.u32Repr p base (core.num.U32.wrapping_mul k value) ⦄ := by
  intro h F s₀ hp hd hm hi
  unfold scale_one_raw
  apply HeapWP.Spec.bind (HeapWP.read_exposed.spec raw_box.u32Repr p base value 0
    (by decide) h F s₀ hp hd hm hi)
  rintro x s₁ ⟨h₁, hd₁, hm₁, hi₁, hx, hp₁⟩
  subst x
  simp only [lift, bind_ok]
  exact HeapWP.write_readable.spec raw_box.u32Repr p base value _
    (raw_box.u32Repr_noPointers _) (by decide) h₁ F s₁ hp₁ hd₁ hm₁ hi₁

/-- **Spec theorem for `raw_scale::scale_one_raw` (disjoint pointers)**
    Preserve the readable source and overwrite the exclusive destination. -/
theorem scale_one_raw.disjoint_spec (k : U32) (src dst : RawPtr U32)
    (srcBase dstBase : BasePtr) (value old : U32) (depth : Nat) :
    ⦃ readable raw_box.u32Repr src srcBase value depth ∗
      readable raw_box.u32Repr dst dstBase old ⦄
    scale_one_raw k src dst
    ⦃ _ => readable raw_box.u32Repr src srcBase value depth ∗
      pointsTo raw_box.u32Repr dst dstBase (core.num.U32.wrapping_mul k value) ⦄ := by
  intro h F s₀ hp hd hm hi
  unfold scale_one_raw
  have read := HeapWP.frame (R := readable raw_box.u32Repr dst dstBase old)
    (HeapWP.read_exposed.spec raw_box.u32Repr src srcBase value depth (by decide))
  apply HeapWP.Spec.bind (read h F s₀ hp hd hm hi)
  rintro x s₁ ⟨h₁, hd₁, hm₁, hi₁, post⟩
  obtain ⟨hx, hp₁⟩ := (sep_and_left _ _ _ h₁).mp post
  subst x
  simp only [lift, bind_ok]
  have write := HeapWP.frame (R := readable raw_box.u32Repr src srcBase value depth)
    (HeapWP.write_readable.spec raw_box.u32Repr dst dstBase old
      (core.num.U32.wrapping_mul k value)
      (raw_box.u32Repr_noPointers _) (by decide))
  apply HeapWP.Spec.mono (write h₁ F s₁ ((sep_comm _ _ _).mp hp₁) hd₁ hm₁ hi₁)
  rintro _ s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
  exact ⟨h₂, hd₂, hm₂, hi₂, (sep_comm _ _ _).mp hp₂⟩

/-- **Spec theorem for `raw_scale::scale_one_raw` (disjoint or equal)**
    The equal case needs one exclusive permission, not two overlapping ones. -/
theorem scale_one_raw.spec (k : U32) (src dst : RawPtr U32)
    (srcBase dstBase : BasePtr) (value old : U32) (depth : Nat) :
    ⦃ fun h =>
      (src = dst ∧ readable raw_box.u32Repr dst dstBase value 0 h) ∨
      (readable raw_box.u32Repr src srcBase value depth ∗
        readable raw_box.u32Repr dst dstBase old) h ⦄
    scale_one_raw k src dst
    ⦃ _ => fun h =>
      (src = dst ∧ pointsTo raw_box.u32Repr dst dstBase
        (core.num.U32.wrapping_mul k value) 0 h) ∨
      (readable raw_box.u32Repr src srcBase value depth ∗
        pointsTo raw_box.u32Repr dst dstBase (core.num.U32.wrapping_mul k value)) h ⦄ := by
  intro h F s₀ hp hd hm hi
  rcases hp with ⟨heq, hp⟩ | hp
  · subst src
    apply HeapWP.Spec.mono (scale_one_raw.in_place_spec k dst dstBase value h F s₀ hp hd hm hi)
    rintro _ s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
    exact ⟨h₁, hd₁, hm₁, hi₁, Or.inl ⟨rfl, hp₁⟩⟩
  · apply HeapWP.Spec.mono
      (scale_one_raw.disjoint_spec k src dst srcBase dstBase value old depth h F s₀ hp hd hm hi)
    rintro _ s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
    exact ⟨h₁, hd₁, hm₁, hi₁, Or.inr hp₁⟩

/-- **Spec theorem for `raw_scale::scale_one_in_place`**
    Return the wrapping product and retire the temporary exposure. -/
theorem scale_one_in_place.spec (k value : U32) :
    ⦃ empty ⦄ scale_one_in_place k value
    ⦃ (result : U32) => fun h =>
      result = core.num.U32.wrapping_mul k value ∧ empty h ⦄ := by
  intro h F s₀ rfl _ hm hi
  simp only [Fragment.empty_union] at hm
  simp only [scale_one_in_place, core.ptr.from_mut, Aeneas.Std.bind_assoc, bind_ok, ext.cast]
  apply HeapWP.Spec.bind
    (HeapWP.allocExposure.spec raw_box.u32Repr value s₀ F hi hm)
  rintro p s₁ ⟨_, h₁, hd₁, hm₁, hi₁, hp₁⟩
  have kernel := HeapWP.frame (R := alloc raw_box.u32Repr p p.address 1 false)
    (scale_one_raw.in_place_spec k p p.address value)
  apply HeapWP.Spec.bind (kernel h₁ F s₁ ((sep_comm _ _ _).mp hp₁) hd₁ hm₁ hi₁)
  rintro _ s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
  have restored := sep_mono (fun _ hp => hp) (fun _ => pointsTo_readable)
    ((sep_comm _ _ _).mp hp₂)
  exact HeapWP.end_from_mut.spec raw_box.u32Repr p p.address _
    (by decide) h₂ F s₂ restored hd₂ hm₂ hi₂

/-- **Spec theorem for `raw_scale::scale_one_into`**
    Return the source's wrapping product, independently of the old destination,
    and retire both temporary exposures. -/
theorem scale_one_into.spec (k src dst : U32) :
    ⦃ empty ⦄ scale_one_into k src dst
    ⦃ (result : U32) => fun h =>
      result = core.num.U32.wrapping_mul k src ∧ empty h ⦄ := by
  intro h F s₀ rfl _ hm hi
  simp only [Fragment.empty_union] at hm
  simp only [scale_one_into, core.ptr.from_ref, core.ptr.from_mut, Aeneas.Std.bind_assoc, bind_ok]
  apply HeapWP.Spec.bind (shared_exposure.spec raw_box.u32Repr src s₀ F hi hm)
  rintro p s₁ ⟨_, a, haF, hm₁, hi₁, source⟩
  apply HeapWP.Spec.bind
    (HeapWP.allocExposure.spec raw_box.u32Repr dst s₁ (a ∪ F) hi₁ hm₁)
  rintro q s₂ ⟨_, b, hb, hm₂, hi₂, target⟩
  obtain ⟨hba, hbF⟩ := Fragment.disjoint_union_right.mp hb
  have read := HeapWP.frame (R := alloc raw_box.u32Repr p p.address 1 false)
    (HeapWP.read_exposed.spec raw_box.u32Repr p p.address src 1 (by decide))
  unfold scale_one_raw
  simp only [Aeneas.Std.bind_assoc]
  have sourceMatch : Fragment.Matches s₂ (a ∪ (b ∪ F)) := by
    rw [← Fragment.union_assoc, Fragment.union_comm a b, Fragment.union_assoc]
    exact hm₂
  apply HeapWP.Spec.bind (read a (b ∪ F) s₂ ((sep_comm _ _ _).mp source)
    (Fragment.disjoint_union_right.mpr ⟨hba.symm, haF⟩) sourceMatch hi₂)
  rintro value s₃ ⟨a₃, ha₃, hm₃, hi₃, post⟩
  obtain ⟨hvalue, source₃⟩ := (sep_and_left _ _ _ a₃).mp post
  subst value
  simp only [lift, bind_ok]
  have hd₃ := Fragment.disjoint_union_right.mp ha₃
  have targetMatch : Fragment.Matches s₃ (b ∪ (a₃ ∪ F)) := by
    rw [← Fragment.union_assoc, Fragment.union_comm b a₃, Fragment.union_assoc]
    exact hm₃
  have write := HeapWP.frame (R := alloc raw_box.u32Repr q q.address 1 false)
    (HeapWP.write_readable.spec raw_box.u32Repr q q.address dst
      (core.num.U32.wrapping_mul k src)
      (raw_box.u32Repr_noPointers _) (by decide))
  apply HeapWP.Spec.bind (write b (a₃ ∪ F) s₃ ((sep_comm _ _ _).mp target)
    (Fragment.disjoint_union_right.mpr ⟨hd₃.1.symm, hbF⟩) targetMatch hi₃)
  rintro _ s₄ ⟨b₄, hb₄, hm₄, hi₄, target₄⟩
  have restored := sep_mono (fun _ hp => hp) (fun _ => pointsTo_readable)
    ((sep_comm _ _ _).mp target₄)
  apply HeapWP.Spec.bind (HeapWP.end_from_mut.spec raw_box.u32Repr q q.address _
    (by decide) b₄ (a₃ ∪ F) s₄ restored hb₄ hm₄ hi₄)
  rintro result s₅ ⟨_, _, hm₅, hi₅, result_eq, rfl⟩
  simp only [Fragment.empty_union] at hm₅
  apply HeapWP.Spec.bind (shared_end.spec raw_box.u32Repr p src
    (by decide) a₃ F s₅ ((sep_comm _ _ _).mp source₃) hd₃.2 hm₅ hi₅)
  rintro _ s₆ ⟨h₆, hd₆, hm₆, hi₆, hempty⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨h₆, hd₆, hm₆, hi₆, result_eq, hempty⟩

end raw_scale
