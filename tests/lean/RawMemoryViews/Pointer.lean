module

public import RawMemoryViews.Repr
public import Aeneas.Std.Heap.Notation
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Core.Ptr

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_memory_views

/- Adaptation of the emitted body: replace the opaque cast by the model's
   address/provenance-preserving cast and supply the missing usize descriptor. -/
def stored_pointer_address (h64 : UScalarTy.numBits .Usize = 64)
    (slot : ConstRawPtr (MutRawPtr U32)) : Result Usize := do
  let p ← Result.ok (slot.cast Usize)
  RawPtr.read (usizeRepr h64) p

private theorem pointer_address_readable (h64 : UScalarTy.numBits .Usize = 64)
    (slot : RawPtr (RawPtr U32)) (base : BasePtr) (target : RawPtr U32)
    (depth : Nat) (h : Fragment)
    (hp : pointsTo (Aeneas.Std.Repr.pointer U32) slot base target depth h) :
    readable (usizeRepr h64) (slot.cast Usize) base target.address depth h := by
  obtain ⟨bytes, encoded, lower, aligned, cells⟩ := hp
  change bytes = Aeneas.Std.Repr.pointerEncoding target at encoded
  subst bytes
  exact ⟨_, usizeRepr_pointer h64 target, lower, aligned, cells⟩

/-- **Spec theorem for `raw_memory_views::stored_pointer_address`**
    Numerical observation preserves the complete symbolic pointer encoding.
    No pointee permission is required, and no integer-to-pointer reconstruction occurs. -/
theorem stored_pointer_address.spec (h64 : UScalarTy.numBits .Usize = 64)
    (slot : ConstRawPtr (MutRawPtr U32)) (base : BasePtr) (target : MutRawPtr U32)
    (depth : Nat) :
    ⦃ pointsTo (Aeneas.Std.Repr.pointer U32) slot base target depth ⦄
    stored_pointer_address h64 slot
    ⦃ (result : Usize) => fun h =>
      result = target.address ∧
      pointsTo (Aeneas.Std.Repr.pointer U32) slot base target depth h ⦄ := by
  intro h F s₀ hp hd hm hi
  simp only [stored_pointer_address, bind_ok]
  have hr := read_of_readable (show 0 < (usizeRepr h64).size from by change 0 < 8; decide)
    (pointer_address_readable h64 slot base target depth h hp)
    ((Fragment.matches_union _ _ _).mp hm).1
  apply HeapWP.Spec.checkedModify.mpr
  refine ⟨⟨target.address, s₀, hr, rfl⟩, ?_⟩
  rintro result s₁ ⟨read, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (read.symm.trans hr), hp⟩

/-- The native test's continuation, generalized to arbitrary values and frames:
    reload the stored pointer after observing its address, then write/read its target. -/
theorem stored_pointer_address.use_spec (h64 : UScalarTy.numBits .Usize = 64)
    (slot : ConstRawPtr (MutRawPtr U32)) (base : BasePtr) (target : MutRawPtr U32)
    (targetBase : BasePtr) (old value : U32) (depth : Nat) :
    ⦃ pointsTo (Aeneas.Std.Repr.pointer U32) slot base target depth ∗
      pointsTo raw_box.u32Repr target targetBase old ⦄
    (do let address ← stored_pointer_address h64 slot
        let p ← RawPtr.read (Aeneas.Std.Repr.pointer U32) slot
        MutRawPtr.write raw_box.u32Repr p value
        let result ← RawPtr.read raw_box.u32Repr p
        pure (address, result))
    ⦃ (address : Usize) (result : U32) => fun h =>
      address = target.address ∧ result = value ∧
      (pointsTo (Aeneas.Std.Repr.pointer U32) slot base target depth ∗
        pointsTo raw_box.u32Repr target targetBase value) h ⦄ := by
  intro h F s₀ hp hd hm hi
  apply HeapWP.Spec.bind
    (HeapWP.frame (stored_pointer_address.spec h64 slot base target depth) h F s₀ hp hd hm hi)
  rintro address s₁ ⟨h₁, hd₁, hm₁, hi₁, post⟩
  obtain ⟨ha, hp₁⟩ := (sep_and_left _ _ _ h₁).mp post
  apply HeapWP.Spec.bind (HeapWP.frame
    (HeapWP.read.spec (Aeneas.Std.Repr.pointer U32) slot base target depth (by decide))
      h₁ F s₁ hp₁ hd₁ hm₁ hi₁)
  rintro p s₂ ⟨h₂, hd₂, hm₂, hi₂, post⟩
  obtain ⟨he, hp₂⟩ := (sep_and_left _ _ _ h₂).mp post
  subst p
  apply HeapWP.Spec.bind (HeapWP.frame
    (HeapWP.write.spec raw_box.u32Repr target targetBase old value
      (raw_box.u32Repr_noPointers value) (by decide))
      h₂ F s₂ ((sep_comm _ _ _).mp hp₂) hd₂ hm₂ hi₂)
  rintro _ s₃ ⟨h₃, hd₃, hm₃, hi₃, hp₃⟩
  apply HeapWP.Spec.bind (HeapWP.frame
    (HeapWP.read.spec raw_box.u32Repr target targetBase value 0 (by decide))
      h₃ F s₃ hp₃ hd₃ hm₃ hi₃)
  rintro result s₄ ⟨h₄, hd₄, hm₄, hi₄, post⟩
  obtain ⟨hr, hp₄⟩ := (sep_and_left _ _ _ h₄).mp post
  exact (HeapWP.Spec.pure _ _ _).mpr
    ⟨h₄, hd₄, hm₄, hi₄, ha, hr, (sep_comm _ _ _).mp hp₄⟩

end raw_memory_views
