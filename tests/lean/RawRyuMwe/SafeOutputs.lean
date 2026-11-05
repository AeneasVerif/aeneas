module

public import RawRyuMwe.Outputs
public import RawRyuMwe.Storage
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Repr

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic scalar_mwe
open scoped Aeneas.Std.HeapWP

namespace raw_ryu_mwe

def initialized_outputs_scoped (a b : U64) (firstAddress secondAddress : BasePtr) :
    Result (U64 × U64) := do
  let first ← exposeBytes (List.replicate 8 .uninit) 0 firstAddress
  let second ← exposeBytes (List.replicate 8 .uninit) 0 secondAddress
  let result ← initialized_outputs a b (first.cast U64) (second.cast U64)
  closeBytes second 8 0
  closeBytes first 8 0
  pure result

/-- **Spec theorem for `raw_ryu_mwe::initialized_outputs`**
    Includes both local materializations and scope returns. `assume_init` is an
    actual aligned heap read after the two writes, not a success axiom. -/
theorem initialized_outputs_scoped.spec (a b : U64) (firstAddress secondAddress : BasePtr)
    (firstAligned : 8 ∣ firstAddress.val) (secondAligned : 8 ∣ secondAddress.val)
    (F : Fragment) (s₀ : Heap) (hm : Fragment.Matches s₀ F) (hi : s₀.Inv) :
    HeapWP.Spec (initialized_outputs_scoped a b firstAddress secondAddress)
      (fun result s₁ => result = (a, b) ∧ s₁.Inv ∧ Fragment.Matches s₁ F) s₀ := by
  let old : Vector Aeneas.Std.Byte 8 := Vector.replicate 8 .uninit
  unfold initialized_outputs_scoped
  apply HeapWP.Spec.bind (exposeBytes.spec _ 0 firstAddress s₀ F hi hm)
  rintro first s₁ ⟨firstAddr, _, h₁, hd₁, hm₁, hi₁, hp₁⟩
  apply HeapWP.Spec.bind (exposeBytes.spec _ 0 secondAddress s₁ (h₁ ∪ F) hi₁ hm₁)
  rintro second s₂ ⟨secondAddr, _, h₂, hd₂, hm₂, hi₂, hp₂⟩
  have localRun : HeapWP.Triple
      (bytesAt first first.address old.toList ∗ bytesAt second second.address old.toList)
      (initialized_outputs a b (first.cast U64) (second.cast U64))
      (fun result h => result = (a, b) ∧
        (bytesAt first first.address ((bytes64 a).toList.map Byte.data) ∗
          bytesAt second second.address ((bytes64 b).toList.map Byte.data)) h) := by
    intro h G s hp hd hm hi
    have pre :
        (block u64Repr (first.cast U64) first.address (old.map (Cell.shared 0)).toList ∗
          block u64Repr (second.cast U64) second.address (old.map (Cell.shared 0)).toList) h := by
      simpa [sep, block, bytesAt, u64Repr, codec, Repr.u8, RawPtr.cast, RawPtr.offsetFrom,
        Vector.toList_map, firstAddr, secondAddr, firstAligned, secondAligned] using hp
    apply HeapWP.Spec.mono (initialized_outputs.spec a b (first.cast U64) (second.cast U64)
      first.address second.address old old h G s pre hd hm hi)
    rintro ⟨x, y⟩ s₁ ⟨h₁, hd₁, hm₁, hi₁, rfl, rfl, values⟩
    refine ⟨h₁, hd₁, hm₁, hi₁, rfl, ?_⟩
    simpa [sep, pointsTo, block, bytesAt, u64Repr, codec, Repr.u8, RawPtr.cast,
      RawPtr.offsetFrom, Vector.toList_map, firstAddr, secondAddr, firstAligned, secondAligned] using values
  have body := preserve_two_storage first second old.toList ((bytes64 a).toList.map Byte.data)
    old.toList ((bytes64 b).toList.map Byte.data) 0 0 _ (fun result => result = (a, b))
    (by simp [bytes64, raw_memory_views.addressBytes]) (by simp [bytes64, raw_memory_views.addressBytes]) localRun
  have separated := (Fragment.disjoint_union_right.mp hd₂).1.symm
  have frames := Fragment.disjoint_union_left.mpr ⟨hd₁, (Fragment.disjoint_union_right.mp hd₂).2⟩
  have matching : Fragment.Matches s₂ ((h₁ ∪ h₂) ∪ F) := by
    simp only [Fragment.matches_union] at hm₂ ⊢
    tauto
  apply HeapWP.Spec.bind (body (h₁ ∪ h₂) F s₂
    ⟨h₁, h₂, separated, rfl, hp₁, hp₂⟩ frames matching hi₂)
  rintro result s₃ ⟨h₃, hd₃, hm₃, hi₃, resultEq, aH, bH, ab, union, ap, bp⟩
  subst result
  have bFrame := Fragment.disjoint_union_right.mpr
    ⟨ab.symm, (Fragment.disjoint_union_left.mp (union ▸ hd₃)).2⟩
  have bMatch : Fragment.Matches s₃ (bH ∪ (aH ∪ F)) := by
    simp only [union, Fragment.matches_union] at hm₃ ⊢
    tauto
  have closeSecond := closeBytes.state_spec second _ 0 bH (aH ∪ F) s₃ bp bFrame bMatch hi₃
  simp only [List.length_map, Vector.length_toList] at closeSecond
  apply HeapWP.Spec.bind closeSecond
  rintro _ s₄ ⟨hi₄, hm₄, _, _⟩
  have closeFirst := closeBytes.state_spec first _ 0 aH F s₄ ap
    (Fragment.disjoint_union_left.mp (union ▸ hd₃)).1 hm₄ hi₄
  simp only [List.length_map, Vector.length_toList] at closeFirst
  apply HeapWP.Spec.bind closeFirst
  rintro _ s₅ ⟨hi₅, hm₅, _, _⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨rfl, hi₅, hm₅⟩

end raw_ryu_mwe
