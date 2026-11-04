module

public import RawScale.Scalar
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Primitives

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic
open scoped Aeneas.Std.HeapWP

namespace raw_scale

private theorem sep_exchange (P Q R S : Assertion) (h : Fragment) :
    ((P ∗ Q) ∗ (R ∗ S)) h ↔ ((P ∗ R) ∗ (Q ∗ S)) h := by
  have move : ∀ h, (Q ∗ (R ∗ S)) h ↔ (R ∗ (Q ∗ S)) h := by
    intro h
    have swap : (Q ∗ R) = (R ∗ Q) := funext fun h => propext (sep_comm Q R h)
    rw [← sep_assoc, swap, sep_assoc]
  rw [sep_assoc, sep_assoc]
  constructor
  · exact sep_mono (fun _ hp => hp) (fun h => (move h).mp)
  · exact sep_mono (fun _ hp => hp) (fun h => (move h).mpr)

def scaledRow (k : U32) (row : Row13) : Row13 :=
  rowOfWords (scaledWords k (rowWords row))

local macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| agrind)

theorem scaledRow_get (k : U32) (row : Row13) (i : Nat) (hi : i < 16) :
    (scaledRow k row).val[i] = core.num.U32.wrapping_mul k row.val[i] := by
  simp [scaledRow, rowOfWords, scaledWords, rowWords]

theorem scaledRow_zero_padding (k : U32) (row : Row13)
    (padding : ∀ i, 13 ≤ i → (hi : i < 16) → row.val[i] = 0#u32) :
    ∀ i, 13 ≤ i → (hi : i < 16) → (scaledRow k row).val[i] = 0#u32 := by
  intro i hlo hi
  rw [scaledRow_get k row i hi, padding i hlo hi]
  bv_tac 32

private theorem row_pointer_facts (p : RawPtr Row13) (row : Row13) (depth : Nat)
    (s : Heap) (h : Fragment)
    (hp : (alloc rowRepr p p.address 1 false ∗ readable rowRepr p p.address row depth) h)
    (hm : Fragment.Matches s h) (hi : s.Inv) :
    32 ∣ p.address.val ∧ ∀ i, i < 16 →
      p.address.val + i * raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize := by
  obtain ⟨blk, hl, _, haddr, aligned, _, hlen, _, _⟩ :=
    whole_readable (by decide : 0 < rowRepr.size) hp hm
  have bounded := hi.validBlock hl
  simp only [Heap.validBlock, Bool.and_eq_true] at bounded
  have hb : 0 < blk.bptr.val ∧
      blk.bptr.val + blk.repr.length < 2 ^ UScalarTy.numBits .Usize := by
    simpa [Heap.bounded] using bounded.1.1
  change blk.repr.length = 64 at hlen
  change 32 ∣ blk.bptr.val at aligned
  constructor
  · simpa [haddr] using aligned
  · intro i hi
    change p.address.val + i * 4 < _
    rw [haddr]
    agrind

theorem scale_in_place_tail.spec (k : U32) (p : RawPtr Row13) (buf : Row13) :
    ⦃ alloc rowRepr p p.address 1 false ∗ pointsTo rowRepr p p.address buf ⦄
    (do scale_raw 16#usize k (p.cast U32) (p.cast U32)
        core.ptr.end_from_mut rowRepr p)
    ⦃ (result : Row13) => fun h => result = scaledRow k buf ∧ empty h ⦄ := by
  intro h F s hp hd hm hi
  have readable := sep_mono (fun _ hp => hp) (fun _ => pointsTo_readable) hp
  obtain ⟨aligned, fit⟩ := row_pointer_facts p buf 0 s h readable
    ((Fragment.matches_union _ _ _).mp hm).1 hi
  have kernel := HeapWP.frame (R := alloc rowRepr p p.address 1 false)
    (scale_raw.in_place_spec 16#usize k (p.cast U32) p.address (rowWords buf) fit)
  have words := sep_mono (fun _ hp => hp) (row_to_words p p.address buf 0) hp
  apply HeapWP.Spec.bind (kernel h F s ((sep_comm _ _ _).mp words) hd hm hi)
  rintro _ s' ⟨h', hd', hm', hi', hp'⟩
  have restored := sep_mono
    (fun h hp => pointsTo_readable
      (words_to_row p p.address (scaledWords k (rowWords buf)) 0 h aligned hp))
    (fun _ hp => hp) hp'
  exact HeapWP.end_from_mut.spec rowRepr p p.address (scaledRow k buf) (by decide)
    h' F s' ((sep_comm _ _ _).mp restored) hd' hm' hi'

/-- **Spec theorem for `raw_scale::scale_in_place`**
    All sixteen physical words are scaled modulo 2^32; the matching backward
    computation returns the updated safe row and retires its temporary exposure.
    Unavailable exposure placement may abort with OOM. -/
theorem scale_in_place.spec (k : U32) (buf : Row13) :
    ⦃ empty ⦄ scale_in_place k buf
    ⦃ (result : Row13) => fun h => result = scaledRow k buf ∧ empty h ⦄ := by
  intro h F s rfl _ hm hi
  simp only [Fragment.empty_union] at hm
  simp only [scale_in_place, ext.row_as_mut_ptr, core.ptr.from_mut,
    Aeneas.Std.bind_assoc, bind_ok, ext.cast]
  apply HeapWP.Spec.bind
    (HeapWP.allocExposure_encoded.spec rowRepr buf (rowRepr_calibrated buf) s F hi hm)
  rintro p s' ⟨_, h, hd, hm', hi', hp⟩
  exact scale_in_place_tail.spec k p buf h F s' hp hd hm' hi'

theorem scale_into_tail.spec (k : U32) (p q : RawPtr Row13) (src dst : Row13) :
    ⦃ (alloc rowRepr p p.address 1 false ∗ readable rowRepr p p.address src 1) ∗
      (alloc rowRepr q q.address 1 false ∗ pointsTo rowRepr q q.address dst) ⦄
    (do scale_raw 16#usize k (p.cast U32) (q.cast U32)
        let result ← core.ptr.end_from_mut rowRepr q
        p.endSharedExposure rowRepr [src]
        pure result)
    ⦃ (result : Row13) => fun h => result = scaledRow k src ∧ empty h ⦄ := by
  intro h F s hp hd hm hi
  have keep := hp
  obtain ⟨a, b, _, hh, source, target⟩ := hp
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  rw [hh, Fragment.matches_union] at localMatch
  have srcFit := (row_pointer_facts p src 1 s a source localMatch.1 hi).2
  have targetReadable := sep_mono (fun _ hp => hp) (fun _ => pointsTo_readable) target
  obtain ⟨aligned, dstFit⟩ := row_pointer_facts q dst 0 s b targetReadable localMatch.2 hi
  have kernel := HeapWP.frame
    (R := alloc rowRepr p p.address 1 false ∗ alloc rowRepr q q.address 1 false)
    (scale_raw.disjoint_readable_spec 16#usize k (p.cast U32) (q.cast U32)
      p.address q.address (rowWords src) (rowWords dst) 1
      (readable rowRepr p p.address src 1) (readable_row_to_words p p.address src 1)
      srcFit dstFit)
  have words := sep_mono (fun _ hp => hp)
    (fun _ => sep_mono (fun _ hp => hp) (row_to_words q q.address dst 0)) keep
  have reordered := (sep_exchange _ _ _ _ h).mp words
  apply HeapWP.Spec.bind (kernel h F s ((sep_comm _ _ _).mp reordered) hd hm hi)
  rintro _ s' ⟨h', hd', hm', hi', hp'⟩
  have restored := sep_mono
    (fun _ => sep_mono (fun _ hp => hp)
      (fun h hp => pointsTo_readable
        (words_to_row q q.address (scaledWords k (rowWords src)) 0 h aligned hp)))
    (fun _ hp => hp) hp'
  have paired := (sep_exchange _ _ _ _ h').mpr ((sep_comm _ _ _).mp restored)
  have back := HeapWP.frame (R := alloc rowRepr p p.address 1 false ∗
    readable rowRepr p p.address src 1)
    (HeapWP.end_from_mut.spec rowRepr q q.address (scaledRow k src) (by decide))
  apply HeapWP.Spec.bind (back h' F s' ((sep_comm _ _ _).mp paired) hd' hm' hi')
  rintro result s'' ⟨h'', hd'', hm'', hi'', post⟩
  obtain ⟨result_eq, source⟩ :
      result = scaledRow k src ∧
      (alloc rowRepr p p.address 1 false ∗ readable rowRepr p p.address src 1) h'' := by
    simpa only [sep_and_left, sep_empty_left] using post
  apply HeapWP.Spec.bind (shared_end.spec rowRepr p src (by decide) h'' F s''
    source hd'' hm'' hi'')
  rintro _ s₃ ⟨h₃, hd₃, hm₃, hi₃, hemp⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨h₃, hd₃, hm₃, hi₃, result_eq, hemp⟩

/-- **Spec theorem for `raw_scale::scale_into`**
    The returned safe row is the pointwise wrapping product of `k` and `src`,
    independently of `dst`. Both temporary exposures are retired; the external
    frame is preserved on success; unavailable placement may abort with OOM. -/
theorem scale_into.spec (k : U32) (src dst : Row13) :
    ⦃ empty ⦄ scale_into k src dst
    ⦃ (result : Row13) => fun h => result = scaledRow k src ∧ empty h ⦄ := by
  intro h F s rfl _ hm hi
  simp only [Fragment.empty_union] at hm
  simp only [scale_into, ext.row_as_ptr, ext.row_as_mut_ptr, core.ptr.from_ref, core.ptr.from_mut,
    Aeneas.Std.bind_assoc, bind_ok]
  apply HeapWP.Spec.bind (shared_exposure.spec rowRepr src s F hi hm)
  rintro p s₁ ⟨run, a, haF, hm₁, hi₁, source⟩
  apply HeapWP.Spec.bind (HeapWP.allocExposure_encoded.spec rowRepr dst
    (rowRepr_calibrated dst) s₁ (a ∪ F) hi₁ hm₁)
  rintro q s₂ ⟨_, b, hb, hm₂, hi₂, target⟩
  obtain ⟨hba, hbF⟩ := Fragment.disjoint_union_right.mp hb
  have pre :
      ((alloc rowRepr p p.address 1 false ∗ readable rowRepr p p.address src 1) ∗
        (alloc rowRepr q q.address 1 false ∗ pointsTo rowRepr q q.address dst)) (b ∪ a) :=
    (sep_comm _ _ _).mp ⟨b, a, hba, rfl, target, source⟩
  have combinedMatch : Fragment.Matches s₂ ((b ∪ a) ∪ F) := by
    simpa only [Fragment.union_assoc] using hm₂
  exact scale_into_tail.spec k p q src dst (b ∪ a) F s₂ pre
    (Fragment.disjoint_union_left.mpr ⟨hbF, haF⟩) combinedMatch hi₂

theorem scale_via_borrow_tail.spec (k : U32) (p : RawPtr Row13) (buf : Row13) :
    ⦃ alloc rowRepr p p.address 1 false ∗ pointsTo rowRepr p p.address buf ⦄
    (do let result ← scale_via_borrow_raw k (p.cast U32)
        let buf ← core.ptr.end_from_mut rowRepr p
        pure (result, buf))
    ⦃ (result : U32) (updated : Row13) => fun h =>
      result = (scaledWords k (rowWords buf))[0] ∧ updated = scaledRow k buf ∧ empty h ⦄ := by
  intro h F s₀ hp hd hm hi
  have readable := sep_mono (fun _ hp => hp) (fun _ => pointsTo_readable) hp
  have aligned := (row_pointer_facts p buf 0 s₀ h readable
    ((Fragment.matches_union _ _ _).mp hm).1 hi).1
  have kernel := HeapWP.frame (R := alloc rowRepr p p.address 1 false)
    (scale_via_borrow_raw.spec k (p.cast U32) p.address (rowWords buf))
  have words := sep_mono (fun _ hp => hp) (row_to_words p p.address buf 0) hp
  apply HeapWP.Spec.bind (kernel h F s₀ ((sep_comm _ _ _).mp words) hd hm hi)
  rintro result s₁ ⟨h₁, hd₁, hm₁, hi₁, post⟩
  obtain ⟨hr, hp₁⟩ := (sep_and_left _ _ _ h₁).mp post
  have restored := sep_mono
    (fun h hp => pointsTo_readable
      (words_to_row p p.address (scaledWords k (rowWords buf)) 0 h aligned hp))
    (fun _ hp => hp) hp₁
  apply HeapWP.Spec.bind (HeapWP.end_from_mut.spec rowRepr p p.address
    (scaledRow k buf) (by decide) h₁ F s₁ ((sep_comm _ _ _).mp restored) hd₁ hm₁ hi₁)
  rintro updated s₂ ⟨h₂, hd₂, hm₂, hi₂, hu, hemp⟩
  exact (HeapWP.Spec.pure _ _ _).mpr ⟨h₂, hd₂, hm₂, hi₂, hr, hu, hemp⟩

/-- **Spec theorem for `raw_scale::scale_via_borrow`**
    The safe row is scaled through a temporary raw pointer and flat safe borrow.
    Both matching backward computations run; the returned scalar is the first
    scaled word, and the external heap frame is preserved. -/
theorem scale_via_borrow.spec (k : U32) (buf : Row13) :
    ⦃ empty ⦄ scale_via_borrow k buf
    ⦃ (result : U32) (updated : Row13) => fun h =>
      result = (scaledWords k (rowWords buf))[0] ∧ updated = scaledRow k buf ∧ empty h ⦄ := by
  intro h F s₀ rfl _ hm hi
  simp only [Fragment.empty_union] at hm
  simp only [scale_via_borrow, ext.row_as_mut_ptr, core.ptr.from_mut,
    Aeneas.Std.bind_assoc, bind_ok]
  apply HeapWP.Spec.bind
    (HeapWP.allocExposure_encoded.spec rowRepr buf (rowRepr_calibrated buf) s₀ F hi hm)
  rintro p s₁ ⟨_, h, hd, hm₁, hi₁, hp⟩
  exact scale_via_borrow_tail.spec k p buf h F s₁ hp hd hm₁ hi₁

end raw_scale
