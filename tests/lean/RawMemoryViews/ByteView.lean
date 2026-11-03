module

public import RawMemoryViews.ByteLayout
public import RawScale.Notation
public import Aeneas.Std.Heap.RangeRestoration
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Slice
import all Aeneas.Std.Primitives
import all Aeneas.Std.Heap.Repr

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_memory_views

set_option maxHeartbeats 1000000

local macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| agrind)

/-- Little-endian specialization of the two `to_ne_bytes` calls. -/
def nativeBytes (word : U16) : Result (Aeneas.Std.Array U8 2#usize) :=
  .ok (.from (u16Bytes word).toList (by simp))

/-- Adapted emitted byte assignments, including the missing final assignment. -/
def updateByteEnds (bytes : Slice U8) (first last : U16) : Result (Slice U8) := do
  let firstBytes ← nativeBytes first
  let lastBytes ← nativeBytes last
  let low ← Array.index_usize firstBytes 0#usize
  let bytes ← Slice.update bytes 0#usize low
  let high ← Array.index_usize firstBytes 1#usize
  let bytes ← Slice.update bytes 1#usize high
  let low ← Array.index_usize lastBytes 0#usize
  let bytes ← Slice.update bytes 14#usize low
  let high ← Array.index_usize lastBytes 1#usize
  Slice.update bytes 15#usize high

def updatedBytes (bytes : Vector U8 16) (first last : U16) : Vector U8 16 :=
  (((bytes.set 0 (u16Bytes first)[0]).set 1 (u16Bytes first)[1]).set
    14 (u16Bytes last)[0]).set 15 (u16Bytes last)[1]

def updatedWords (words : Words) (first last : U16) : Words :=
  ofWordVector (((wordVector words).set 0 first).set 7 last)

unseal Result in
/-- **Spec theorem for `raw_memory_views::update_word_bytes`'s safe byte updates.**
    All four assignments succeed and every other byte is unchanged. -/
theorem updateByteEnds.spec (bytes : Slice U8) (initial : Vector U8 16)
    (first last : U16) (he : bytes.val = initial.toList) :
    updateByteEnds bytes first last ⦃ (result : Slice U8) =>
      result.val = (updatedBytes initial first last).toList ⦄ := by
  have hlen : bytes.length = 16 := by simp [Slice.length, he]
  unfold updateByteEnds nativeBytes
  simp only [bind_ok]
  step*
  · simp_lists [*, updatedBytes]
    simp_scalar
  · simp_lists [*, updatedBytes]
    simp_scalar
    simp

theorem decodeWords_updatedBytes (bytes : Vector U8 16) (first last : U16) :
    decodeWords (updatedBytes bytes first last) =
      ((decodeWords bytes).set 0 first).set 7 last := by
  apply Vector.ext
  intro i hi
  by_cases h0 : i = 0
  · subst i
    simp [decodeWords, updatedBytes, u16Bytes_roundtrip]
  · by_cases h7 : i = 7
    · subst i
      simp [decodeWords, updatedBytes, u16Bytes_roundtrip]
    · have hlow : 2 ≤ 2 * i ∧ 2 * i + 1 < 14 := by scalar_tac
      simp [decodeWords, updatedBytes, Vector.getElem_set, h0, h7]
      agrind

/-- The six middle words are preserved, not merely the array length. -/
theorem updatedWords_get (words : Words) (first last : U16) (i : Fin 8) :
    (wordVector (updatedWords words first last))[i.val] =
      if i.val = 0 then first else if i.val = 7 then last else (wordVector words)[i.val] := by
  simp [updatedWords, Vector.getElem_set]
  agrind

/- The extracted slice exposure loses its backward function. This adapted tail
   borrows the same sixteen bytes and executes the matching effectful callback. -/
def update_word_bytes_raw (p : MutRawPtr Words) (first last : U16) : Result Unit := do
  let (bytes, back) ← core.slice.raw.from_raw_parts_mut Aeneas.Std.Repr.u8
    (p.cast U8) 16#usize
  let updated ← updateByteEnds bytes first last
  back updated

open SepLogic
open scoped Aeneas.Std.HeapWP

unseal Result in
private theorem pure_spec_heap {α : Type} {c : Result α} {P : α → Prop}
    (hc : WP.spec c P) (s : Heap) :
    HeapWP.Spec c (fun result s' => P result ∧ s' = s) s := by
  cases c
  · rename_i result
    exact (HeapWP.Spec.pure result _ s).mpr ⟨(WP.spec_ok result).mp hc, rfl⟩
  · exact (WP.spec_vis _ _ |>.mp hc).elim
  · exact (WP.spec_div.mp hc).elim

unseal Result in
/-- A mixed-width mutable borrow updates exactly the first and last u16 words,
    restores their two-byte-aligned representation, and preserves every frame. -/
theorem update_word_bytes_raw.spec (p : MutRawPtr Words) (base : BasePtr)
    (words : Words) (first last : U16) :
    ⦃ pointsTo wordsRepr p base words ⦄
    update_word_bytes_raw p first last
    ⦃ _ => pointsTo wordsRepr p base (updatedWords words first last) ⦄ := by
  intro h F s₀ hp hd hm hi
  have aligned : 2 ∣ p.address.val := by
    obtain ⟨_, _, _, aligned, _⟩ := hp
    exact aligned
  let initial := wordBytes (wordVector words)
  let updated := updatedBytes initial first last
  have hpBytes := words_to_bytes p base words h hp
  have noPointers : ∀ i : Fin 16, ∀ q, ¬ Aeneas.Std.Repr.u8.Carries updated[i.val] q := by
    intro i q
    exact Aeneas.Std.Repr.u8_noPointers _ q
  have fits : initial.toList.length ≤ Usize.max := by scalar_tac
  unfold update_word_bytes_raw core.slice.raw.from_raw_parts_mut RawPtr.borrowSlice
  simp only [bind_tc_eq, bind_ok, Aeneas.Std.bind_assoc]
  have count_eq : (16#usize).val = 16 := by simp
  rw [count_eq]
  apply HeapWP.Spec.bind (HeapWP.borrowRange_return.spec Aeneas.Std.Repr.u8
    (p.cast U8) base initial updated noPointers (by decide) (by decide) h F s₀ hpBytes hd hm hi)
  rintro bytes s₁ ⟨he, returns⟩
  rw [he]
  simp only [dite_eq_left fits, bind_ok]
  apply HeapWP.Spec.bind
    (pure_spec_heap (updateByteEnds.spec _ initial first last (by simp)) s₁)
  rintro result s₂ ⟨hr, rfl⟩
  have hlen : result.length = (16#usize).val := by
    change result.val.length = (16#usize).val
    rw [hr]
    simp
  unfold core.slice.raw.from_raw_parts_mut.back
  rw [ite_eq_left hlen, hr]
  apply HeapWP.Spec.mono returns
  rintro _ s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
  have restored := bytes_to_words p base updated h₂ aligned hp₂
  have he : ofWordVector (decodeWords updated) = updatedWords words first last := by
    simp [updated, initial, updatedWords, decodeWords_updatedBytes, decodeWords_wordBytes]
  exact ⟨h₂, hd₂, hm₂, hi₂, he ▸ restored⟩

/- Manual reconstruction of the outer mutable-array exposure. The emitted
   `as_mut_ptr` returns a stale slice rather than a matching backward computation. -/
def update_word_bytes (words : Words) (first last : U16) : Result Words := do
  let (p, back) ← core.ptr.from_mut wordsRepr words
  update_word_bytes_raw p first last
  back

unseal Result in
theorem update_word_bytes_tail.spec (p : RawPtr Words) (words : Words) (first last : U16) :
    ⦃ alloc wordsRepr p p.address 1 false ∗ pointsTo wordsRepr p p.address words ⦄
    (do update_word_bytes_raw p first last
        core.ptr.end_from_mut wordsRepr p)
    ⦃ (result : Words) => fun h => result = updatedWords words first last ∧ emp h ⦄ := by
  intro h F s₀ hp hd hm hi
  have kernel := HeapWP.frame (R := alloc wordsRepr p p.address 1 false)
    (update_word_bytes_raw.spec p p.address words first last)
  apply HeapWP.Spec.bind (kernel h F s₀ ((sep_comm _ _ _).mp hp) hd hm hi)
  rintro _ s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  have restored := (sep_comm _ _ _).mp
    (sep_mono (fun _ => pointsTo_readable) (fun _ hp => hp) hp₁)
  exact HeapWP.end_from_mut.spec wordsRepr p p.address
    (updatedWords words first last) (by decide) h₁ F s₁ restored hd₁ hm₁ hi₁

unseal Result in
/-- **Spec theorem for `raw_memory_views::update_word_bytes`**
    The safe array returns with precisely its first and last words replaced.
    Both backward computations execute, and the external heap frame is preserved. -/
theorem update_word_bytes.spec (words : Words) (first last : U16) (s₀ : Heap) (F : Fragment)
    (hi : s₀.Inv) (hm : Fragment.Matches s₀ F)
    (feasible : ∃ p s₁, State.newBlock wordsRepr [words] false s₀ p s₁) :
    HeapWP.Spec (update_word_bytes words first last)
      (fun result s₁ => result = updatedWords words first last ∧
        Fragment.Matches s₁ F ∧ s₁.Inv) s₀ := by
  simp only [update_word_bytes, core.ptr.from_mut, Aeneas.Std.bind_assoc, bind_ok]
  apply HeapWP.Spec.bind (HeapWP.allocExposure_encoded.spec wordsRepr words
    (wordsRepr_calibrated words) s₀ F hi hm feasible)
  rintro p s₁ ⟨_, h, hd, hm₁, hi₁, hp⟩
  apply HeapWP.Spec.mono (update_word_bytes_tail.spec p words first last h F s₁ hp hd hm₁ hi₁)
  rintro result s₂ ⟨h₂, _, hm₂, hi₂, hr, rfl⟩
  exact ⟨hr, by simpa using hm₂, hi₂⟩

end raw_memory_views
