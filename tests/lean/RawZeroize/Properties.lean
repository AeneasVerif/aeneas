module

public import RawZeroize.Funs
public import RawMemoryViews.ByteStorage
public import Aeneas.Std.RangeIter
import all RawBoxProofs
import all Aeneas.Std.Primitives
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic raw_memory_views
open scoped Aeneas.Std.HeapWP

namespace raw_zeroize

set_option maxHeartbeats 1000000

/-- The emitted Range loop initializes each byte to zero without reading it. -/
theorem zeroize_loop.spec (iter : core.ops.range.Range Usize) (bytes : RawPtr U8)
    (base : BasePtr) (initial : Vector Aeneas.Std.Byte iter.end.val)
    (bound : iter.start.val ≤ iter.end.val)
    (fits : ∀ j, j < iter.end.val → bytes.address.val + j < 2 ^ UScalarTy.numBits .Usize) :
    ⦃ writableBytes bytes base initial ⦄ zeroize_loop iter bytes
    ⦃ _ => writableBytes bytes base (filledFrom initial 0#u8 iter.start.val) ⦄ := by
  intro h F s hp hd hm hi
  unfold zeroize_loop
  by_cases more : iter.start.val < iter.end.val
  · apply HeapWP.Spec.bind
      (HeapWP.Spec.of_spec (core.iter.range.IteratorRange.next_Usize_some_spec iter more) s)
    rintro ⟨o, iter₁⟩ s₁ ⟨⟨ho, hstart, hend⟩, same⟩
    subst o
    subst s₁
    apply HeapWP.Spec.bind
      (add_writable.spec bytes base initial iter.start (by agrind) (by agrind)
        (fits iter.start.val more) h F s hp hd hm hi)
    rintro p s₁ ⟨h₁, hd₁, hm₁, hi₁, prov, address, hp₁⟩
    apply HeapWP.Spec.bind
      (write_byte.spec bytes p base initial ⟨iter.start.val, more⟩ 0#u8 prov address
        h₁ F s₁ hp₁ hd₁ hm₁ hi₁)
    rintro _ s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
    have ih := zeroize_loop.spec iter₁ bytes base
      ((initial.set iter.start.val (.data 0#u8)).cast (congrArg UScalar.val hend).symm)
      (by agrind) (by simpa only [hend] using fits)
    apply HeapWP.Spec.mono (ih h₂ F s₂ hp₂ hd₂ hm₂ hi₂)
    rintro _ s₃ ⟨h₃, hd₃, hm₃, hi₃, hp₃⟩
    refine ⟨h₃, hd₃, hm₃, hi₃, ?_⟩
    rcases iter₁ with ⟨start, finish⟩
    dsimp at hend hstart hp₃
    subst finish
    simpa only [Vector.cast_rfl, hstart,
      filledFrom_step initial 0#u8 ⟨iter.start.val, more⟩] using hp₃
  · apply HeapWP.Spec.bind
      (HeapWP.Spec.of_spec (core.iter.range.IteratorRange.next_Usize_none_spec iter (by agrind)) s)
    rintro ⟨o, iter₁⟩ s₁ ⟨⟨ho, _⟩, same⟩
    subst o
    subst s₁
    have done : filledFrom initial 0#u8 iter.start.val = initial := by
      apply Vector.ext
      intro j hj
      have before : ¬ iter.start.val ≤ j := by agrind
      simp [filledFrom, before]
    exact (HeapWP.Spec.pure () _ s).mpr ⟨h, hd, hm, hi, by simpa only [done] using hp⟩
termination_by iter.end.val - iter.start.val
decreasing_by agrind

/- Keep the emitted checks intact, factoring them only for the proof. -/
def checkedSize (elementSize len : Usize) : Result Usize := do
  let o ← lift (Usize.checked_mul len elementSize)
  let size ← core.option.Option.expect o (toStr "overflow")
  let max ← lift (IScalar.hcast .Usize core.num.Isize.MAX)
  massert (size <= max)
  pure size

@[local simp, local scalar_tac_simps]
theorem max_isize_cast :
    (IScalar.hcast .Usize core.num.Isize.MAX).val = Isize.max.toNat := by
  simp_scalar
  rcases System.Platform.numBits_eq with bits | bits
  · simp [Isize.max, Isize.numBits, bits]
  · simp [Isize.max, Isize.numBits, bits]

private theorem isize_max_le_usize : Isize.max.toNat ≤ Usize.max := by
  rcases System.Platform.numBits_eq with bits | bits
  · simp [Isize.max, Isize.numBits, Usize.max, Usize.numBits, bits]
  · simp [Isize.max, Isize.numBits, Usize.max, Usize.numBits, bits]

attribute [local step] core.option.Option.expect.spec

@[local step]
theorem checkedSize.spec (elementSize len : Usize)
    (bound : len.val * elementSize.val ≤ Isize.max.toNat) :
    checkedSize elementSize len ⦃ (size : Usize) =>
      size.val = len.val * elementSize.val ⦄ := by
  unfold checkedSize
  have fits := isize_max_le_usize
  step as ⟨o, ho⟩
  have present : o.isSome := by
    cases o
    · exact False.elim ((Nat.not_lt_of_ge (bound.trans fits)) ho)
    · rfl
  step as ⟨size, sizeEq⟩
  have sizeVal : size.val = len.val * elementSize.val := by
    rw [sizeEq] at ho
    exact ho.2.1
  step*

theorem zeroize.fold (elementSize : Usize) (storage : UninitSlice T) :
    zeroize elementSize storage =
      (do
        let size ← checkedSize elementSize storage.len
        zeroize_loop ⟨0#usize, size⟩ (storage.ptr.cast U8)
        pure storage) := by
  simp only [zeroize, UninitSlice.as_mut_ptr, ptr_cast, size_of, checkedSize, bind_ok,
    Aeneas.Std.bind_assoc, pure]
  rfl

/-- **Spec theorem for `raw_zeroize::zeroize`**
    All bytes of all len elements, including padding and uninitialized bytes,
    become numerical zero. No old T or all-zero validity of T is required. -/
theorem zeroize.spec (elementSize : Usize) (storage : UninitSlice T)
    (base : BasePtr) (initial : Vector Aeneas.Std.Byte (storage.len.val * elementSize.val))
    (bound : storage.len.val * elementSize.val ≤ Isize.max.toNat) :
    ⦃ writableBytes (storage.ptr.cast U8) base initial ⦄ zeroize elementSize storage
    ⦃ (result : UninitSlice T) => fun h => result = storage ∧
      writableBytes (storage.ptr.cast U8) base
        (Vector.replicate (storage.len.val * elementSize.val) (.data 0#u8)) h ⦄ := by
  rw [zeroize.fold]
  intro h F s hp hd hm hi
  apply HeapWP.Spec.bind (HeapWP.Spec.of_spec (checkedSize.spec elementSize storage.len bound) s)
  rintro size s₁ ⟨sizeEq, same⟩
  subst s₁
  have fits := writableBytes_fits (storage.ptr.cast U8) base initial h s hp
    ((Fragment.matches_union _ _ _).mp hm).1 hi
  have loop := zeroize_loop.spec ⟨0#usize, size⟩ (storage.ptr.cast U8) base
    (initial.cast sizeEq.symm) (by simp) (by simpa only [sizeEq] using fits)
  apply HeapWP.Spec.bind (loop h F s hp hd hm hi)
  rintro _ s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
  apply (HeapWP.Spec.pure storage _ s₂).mpr
  refine ⟨h₂, hd₂, hm₂, hi₂, rfl, ?_⟩
  have zero : filledFrom (initial.cast sizeEq.symm) 0#u8 (0#usize).val =
      Vector.replicate size.val (.data 0#u8) := by
    apply Vector.ext
    intro j hj
    simp [filledFrom]
  simp only [zero] at hp₂
  simpa only [writableBytes, Vector.toList_map, Vector.toList_replicate, sizeEq] using hp₂

/-- Empty or zero-sized ranges make no heap accesses, even with an invalid
    pointer. This ordinary WP excludes all heap effects. -/
theorem zeroize.zero (elementSize : Usize) (storage : UninitSlice T)
    (empty : storage.len.val * elementSize.val = 0) :
    zeroize elementSize storage ⦃ (result : UninitSlice T) => result = storage ⦄ := by
  rw [zeroize.fold]
  apply WP.spec_bind (checkedSize.spec elementSize storage.len (by simp [empty]))
  intro size sizeEq
  have sizeZero : size = 0#usize := by scalar_tac
  subst size
  unfold zeroize_loop
  simp only [Aeneas.Std.bind_assoc]
  apply WP.spec_bind (core.iter.range.IteratorRange.next_Usize_none_spec
    ⟨0#usize, 0#usize⟩ (by simp))
  rintro ⟨o, iter⟩ ⟨rfl, _⟩
  simp [pure]

/-- The byte part of zeroize's postcondition determines every aligned,
    positive-sized, in-bounds read by the decoder alone. In particular,
    invalid all-zero representations give none, not a fabricated typed value. -/
theorem zeroize.post_read_eq (repr : Aeneas.Std.Repr V)
    (p : RawPtr U8) (q : RawPtr V) (base : BasePtr) (n offset : Nat)
    (s : Heap) (h : Fragment)
    (zeroed : writableBytes p base (Vector.replicate n (.data 0#u8)) h)
    (matching : Fragment.Matches s h)
    (positive : 0 < repr.size) (bounds : offset + repr.size ≤ n)
    (provenance : q.provenance = p.provenance)
    (address : q.address.val = p.address.val + offset)
    (aligned : repr.align.val ∣ q.address.val) :
    Heap.read repr q s = repr.decode (Vector.replicate repr.size (.data 0#u8)) := by
  obtain ⟨lower, _, cells⟩ := zeroed
  rw [cells] at matching
  simp only [Vector.map_replicate, Vector.toList_replicate] at matching
  have qlower : base.val ≤ q.address.val := by agrind
  have qoffset : q.offsetFrom base = p.offsetFrom base + offset := by
    simp only [RawPtr.offsetFrom]
    agrind
  have selected : Fragment.Matches s (cellsHeap base q.provenance (q.offsetFrom base)
      ((Vector.replicate repr.size (.data 0#u8)).map (Cell.shared 0)).toList) := by
    apply matches_cellsHeap.mpr
    intro i hi
    have small : i < repr.size := by simpa using hi
    have inside : offset + i < (List.replicate n (Cell.shared 0 (.data 0#u8))).length := by
      simp only [List.length_replicate]
      agrind
    obtain ⟨blk, found, live, baseEq, byte⟩ := matches_cellsHeap.mp matching (offset + i) inside
    refine ⟨blk, ?_, live, baseEq, ?_⟩
    · simpa only [provenance] using found
    · simpa [qoffset, Nat.add_assoc, small] using byte
  obtain ⟨blk, fit, found, live, baseEq, data⟩ :=
    bytes_of_matches (repr := repr) positive selected
  have readZero := Aeneas.Std.Repr.readBytes_shared
    (Vector.replicate repr.size (.data 0#u8)) 0
  simp only [Vector.map_replicate] at readZero
  simp [Heap.read, found, live, baseEq, qlower, aligned, Aeneas.Std.Repr.read,
    positive, fit, data, readZero]

/-- Two instances of zeroize's byte postcondition make corresponding reads
    equal, irrespective of the initial values, final allocation identities,
    or surrounding heaps. No all-zero validity hypothesis is required. -/
theorem zeroize.post_read_independent (repr : Aeneas.Std.Repr V)
    (p₁ p₂ : RawPtr U8) (q₁ q₂ : RawPtr V) (base₁ base₂ : BasePtr)
    (n₁ n₂ offset : Nat) (s₁ s₂ : Heap) (h₁ h₂ : Fragment)
    (post₁ : writableBytes p₁ base₁ (Vector.replicate n₁ (.data 0#u8)) h₁)
    (post₂ : writableBytes p₂ base₂ (Vector.replicate n₂ (.data 0#u8)) h₂)
    (match₁ : Fragment.Matches s₁ h₁) (match₂ : Fragment.Matches s₂ h₂)
    (positive : 0 < repr.size)
    (bounds₁ : offset + repr.size ≤ n₁) (bounds₂ : offset + repr.size ≤ n₂)
    (prov₁ : q₁.provenance = p₁.provenance) (prov₂ : q₂.provenance = p₂.provenance)
    (addr₁ : q₁.address.val = p₁.address.val + offset)
    (addr₂ : q₂.address.val = p₂.address.val + offset)
    (align₁ : repr.align.val ∣ q₁.address.val) (align₂ : repr.align.val ∣ q₂.address.val) :
    Heap.read repr q₁ s₁ = Heap.read repr q₂ s₂ := by
  rw [zeroize.post_read_eq repr p₁ q₁ base₁ n₁ offset s₁ h₁ post₁ match₁
    positive bounds₁ prov₁ addr₁ align₁]
  rw [zeroize.post_read_eq repr p₂ q₂ base₂ n₂ offset s₂ h₂ post₂ match₂
    positive bounds₂ prov₂ addr₂ align₂]

/-- Typed restoration requires a witness that the final all-zero bytes encode
    this value. It is not a claim about arbitrary T or T::default(). -/
theorem zeroize.restore_spec (repr : Aeneas.Std.Repr T) (elementSize : Usize)
    (storage : UninitSlice T) (base : BasePtr)
    (size : storage.len.val * elementSize.val = repr.size)
    (bound : repr.size ≤ Isize.max.toNat) (initial : Vector Aeneas.Std.Byte repr.size)
    (zero : T) (allZero : repr.encode zero (Vector.replicate repr.size (.data 0#u8))) :
    ⦃ block repr storage.ptr base (initial.map (Cell.shared 0)).toList ⦄
    zeroize elementSize storage
    ⦃ (result : UninitSlice T) => fun h => result = storage ∧
      pointsTo repr storage.ptr base zero 0 h ⦄ := by
  intro h F s hp hd hm hi
  have writable : writableBytes (storage.ptr.cast U8) base (initial.cast size.symm) h := by
    refine ⟨hp.1, by simp [Aeneas.Std.Repr.u8], ?_⟩
    exact hp.2.2
  apply HeapWP.Spec.mono (zeroize.spec elementSize storage base
    (initial.cast size.symm) (by simpa only [size] using bound) h F s writable hd hm hi)
  rintro result s₁ ⟨h₁, hd₁, hm₁, hi₁, same, _, _, cells⟩
  refine ⟨h₁, hd₁, hm₁, hi₁, same, Vector.replicate repr.size (.data 0#u8), allZero,
    hp.1, hp.2.1, ?_⟩
  simpa only [Vector.toList_map, Vector.toList_replicate, size,
    RawPtr.cast, RawPtr.offsetFrom] using cells

theorem u32_zero_encoding :
    raw_box.u32Repr.encode 0#u32 (Vector.replicate raw_box.u32Repr.size (.data 0#u8)) := by
  change Vector.replicate 4 (Aeneas.Std.Byte.data 0#u8) =
    (raw_box.u32Bytes 0#u32).map Aeneas.Std.Byte.data
  unfold raw_box.u32Bytes
  apply Vector.toList_inj.mp
  rw [Vector.toList_map]
  simp
  bv_tac 8

private theorem zeroize_word_tail.spec (ptr : RawPtr U32) (word : U32) :
    ⦃ alloc raw_box.u32Repr ptr ptr.address 1 false ∗
      readable raw_box.u32Repr ptr ptr.address word ⦄
    (do
      let _ ← zeroize 4#usize ⟨ptr, 1#usize⟩
      let _ ← Result.ok ()
      core.ptr.end_from_mut raw_box.u32Repr ptr)
    ⦃ (result : U32) => fun h => result = 0#u32 ∧ empty h ⦄ := by
  have bound : raw_box.u32Repr.size ≤ Isize.max.toNat := by
    change 4 ≤ Isize.max.toNat
    rcases System.Platform.numBits_eq with bits | bits
    · simp [Isize.max, Isize.numBits, bits]
    · simp [Isize.max, Isize.numBits, bits]
  have wiping : ⦃ readable raw_box.u32Repr ptr ptr.address word ⦄
      zeroize 4#usize ⟨ptr, 1#usize⟩ ⦃ _ => pointsTo raw_box.u32Repr ptr ptr.address 0#u32 ⦄ := by
    rintro h F s ⟨initial, _, cells⟩ hd hm hi
    apply HeapWP.Spec.mono (zeroize.restore_spec raw_box.u32Repr 4#usize ⟨ptr, 1#usize⟩ ptr.address
      (by change 1 * 4 = 4; decide) bound initial 0#u32 u32_zero_encoding h F s cells hd hm hi)
    rintro _ s₁ ⟨h₁, hd₁, hm₁, hi₁, _, point⟩
    exact ⟨h₁, hd₁, hm₁, hi₁, point⟩
  intro h F s hp hd hm hi
  apply HeapWP.Spec.bind (HeapWP.frame (R := alloc raw_box.u32Repr ptr ptr.address 1 false)
    wiping h F s ((sep_comm _ _ _).mp hp) hd hm hi)
  rintro _ s₁ ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩
  rw [bind_ok]
  have readable := sep_mono (fun _ => pointsTo_readable) (fun _ x => x) hp₁
  exact HeapWP.end_from_mut.spec raw_box.u32Repr ptr ptr.address 0#u32 (by decide)
    h₁ F s₁ ((sep_comm _ _ _).mp readable) hd₁ hm₁ hi₁

/-- **Spec theorem for `raw_zeroize::zeroize_word`**
    The safe value returns as zero, the temporary exposure is retired, and
    arbitrary external frames are preserved. OOM is an accepted abort. -/
theorem zeroize_word.spec (word : U32) (s₀ : Heap) (F : Fragment)
    (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    HeapWP.Spec (zeroize_word word)
      (fun result s₁ => result = 0#u32 ∧ Fragment.Matches s₁ F ∧ s₁.Inv) s₀ := by
  simp only [zeroize_word, core.ptr.from_mut, ptr_cast, UninitSlice.from_raw_parts_mut,
    Aeneas.Std.bind_assoc, bind_ok, RawPtr.cast]
  apply HeapWP.Spec.bind (HeapWP.allocExposure.spec raw_box.u32Repr word s₀ F hi hm)
  rintro ptr s₁ ⟨_, h₁, hd₁, hm₁, hi₁, hp₁⟩
  change HeapWP.Spec
    (do
      let _ ← zeroize 4#usize ⟨ptr, 1#usize⟩
      let _ ← Result.ok ()
      core.ptr.end_from_mut raw_box.u32Repr ptr) _ s₁
  apply HeapWP.Spec.mono (zeroize_word_tail.spec ptr word h₁ F s₁ hp₁ hd₁ hm₁ hi₁)
  rintro result s₂ ⟨empty, _, frame, inv, resultEq, rfl⟩
  exact ⟨resultEq, by simpa using frame, inv⟩

end raw_zeroize
