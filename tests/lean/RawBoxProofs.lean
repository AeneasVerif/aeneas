module

public import RawBox
public import Aeneas.Std.Heap.EffectSpecs

public section

open Aeneas.Std
open Aeneas.Std.SepLogic

namespace raw_box

theorem u32Bytes_roundtrip (bits : BitVec 32) :
    bits.extractLsb' 24 8 ++ bits.extractLsb' 16 8 ++
      bits.extractLsb' 8 8 ++ bits.extractLsb' 0 8 = bits := by
  bv_decide

def u32Bytes (value : U32) : Vector U8 4 :=
  #v[⟨value.bv.extractLsb' 0 8⟩, ⟨value.bv.extractLsb' 8 8⟩,
    ⟨value.bv.extractLsb' 16 8⟩, ⟨value.bv.extractLsb' 24 8⟩]

private theorem dataBytes_numeric (values : Vector U8 n) :
    (values.map Aeneas.Std.Byte.data).mapM Aeneas.Std.Byte.numeric = some values := by
  rw [Vector.mapM_map]
  change values.mapM (fun x => pure (id x)) = some values
  rw [Vector.mapM_pure]
  simp

private theorem numericBytes_eq {n : Nat} (bytes bytes' : Vector Aeneas.Std.Byte n)
    (values : Vector U8 n) (decoded : bytes.mapM Aeneas.Std.Byte.numeric = some values)
    (agree : ∀ i : Fin n, bytes[i.val] ≠ .uninit → bytes'[i.val] = bytes[i.val]) :
    bytes' = bytes := by
  apply Vector.ext
  intro i hi
  apply agree ⟨i, hi⟩
  obtain ⟨value, hv⟩ := vector_mapM_enabled decoded i hi
  intro he
  simp [he, Aeneas.Std.Byte.numeric] at hv

/-- Little-endian, four-byte `u32` descriptor; no global representation lookup. -/
@[expose] def u32Repr : Aeneas.Std.Repr U32 where
  size := 4
  align := ⟨4, 2, rfl⟩
  decode bytes := do
    let bytes ← bytes.mapM Aeneas.Std.Byte.numeric
    pure ⟨bytes[3].bv ++ bytes[2].bv ++ bytes[1].bv ++ bytes[0].bv⟩
  encode value bytes := bytes = (u32Bytes value).map Aeneas.Std.Byte.data
  aligned := by decide
  encode_complete value := ⟨(u32Bytes value).map Aeneas.Std.Byte.data, rfl⟩
  encode_decode value bytes encoded := by
    subst bytes
    rw [dataBytes_numeric]
    change some ⟨value.bv.extractLsb' 24 8 ++ value.bv.extractLsb' 16 8 ++
      value.bv.extractLsb' 8 8 ++ value.bv.extractLsb' 0 8⟩ = some value
    apply congrArg some
    cases value
    rename_i bits
    apply congrArg UScalar.mk
    change bits.extractLsb' 24 8 ++ bits.extractLsb' 16 8 ++
      bits.extractLsb' 8 8 ++ bits.extractLsb' 0 8 = bits
    exact u32Bytes_roundtrip bits
  decode_mono bytes bytes' value decoded agree := by
    cases hn : bytes.mapM Aeneas.Std.Byte.numeric
    · simp [hn] at decoded
    · rename_i values
      have same := numericBytes_eq bytes bytes' values hn agree
      simpa only [same] using decoded
  encode_valid value bytes i encoded := by
    subst bytes
    simp

@[simp] theorem u32Repr_noPointers (value : U32) (p : RawPtr Unit) :
    ¬ u32Repr.Carries value p := by
  rintro ⟨bytes, encoded, i, lane, hp⟩
  change bytes = (u32Bytes value).map Aeneas.Std.Byte.data at encoded
  subst bytes
  have impossible := (Vector.getElem_map Aeneas.Std.Byte.data
    (xs := u32Bytes value) i.isLt).symm.trans hp
  cases impossible

/-- Two consecutive little-endian `u32`s, with four-byte alignment. -/
def pairRepr : Aeneas.Std.Repr (U32 × U32) where
  size := 8
  align := ⟨4, 2, rfl⟩
  decode bytes := do
    let bytes ← bytes.mapM Aeneas.Std.Byte.numeric
    pure (⟨bytes[3].bv ++ bytes[2].bv ++ bytes[1].bv ++ bytes[0].bv⟩,
      ⟨bytes[7].bv ++ bytes[6].bv ++ bytes[5].bv ++ bytes[4].bv⟩)
  encode value bytes :=
    bytes = (u32Bytes value.1 ++ u32Bytes value.2).map Aeneas.Std.Byte.data
  aligned := by decide
  encode_complete value :=
    ⟨(u32Bytes value.1 ++ u32Bytes value.2).map Aeneas.Std.Byte.data, rfl⟩
  encode_decode value bytes encoded := by
    subst bytes
    rw [dataBytes_numeric]
    rcases value with ⟨⟨first⟩, ⟨second⟩⟩
    change some ((⟨first.extractLsb' 24 8 ++ first.extractLsb' 16 8 ++
      first.extractLsb' 8 8 ++ first.extractLsb' 0 8⟩,
      ⟨second.extractLsb' 24 8 ++ second.extractLsb' 16 8 ++
      second.extractLsb' 8 8 ++ second.extractLsb' 0 8⟩) : U32 × U32) =
        some (⟨first⟩, ⟨second⟩)
    apply congrArg some
    apply Prod.ext
    · apply congrArg UScalar.mk
      exact u32Bytes_roundtrip first
    · apply congrArg UScalar.mk
      exact u32Bytes_roundtrip second
  decode_mono bytes bytes' value decoded agree := by
    cases hn : bytes.mapM Aeneas.Std.Byte.numeric
    · simp [hn] at decoded
    · rename_i values
      have same := numericBytes_eq bytes bytes' values hn agree
      simpa only [same] using decoded
  encode_valid value bytes i encoded := by
    subst bytes
    simp

@[simp] theorem pairRepr_noPointers (value : U32 × U32) (p : RawPtr Unit) :
    ¬ pairRepr.Carries value p := by
  rintro ⟨bytes, encoded, i, lane, hp⟩
  change bytes =
    (u32Bytes value.1 ++ u32Bytes value.2).map Aeneas.Std.Byte.data at encoded
  subst bytes
  have impossible := (Vector.getElem_map Aeneas.Std.Byte.data
    (xs := u32Bytes value.1 ++ u32Bytes value.2) i.isLt).symm.trans hp
  cases impossible

theorem round_trip_tail.spec (repr : Aeneas.Std.Repr U32) (p : MutRawPtr U32)
    (initial replacement : U32) (hsize : 0 < repr.size) :
    HeapWP.Triple (sep (alloc repr p 1 true) (pointsTo repr p initial))
      (do MutRawPtr.write repr p replacement
          let value ← RawPtr.read repr p
          let _ ← alloc.boxed.Box.from_raw repr p
          pure value)
      (fun value h => value = replacement ∧ emp h) := by
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h) (HeapWP.frame (R := alloc repr p 1 true)
      (HeapWP.write.spec repr p initial replacement hsize)))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun _ h => h)
    (fun value h hp => (sep_and_left (value = replacement)
      (pointsTo repr p replacement) (alloc repr p 1 true) h).mp hp)
    (HeapWP.frame (R := alloc repr p 1 true) (HeapWP.read.spec repr p replacement 0 hsize)))
  intro value
  apply HeapWP.Triple.pure_pre
  intro hv
  subst value
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ hp => hp.2) (HeapWP.fromRaw.spec repr p replacement hsize))
  intro _
  exact HeapWP.Triple.pure emp replacement

/-- The actual lifecycle consumes its allocation and preserves any matching frame.
The capacity hypothesis is necessary because base identifiers are bounded. -/
theorem round_trip.spec (repr : Aeneas.Std.Repr U32) (initial replacement : U32)
    (hsize : 0 < repr.size) (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (round_trip repr initial replacement)
      (fun value s' => value = replacement ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold round_trip
  apply HeapWP.Spec.bind (HeapWP.intoRaw.spec repr initial s F hi hm hc hfit)
  rintro p s' ⟨_, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono (round_trip_tail.spec repr p initial replacement hsize h F s' hp hd hm' hi')
  rintro value s'' ⟨h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

theorem stored_pointer_tail.spec (repr : Aeneas.Std.Repr U32)
    (pointerRepr : Aeneas.Std.Repr (MutRawPtr U32)) (target : MutRawPtr U32)
    (slot : MutRawPtr (MutRawPtr U32))
    (initial replacement : U32) (hsize : 0 < repr.size) (hptr : 0 < pointerRepr.size) :
    HeapWP.Triple
      (sep (sep (alloc pointerRepr slot 1 true) (pointsTo pointerRepr slot target))
        (sep (alloc repr target 1 true) (pointsTo repr target initial)))
      (do let loaded ← RawPtr.read pointerRepr slot
          MutRawPtr.write repr loaded replacement
          let _ ← alloc.boxed.Box.from_raw pointerRepr slot
          alloc.boxed.Box.from_raw repr target)
      (fun value h => value = replacement ∧ emp h) := by
  let targetOwn := sep (alloc repr target 1 true) (pointsTo repr target initial)
  let slotOwn := sep (alloc pointerRepr slot 1 true) (pointsTo pointerRepr slot target)
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun _ h => h)
    (fun loaded h hp => (sep_and_left (loaded = target) slotOwn targetOwn h).mp hp)
    (HeapWP.frame (R := targetOwn)
      (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
        (fun loaded h hp => (sep_and_left (loaded = target)
          (pointsTo pointerRepr slot target) (alloc pointerRepr slot 1 true) h).mp hp |>.imp_right
            ((sep_comm _ _ h).mp))
        (HeapWP.frame (R := alloc pointerRepr slot 1 true)
          (HeapWP.read.spec pointerRepr slot target 0 hptr)))))
  intro loaded
  apply HeapWP.Triple.pure_pre
  intro he
  subst loaded
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ h => h)
    (HeapWP.frame (R := slotOwn)
      (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
        (fun _ _ h => (sep_comm _ _ _).mp h)
        (HeapWP.frame (R := alloc repr target 1 true)
          (HeapWP.write.spec repr target initial replacement hsize)))))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => (sep_emp_left
      (sep (alloc repr target 1 true) (pointsTo repr target replacement)) h).mp
        (sep_mono (fun _ hp => hp.2) (fun _ h => h) hp))
    (HeapWP.frame (R := sep (alloc repr target 1 true) (pointsTo repr target replacement))
      (HeapWP.fromRaw.spec pointerRepr slot target hptr)))
  intro _
  exact HeapWP.fromRaw.spec repr target replacement hsize

/-- A pointer is encoded in the second allocation using its own explicit
representation, not assumed to fit in one machine word. -/
theorem stored_pointer.spec (repr : Aeneas.Std.Repr U32)
    (pointerRepr : Aeneas.Std.Repr (MutRawPtr U32)) (initial replacement : U32)
    (hsize : 0 < repr.size) (hptr : 0 < pointerRepr.size)
    (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (hptrfit : pointerRepr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 2 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (stored_pointer repr pointerRepr initial replacement)
      (fun value s' => value = replacement ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold stored_pointer
  have hc' : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize := by agrind
  apply HeapWP.Spec.bind (HeapWP.intoRaw.spec repr initial s F hi hm hc' hfit)
  rintro target s₁ ⟨hn, a, haF, hm₁, hi₁, hp⟩
  have hc₁ : s₁.next.val + 1 < 2 ^ UScalarTy.numBits .Usize := by agrind
  apply HeapWP.Spec.bind (HeapWP.intoRaw.spec pointerRepr target s₁ (a ∪ F) hi₁ hm₁ hc₁ hptrfit)
  rintro slot s₂ ⟨_, b, hd, hm₂, hi₂, hq⟩
  obtain ⟨hba, hbF⟩ := Fragment.disjoint_union_right.mp hd
  have hown : sep (sep (alloc pointerRepr slot 1 true) (pointsTo pointerRepr slot target))
      (sep (alloc repr target 1 true) (pointsTo repr target initial)) (b ∪ a) :=
    ⟨b, a, hba, rfl, hq, hp⟩
  have hd' := Fragment.disjoint_union_left.mpr ⟨hbF, haF⟩
  have hm' : Fragment.Matches s₂ (b ∪ a ∪ F) := by
    simpa [Fragment.union_assoc] using hm₂
  apply HeapWP.Spec.mono
    (stored_pointer_tail.spec repr pointerRepr target slot initial replacement hsize hptr
      (b ∪ a) F s₂ hown hd' hm' hi₂)
  rintro value s' ⟨h', _, hm', hi', hv, rfl⟩
  exact ⟨hv, by simpa using hm', hi'⟩

theorem replace_pair_tail.spec (repr : Aeneas.Std.Repr (U32 × U32))
    (p : MutRawPtr (U32 × U32)) (first second replacement : U32)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (sep (alloc repr p 1 true) (pointsTo repr p (first, second)))
      (do let (i, _) ← RawPtr.read repr p
          MutRawPtr.write repr p (i, replacement)
          alloc.boxed.Box.from_raw repr p)
      (fun value h => value = (first, replacement) ∧ emp h) := by
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp)
    (fun value h hp => (sep_and_left (value = (first, second))
      (pointsTo repr p (first, second)) (alloc repr p 1 true) h).mp hp)
    (HeapWP.frame (R := alloc repr p 1 true)
      (HeapWP.read.spec repr p (first, second) 0 hsize)))
  intro value
  apply HeapWP.Triple.pure_pre
  intro hv
  subst value
  apply HeapWP.Triple.bind (HeapWP.frame (R := alloc repr p 1 true)
    (HeapWP.write.spec repr p (first, second) (first, replacement) hsize))
  intro _
  exact HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ hp => hp) (HeapWP.fromRaw.spec repr p (first, replacement) hsize)

/-- Pair replacement preserves the first component and consumes the allocation. -/
theorem replace_pair.spec (repr : Aeneas.Std.Repr (U32 × U32))
    (first second replacement : U32) (hsize : 0 < repr.size)
    (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (replace_pair repr first second replacement)
      (fun value s' => value = (first, replacement) ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold replace_pair
  apply HeapWP.Spec.bind (HeapWP.intoRaw.spec repr (first, second) s F hi hm hc hfit)
  rintro p s' ⟨_, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono
    (replace_pair_tail.spec repr p first second replacement hsize h F s' hp hd hm' hi')
  rintro value s'' ⟨h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

theorem one_past_end_tail.spec (repr : Aeneas.Std.Repr U32)
    (p : MutRawPtr U32) (value : U32) (hsize : 0 < repr.size)
    (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (hzero : p.byteOffset.val = 0) :
    HeapWP.Triple (sep (alloc repr p 1 true) (pointsTo repr p value))
      (do let start ← RawPtr.add repr p 0#usize
          let _ ← RawPtr.add repr p 1#usize
          let result ← RawPtr.read repr start
          let _ ← alloc.boxed.Box.from_raw repr p
          pure result)
      (fun result h => result = value ∧ emp h) := by
  have hp : (⟨p.provenance, ⟨0⟩⟩ : RawPtr U32) = p := by
    rcases p with ⟨base, index⟩
    have he : (⟨0⟩ : Usize) = index := UScalar.eq_of_val_eq hzero.symm
    exact congrArg (RawPtr.mk base) he
  have hstart : p.byteOffset.val ≤ 1 * repr.size := by simp [hzero]
  have hbound0 : p.byteOffset.val + (0#usize).val * repr.size ≤ 1 * repr.size := by simp [hzero]
  have hbound1 : p.byteOffset.val + (1#usize).val * repr.size ≤ 1 * repr.size := by simp [hzero]
  have hfit0 : p.byteOffset.val + (0#usize).val * repr.size < 2 ^ UScalarTy.numBits .Usize := by
    simp [hzero]
  have hfit1 : p.byteOffset.val + (1#usize).val * repr.size < 2 ^ UScalarTy.numBits .Usize := by
    simpa [hzero] using hfit
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun _ h => h)
    (fun start h hs => (sep_and_left (start.provenance = p.provenance)
      (fun h => start.byteOffset.val = p.byteOffset.val + (0#usize).val * repr.size ∧ alloc repr p 1 true h)
      (pointsTo repr p value) h).mp hs |>.imp_right
        (fun hs => (sep_and_left (start.byteOffset.val = p.byteOffset.val + (0#usize).val * repr.size)
          (alloc repr p 1 true) (pointsTo repr p value) h).mp hs))
    (HeapWP.frame (R := pointsTo repr p value)
      (by simpa only [hp] using
        HeapWP.add.spec repr p 0#usize 1 true hsize hstart hbound0 hfit0)))
  intro start
  apply HeapWP.Triple.pure_pre
  intro hb
  apply HeapWP.Triple.pure_pre
  intro hi
  have he : start = p := by
    rcases start with ⟨base, index⟩
    rcases p with ⟨pbase, pindex⟩
    have hi' : index.val = pindex.val := by simpa using hi
    have he := UScalar.eq_of_val_eq hi'
    cases hb
    cases he
    rfl
  subst start
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun _ h => h)
    (fun q h hs => sep_mono
      (fun a (hp : q.provenance = p.provenance ∧ q.byteOffset.val = p.byteOffset.val + (1#usize).val * repr.size ∧
        alloc repr p 1 true a) => hp.2.2) (fun _ hp => hp) hs)
    (HeapWP.frame (R := pointsTo repr p value)
      (by simpa only [hp] using
        HeapWP.add.spec repr p 1#usize 1 true hsize hstart hbound1 hfit1)))
  intro _
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp)
    (fun result h hs => (sep_and_left (result = value)
      (pointsTo repr p value) (alloc repr p 1 true) h).mp hs)
    (HeapWP.frame (R := alloc repr p 1 true) (HeapWP.read.spec repr p value 0 hsize)))
  intro result
  apply HeapWP.Triple.pure_pre
  intro hr
  subst result
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp) (fun _ _ hp => hp.2)
    (HeapWP.fromRaw.spec repr p value hsize))
  intro _
  exact HeapWP.Triple.pure emp value

/-- Forming a one-past pointer does not authorize dereferencing it. The example
reads the original start pointer and then consumes the allocation. -/
theorem one_past_end.spec (repr : Aeneas.Std.Repr U32) (value : U32)
    (hsize : 0 < repr.size) (hfit : repr.size < 2 ^ UScalarTy.numBits .Usize)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (one_past_end repr value)
      (fun result s' => result = value ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold one_past_end
  apply HeapWP.Spec.bind (HeapWP.intoRaw.spec repr value s F hi hm hc hfit)
  rintro p s' ⟨_, h, hd, hm', hi', hp⟩
  have hz : p.byteOffset.val = 0 := by
    obtain ⟨a, b, _, _, ha, _⟩ := hp
    exact ha.1
  apply HeapWP.Spec.mono
    (one_past_end_tail.spec repr p value hsize hfit hz h F s' hp hd hm' hi')
  rintro result s'' ⟨h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

/-- Concrete byte semantics, with no representation hypothesis left to the caller. -/
theorem round_trip_u32.spec (initial replacement : U32)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (round_trip u32Repr initial replacement)
      (fun value s' => value = replacement ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  have hfit : u32Repr.size < 2 ^ UScalarTy.numBits .Usize := by
    change 4 < 2 ^ UScalarTy.numBits .Usize
    scalar_tac
  exact round_trip.spec u32Repr initial replacement (by decide) hfit s F hi hm hc

theorem replace_pair_u32.spec (first second replacement : U32)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (replace_pair pairRepr first second replacement)
      (fun value s' => value = (first, replacement) ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  have hfit : pairRepr.size < 2 ^ UScalarTy.numBits .Usize := by
    change 8 < 2 ^ UScalarTy.numBits .Usize
    scalar_tac
  exact replace_pair.spec pairRepr first second replacement (by decide) hfit s F hi hm hc

theorem one_past_end_u32.spec (value : U32)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (one_past_end u32Repr value)
      (fun result s' => result = value ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  have hfit : u32Repr.size < 2 ^ UScalarTy.numBits .Usize := by
    change 4 < 2 ^ UScalarTy.numBits .Usize
    scalar_tac
  exact one_past_end.spec u32Repr value (by decide) hfit s F hi hm hc

end raw_box

/-- info: 'raw_box.round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box.round_trip.spec

/-- info: 'raw_box.stored_pointer.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box.stored_pointer.spec

/-- info: 'raw_box.u32Repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box.u32Repr

/-- info: 'raw_box.pairRepr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box.pairRepr

/-- info: 'raw_box.replace_pair_u32.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box.replace_pair_u32.spec

/-- info: 'raw_box.one_past_end_u32.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_box.one_past_end_u32.spec

/-- info: 'Aeneas.Std.HeapWP.choose.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aeneas.Std.HeapWP.choose.spec
