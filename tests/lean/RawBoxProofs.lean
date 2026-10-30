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

/-- Little-endian, four-byte `u32` descriptor; no global representation lookup. -/
def u32Repr : Aeneas.Std.Repr U32 where
  size := 4
  align := ⟨4, 2, rfl⟩
  decode bytes := some ⟨bytes[3].bv ++ bytes[2].bv ++ bytes[1].bv ++ bytes[0].bv⟩
  aligned := by decide
  complete value := by
    refine ⟨#v[⟨value.bv.extractLsb' 0 8⟩, ⟨value.bv.extractLsb' 8 8⟩,
      ⟨value.bv.extractLsb' 16 8⟩, ⟨value.bv.extractLsb' 24 8⟩], ?_⟩
    apply congrArg some
    cases value
    rename_i bits
    apply congrArg UScalar.mk
    change bits.extractLsb' 24 8 ++ bits.extractLsb' 16 8 ++
      bits.extractLsb' 8 8 ++ bits.extractLsb' 0 8 = bits
    exact u32Bytes_roundtrip bits

/-- Two consecutive little-endian `u32`s, with four-byte alignment. -/
def pairRepr : Aeneas.Std.Repr (U32 × U32) where
  size := 8
  align := ⟨4, 2, rfl⟩
  decode bytes := some
    (⟨bytes[3].bv ++ bytes[2].bv ++ bytes[1].bv ++ bytes[0].bv⟩,
     ⟨bytes[7].bv ++ bytes[6].bv ++ bytes[5].bv ++ bytes[4].bv⟩)
  aligned := by decide
  complete value := by
    rcases value with ⟨⟨first⟩, ⟨second⟩⟩
    refine ⟨#v[⟨first.extractLsb' 0 8⟩, ⟨first.extractLsb' 8 8⟩,
      ⟨first.extractLsb' 16 8⟩, ⟨first.extractLsb' 24 8⟩,
      ⟨second.extractLsb' 0 8⟩, ⟨second.extractLsb' 8 8⟩,
      ⟨second.extractLsb' 16 8⟩, ⟨second.extractLsb' 24 8⟩], ?_⟩
    apply congrArg some
    apply Prod.ext
    · apply congrArg UScalar.mk
      exact u32Bytes_roundtrip first
    · apply congrArg UScalar.mk
      exact u32Bytes_roundtrip second

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
    (hzero : p.index.val = 0) :
    HeapWP.Triple (sep (alloc repr p 1 true) (pointsTo repr p value))
      (do let start ← RawPtr.add repr p 0#usize
          let _ ← RawPtr.add repr p 1#usize
          let result ← RawPtr.read repr start
          let _ ← alloc.boxed.Box.from_raw repr p
          pure result)
      (fun result h => result = value ∧ emp h) := by
  have hp : (⟨p.base, ⟨0⟩⟩ : RawPtr U32) = p := by
    rcases p with ⟨base, index⟩
    have he : (⟨0⟩ : Usize) = index := UScalar.eq_of_val_eq hzero.symm
    exact congrArg (RawPtr.mk base) he
  have hstart : p.index.val ≤ 1 := by agrind
  have hbound0 : p.index.val + (0#usize).val ≤ 1 := by simp [hzero]
  have hbound1 : p.index.val + (1#usize).val ≤ 1 := by simp [hzero]
  have hfit0 : p.index.val + (0#usize).val < 2 ^ UScalarTy.numBits .Usize := by
    simp [hzero]
  have hfit1 : p.index.val + (1#usize).val < 2 ^ UScalarTy.numBits .Usize := by
    simp only [hzero, Nat.zero_add]
    scalar_tac
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun _ h => h)
    (fun start h hs => (sep_and_left (start.base = p.base)
      (fun h => start.index.val = p.index.val + (0#usize).val ∧ alloc repr p 1 true h)
      (pointsTo repr p value) h).mp hs |>.imp_right
        (fun hs => (sep_and_left (start.index.val = p.index.val + (0#usize).val)
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
    have he := UScalar.eq_of_val_eq hi
    cases hb
    cases he
    rfl
  subst start
  apply HeapWP.Triple.bind (HeapWP.Triple.conseq (fun _ h => h)
    (fun q h hs => sep_mono
      (fun a (hp : q.base = p.base ∧ q.index.val = p.index.val + (1#usize).val ∧
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
  have hz : p.index.val = 0 := by
    obtain ⟨a, b, _, _, ha, _⟩ := hp
    exact ha.1
  apply HeapWP.Spec.mono
    (one_past_end_tail.spec repr p value hsize hz h F s' hp hd hm' hi')
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
