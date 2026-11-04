module

public import RawBox
public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Alloc.Boxed
import all Aeneas.Std.Core.Ptr

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

theorem dataBytes_numeric (values : Vector U8 n) :
    (values.map Aeneas.Std.Byte.data).mapM Aeneas.Std.Byte.numeric = some values := by
  rw [Vector.mapM_map]
  change values.mapM (fun x => pure (id x)) = some values
  rw [Vector.mapM_pure]
  simp

theorem numericBytes_eq {n : Nat} (bytes bytes' : Vector Aeneas.Std.Byte n)
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
    (bptr : BasePtr) (initial replacement : U32)
    (noPointers : ∀ q, ¬ repr.Carries replacement q) (hsize : 0 < repr.size) :
    HeapWP.RootTriple [p.provenance]
      (sep (alloc repr p bptr 1 true) (pointsTo repr p bptr initial))
      (do MutRawPtr.write repr p replacement
          let value ← RawPtr.read repr p
          let _ ← alloc.boxed.Box.from_raw repr p
          pure value)
      (fun value h => value = replacement ∧ empty h) := by
  apply HeapWP.RootTriple.bind
    (HeapWP.RootTriple.write_owned repr p bptr initial replacement true noPointers hsize)
  intro _
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.read_owned repr p bptr replacement true hsize)
  intro value
  apply HeapWP.RootTriple.pure_pre
  intro hv
  subst value
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq (fun _ hp => hp)
    (fun _ _ hp => hp.2) (HeapWP.RootTriple.fromRaw repr p bptr replacement hsize (by simp)))
  intro _
  exact HeapWP.RootTriple.pure empty replacement

/-- The actual lifecycle consumes its allocation and preserves any matching frame.
Allocation requires compatible concrete placement, not bounded ghost identifiers. -/
theorem round_trip.spec (repr : Aeneas.Std.Repr U32) (initial replacement : U32)
    (noPointers : ∀ q, ¬ repr.Carries replacement q) (hsize : 0 < repr.size)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F) :
    HeapWP.Spec (round_trip repr initial replacement)
      (fun value s' => value = replacement ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold round_trip
  apply HeapWP.Spec.bind (HeapWP.intoRaw_return.spec repr initial s F hi hm)
  rintro p s' ⟨authority, _, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono
    (round_trip_tail.spec repr p p.address initial replacement noPointers hsize
      h F s' hp hd hm' hi' (by simpa using authority))
  rintro value s'' ⟨_, h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

theorem stored_pointer_tail.spec (repr : Aeneas.Std.Repr U32)
    (pointerRepr : Aeneas.Std.Repr (MutRawPtr U32)) (target : MutRawPtr U32)
    (slot : MutRawPtr (MutRawPtr U32)) (targetBase slotBase : BasePtr)
    (initial replacement : U32) (noPointers : ∀ q, ¬ repr.Carries replacement q)
    (hsize : 0 < repr.size) (hptr : 0 < pointerRepr.size) :
    HeapWP.RootTriple [target.provenance, slot.provenance]
      (sep (sep (alloc pointerRepr slot slotBase 1 true) (pointsTo pointerRepr slot slotBase target))
        (sep (alloc repr target targetBase 1 true) (pointsTo repr target targetBase initial)))
      (do let loaded ← RawPtr.read pointerRepr slot
          MutRawPtr.write repr loaded replacement
          let _ ← alloc.boxed.Box.from_raw pointerRepr slot
          alloc.boxed.Box.from_raw repr target)
      (fun value h => value = replacement ∧ empty h) := by
  let targetOwn := sep (alloc repr target targetBase 1 true) (pointsTo repr target targetBase initial)
  let slotOwn := sep (alloc pointerRepr slot slotBase 1 true) (pointsTo pointerRepr slot slotBase target)
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq
    (fun _ h => h)
    (fun loaded h hp => (sep_and_left (loaded = target) slotOwn targetOwn h).mp hp)
    (HeapWP.RootTriple.frame (R := targetOwn)
      (HeapWP.RootTriple.read_owned pointerRepr slot slotBase target true hptr)))
  intro loaded
  apply HeapWP.RootTriple.pure_pre
  intro he
  subst loaded
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => (sep_comm _ _ h).mp hp)
    (HeapWP.RootTriple.frame (R := slotOwn)
      (HeapWP.RootTriple.write_owned repr target targetBase initial replacement true noPointers hsize)))
  intro _
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq
    (fun _ hp => hp)
    (fun _ h hp => (sep_empty_left
      (sep (alloc repr target targetBase 1 true) (pointsTo repr target targetBase replacement)) h).mp
        (sep_mono (fun _ hp => hp.2) (fun _ h => h) hp))
    (HeapWP.RootTriple.frame
      (R := sep (alloc repr target targetBase 1 true) (pointsTo repr target targetBase replacement))
      (HeapWP.RootTriple.fromRaw pointerRepr slot slotBase target hptr (by simp))))
  intro _
  exact HeapWP.RootTriple.fromRaw repr target targetBase replacement hsize (by simp)

/-- A pointer is encoded in the second allocation using its own explicit
representation, not assumed to fit in one machine word. -/
theorem stored_pointer.spec (repr : Aeneas.Std.Repr U32)
    (pointerRepr : Aeneas.Std.Repr (MutRawPtr U32)) (initial replacement : U32)
    (noPointers : ∀ q, ¬ repr.Carries replacement q)
    (hsize : 0 < repr.size) (hptr : 0 < pointerRepr.size)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F) :
    HeapWP.Spec (stored_pointer repr pointerRepr initial replacement)
      (fun value s' => value = replacement ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold stored_pointer
  apply HeapWP.Spec.bind (HeapWP.intoRaw_return.spec repr initial s F hi hm)
  rintro target s₁ ⟨targetAuthority, _, a, haF, hm₁, hi₁, hp⟩
  have second := HeapWP.intoRaw_preserving.spec pointerRepr target s₁ (a ∪ F)
    hi₁ hm₁
  apply HeapWP.Spec.bind second
  rintro slot s₂ ⟨preserve, slotAuthority, _, b, hd, hm₂, hi₂, hq⟩
  have owned := hp
  obtain ⟨cleanup, bytes, _, ha, hc, _⟩ := owned
  have matchesCleanup : Fragment.Matches s₁ cleanup := by
    have matchesA := ((Fragment.matches_union _ _ _).mp hm₁).1
    rw [ha, Fragment.matches_union] at matchesA
    exact matchesA.1
  obtain ⟨blk, hl, active⟩ := alloc_active hc matchesCleanup
  have targetAuthority' := preserve _ _ hl active targetAuthority
  obtain ⟨hba, hbF⟩ := Fragment.disjoint_union_right.mp hd
  have hown : sep (sep (alloc pointerRepr slot slot.address 1 true)
      (pointsTo pointerRepr slot slot.address target))
      (sep (alloc repr target target.address 1 true) (pointsTo repr target target.address initial)) (b ∪ a) :=
    ⟨b, a, hba, rfl, hq, hp⟩
  have hd' := Fragment.disjoint_union_left.mpr ⟨hbF, haF⟩
  have hm' : Fragment.Matches s₂ (b ∪ a ∪ F) := by
    simpa [Fragment.union_assoc] using hm₂
  apply HeapWP.Spec.mono
    (stored_pointer_tail.spec repr pointerRepr target slot target.address slot.address
      initial replacement noPointers hsize hptr (b ∪ a) F s₂ hown hd' hm' hi₂
      (by simpa using And.intro targetAuthority' slotAuthority))
  rintro value s' ⟨_, h', _, hm', hi', hv, rfl⟩
  exact ⟨hv, by simpa using hm', hi'⟩

theorem replace_pair_tail.spec (repr : Aeneas.Std.Repr (U32 × U32))
    (p : MutRawPtr (U32 × U32)) (bptr : BasePtr) (first second replacement : U32)
    (noPointers : ∀ q, ¬ repr.Carries (first, replacement) q) (hsize : 0 < repr.size) :
    HeapWP.RootTriple [p.provenance]
      (sep (alloc repr p bptr 1 true) (pointsTo repr p bptr (first, second)))
      (do let (i, _) ← RawPtr.read repr p
          MutRawPtr.write repr p (i, replacement)
          alloc.boxed.Box.from_raw repr p)
      (fun value h => value = (first, replacement) ∧ empty h) := by
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.read_owned repr p bptr (first, second) true hsize)
  intro value
  apply HeapWP.RootTriple.pure_pre
  intro hv
  subst value
  apply HeapWP.RootTriple.bind
    (HeapWP.RootTriple.write_owned repr p bptr (first, second) (first, replacement) true noPointers hsize)
  intro _
  exact HeapWP.RootTriple.fromRaw repr p bptr (first, replacement) hsize (by simp)

/-- Pair replacement preserves the first component and consumes the allocation. -/
theorem replace_pair.spec (repr : Aeneas.Std.Repr (U32 × U32))
    (first second replacement : U32) (hsize : 0 < repr.size)
    (noPointers : ∀ q, ¬ repr.Carries (first, replacement) q)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F) :
    HeapWP.Spec (replace_pair repr first second replacement)
      (fun value s' => value = (first, replacement) ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold replace_pair
  apply HeapWP.Spec.bind (HeapWP.intoRaw_return.spec repr (first, second) s F hi hm)
  rintro p s' ⟨authority, _, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono
    (replace_pair_tail.spec repr p p.address first second replacement noPointers hsize
      h F s' hp hd hm' hi' (by simpa using authority))
  rintro value s'' ⟨_, h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

theorem one_past_end_tail.spec (repr : Aeneas.Std.Repr U32)
    (p : MutRawPtr U32) (bptr : BasePtr) (value : U32) (hsize : 0 < repr.size) :
    HeapWP.RootTriple [p.provenance]
      (sep (alloc repr p bptr 1 true) (pointsTo repr p bptr value))
      (do let start ← RawPtr.add repr p 0#usize
          let _ ← RawPtr.add repr p 1#usize
          let result ← RawPtr.read repr start
          let _ ← alloc.boxed.Box.from_raw repr p
          pure result)
      (fun result h => result = value ∧ empty h) := by
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq (fun _ h => h)
    (fun start h hs => (sep_and_left (start.provenance = p.provenance)
      (fun h => start.address.val = p.address.val + (0#usize).val * repr.size ∧
        alloc repr p bptr 1 true h)
      (pointsTo repr p bptr value) h).mp hs |>.imp_right
        (fun hs => (sep_and_left (start.address.val = p.address.val + (0#usize).val * repr.size)
          (alloc repr p bptr 1 true) (pointsTo repr p bptr value) h).mp hs))
    (HeapWP.RootTriple.frame (R := pointsTo repr p bptr value)
      (HeapWP.RootTriple.add_alloc repr p bptr 0#usize 1 true (by decide))))
  intro start
  apply HeapWP.RootTriple.pure_pre
  intro hb
  apply HeapWP.RootTriple.pure_pre
  intro hi
  have he : start = p := by
    have same : start.address = p.address := UScalar.eq_of_val_eq (by simpa using hi)
    cases start
    cases p
    cases hb
    cases same
    rfl
  subst start
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq (fun _ h => h)
    (fun q h hs => sep_mono
      (fun a (hp : q.provenance = p.provenance ∧ q.address.val = p.address.val + (1#usize).val * repr.size ∧
        alloc repr p bptr 1 true a) => hp.2.2) (fun _ hp => hp) hs)
    (HeapWP.RootTriple.frame (R := pointsTo repr p bptr value)
      (HeapWP.RootTriple.add_alloc repr p bptr 1#usize 1 true (by decide))))
  intro _
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.read_owned repr p bptr value true hsize)
  intro result
  apply HeapWP.RootTriple.pure_pre
  intro hr
  subst result
  apply HeapWP.RootTriple.bind (HeapWP.RootTriple.conseq
    (fun _ hp => hp) (fun _ _ hp => hp.2)
    (HeapWP.RootTriple.fromRaw repr p bptr value hsize (by simp)))
  intro _
  exact HeapWP.RootTriple.pure empty value

/-- Forming a one-past pointer does not authorize dereferencing it. The example
reads the original start pointer and then consumes the allocation. -/
theorem one_past_end.spec (repr : Aeneas.Std.Repr U32) (value : U32)
    (hsize : 0 < repr.size)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F) :
    HeapWP.Spec (one_past_end repr value)
      (fun result s' => result = value ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  unfold one_past_end
  apply HeapWP.Spec.bind (HeapWP.intoRaw_return.spec repr value s F hi hm)
  rintro p s' ⟨authority, _, h, hd, hm', hi', hp⟩
  apply HeapWP.Spec.mono
    (one_past_end_tail.spec repr p p.address value hsize h F s' hp hd hm' hi'
      (by simpa using authority))
  rintro result s'' ⟨_, h', _, hm'', hi'', hv, rfl⟩
  exact ⟨hv, by simpa using hm'', hi''⟩

/-- Concrete byte semantics, with no representation hypothesis left to the caller. -/
theorem round_trip_u32.spec (initial replacement : U32)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F) :
    HeapWP.Spec (round_trip u32Repr initial replacement)
      (fun value s' => value = replacement ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  exact round_trip.spec u32Repr initial replacement (u32Repr_noPointers replacement)
    (by decide) s F hi hm

theorem replace_pair_u32.spec (first second replacement : U32)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F) :
    HeapWP.Spec (replace_pair pairRepr first second replacement)
      (fun value s' => value = (first, replacement) ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  exact replace_pair.spec pairRepr first second replacement (by decide)
    (pairRepr_noPointers (first, replacement)) s F hi hm

theorem one_past_end_u32.spec (value : U32)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F) :
    HeapWP.Spec (one_past_end u32Repr value)
      (fun result s' => result = value ∧ Fragment.Matches s' F ∧ s'.Inv) s := by
  exact one_past_end.spec u32Repr value (by decide) s F hi hm

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
