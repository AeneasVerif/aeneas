module

public import RawTransmuteExternals.Properties
public import Aeneas.Std.Heap.RangeRestoration
import all RawBoxProofs
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap.Separation

public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace raw_transmute_externals

def borrowedWord (p : MutRawPtr U32) (bptr : BasePtr) : Assertion :=
  block raw_box.u32Repr p bptr (List.replicate 4 .borrowed)

def pendingWord (p : MutRawPtr U32) (bptr : BasePtr) : Assertion :=
  sep (alloc raw_box.u32Repr p bptr 1 false) (borrowedWord p bptr)

theorem word_as_array {p : MutRawPtr U32} {bptr : BasePtr} {word : U32}
    {depth : Nat} {h : Fragment} (hp : pointsTo raw_box.u32Repr p bptr word depth h) :
    pointsTo arrayRepr (p.cast FourBytes) bptr (toLittleBytes word) depth h := by
  obtain ⟨data, encoded, lower, _, cells⟩ := hp
  refine ⟨data, ?_, lower, by simp [arrayRepr], cells⟩
  change data = (wordEncoding word).map Aeneas.Std.Byte.data at encoded
  change data = (fourVector (toLittleBytes word)).map Aeneas.Std.Byte.data
  rw [show fourVector (toLittleBytes word) = wordEncoding word from fourVector_fourBytes _]
  exact encoded

theorem array_as_word {p : MutRawPtr U32} {bptr : BasePtr} {value : FourBytes}
    {depth : Nat} {h : Fragment} (aligned : 4 ∣ p.address.val)
    (hp : pointsTo arrayRepr (p.cast FourBytes) bptr value depth h) :
    pointsTo raw_box.u32Repr p bptr (fromLittleBytes value) depth h := by
  obtain ⟨data, encoded, lower, _, cells⟩ := hp
  refine ⟨data, ?_, lower, aligned, cells⟩
  change data = (fourVector value).map Aeneas.Std.Byte.data at encoded
  change data = (wordEncoding (fromLittleBytes value)).map Aeneas.Std.Byte.data
  rw [encoded]
  have he := wordEncoding_decode (fourVector value)
  rw [fourBytes_fourVector] at he
  rw [he]

@[step]
theorem raw_bytes_view.spec (words : MutRawPtr U32) :
    raw_bytes_view words ⦃ (result : MutRawPtr FourBytes) =>
      result = RawPtr.cast FourBytes words ⦄ := by
  simp [raw_bytes_view, ext.transmute_mut]

@[step]
theorem array_pointer_round_trip.spec (words : MutRawPtr U32) :
    array_pointer_round_trip words ⦃ (result : MutRawPtr U32) => result = words ⦄ := by
  simp [array_pointer_round_trip, raw_bytes_view, ext.transmute_mut, RawPtr.cast]

theorem read_word_bytes.spec (words : MutRawPtr U32) (bptr : BasePtr) (word : U32) :
    HeapWP.Triple (pointsTo raw_box.u32Repr words bptr word) (read_word_bytes words)
      (fun bytes h => bytes = toLittleBytes word ∧ pointsTo raw_box.u32Repr words bptr word 0 h) := by
  simp only [read_word_bytes, raw_bytes_view, ext.transmute_mut, bind_ok, ext.read_four]
  intro h F s hp hd hm hi
  have aligned : 4 ∣ words.address.val := hp.choose_spec.2.2.1
  have read := HeapWP.read.spec arrayRepr (words.cast FourBytes) bptr (toLittleBytes word) 0
    (by decide) h F s (word_as_array hp) hd hm hi
  apply HeapWP.Spec.mono read
  rintro bytes s' ⟨h', hd', hm', hi', equal, hp'⟩
  exact ⟨h', hd', hm', hi', equal, by simpa using array_as_word aligned hp'⟩

theorem write_array_word.spec (p : MutRawPtr U32) (bptr : BasePtr) (word : U32) (value : FourBytes) :
    HeapWP.Triple (pointsTo raw_box.u32Repr p bptr word)
      (MutRawPtr.write arrayRepr (RawPtr.cast FourBytes p) value)
      (fun _ => pointsTo raw_box.u32Repr p bptr (fromLittleBytes value)) := by
  intro h F s hp hd hm hi
  have aligned : 4 ∣ p.address.val := hp.choose_spec.2.2.1
  apply HeapWP.Spec.mono
    (HeapWP.write.spec arrayRepr (p.cast FourBytes) bptr (toLittleBytes word) value
      (arrayRepr_noPointers value) (by decide) h F s (word_as_array hp) hd hm hi)
  rintro _ s' ⟨h', hd', hm', hi', hp'⟩
  exact ⟨h', hd', hm', hi', array_as_word aligned hp'⟩

theorem overwrite_word_bytes.spec (words : MutRawPtr U32) (bptr : BasePtr)
    (word : U32) (bytes : FourBytes) :
    HeapWP.Triple (pointsTo raw_box.u32Repr words bptr word) (overwrite_word_bytes words bytes)
      (fun result h => result = fromLittleBytes bytes ∧
        pointsTo raw_box.u32Repr words bptr (fromLittleBytes bytes) 0 h) := by
  simp only [overwrite_word_bytes, raw_bytes_view, ext.transmute_mut, bind_ok,
    ext.write_four, ext.read_word]
  apply HeapWP.Triple.bind (write_array_word.spec words bptr word bytes)
  intro _
  exact HeapWP.read.spec raw_box.u32Repr words bptr (fromLittleBytes bytes) 0 (by decide)

/-- The callback carries the matching return authority at the forward-produced
state. Borrowed cells alone do not authorize an arbitrary restoration. -/
theorem ext.borrow_four.spec (p : MutRawPtr U32) (bptr : BasePtr) (word : U32)
    (h F : Fragment) (s : Heap) (hp : pointsTo raw_box.u32Repr p bptr word 0 h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s (h ∪ F)) (hi : s.Inv) :
    HeapWP.Spec (ext.borrow_four (p.cast FourBytes))
      (fun (bytes, back) s' => bytes = toLittleBytes word ∧
        (∃ h', h'.Disjoint F ∧ Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧ borrowedWord p bptr h') ∧
        ∀ updated, HeapWP.Spec (back updated)
          (fun _ s'' => ∃ h'', h''.Disjoint F ∧ Fragment.Matches s'' (h'' ∪ F) ∧ s''.Inv ∧
            pointsTo raw_box.u32Repr p bptr (fromLittleBytes updated) 0 h'') s') s := by
  have aligned : 4 ∣ p.address.val := hp.choose_spec.2.2.1
  unfold ext.borrow_four
  apply HeapWP.Spec.mono (HeapWP.borrowWithBack.spec arrayRepr (p.cast FourBytes) bptr
    (toLittleBytes word) (by decide) h F s (word_as_array hp) hd hm hi)
  rintro ⟨bytes, back⟩ s' ⟨equal, suspended, returns⟩
  refine ⟨equal, ?_, ?_⟩
  · obtain ⟨h', hd', hm', hi', lower, _, cells⟩ := suspended
    exact ⟨h', hd', hm', hi', lower, aligned, cells⟩
  · intro updated
    apply HeapWP.Spec.mono (returns updated (arrayRepr_noPointers updated))
    rintro _ s'' ⟨h'', hd'', hm'', hi'', restored⟩
    exact ⟨h'', hd'', hm'', hi'', array_as_word aligned restored⟩

/-- Exact forward bytes and restoration of every replacement, consuming the
temporary exposure before returning the complete safe word. -/
theorem bytes_view.spec (word : U32) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F) :
    HeapWP.Spec (bytes_view word)
      (fun (bytes, back) s' => bytes = toLittleBytes word ∧
        ∀ updated, HeapWP.Spec (back updated)
          (fun result s'' => result = fromLittleBytes updated ∧
            Fragment.Matches s'' F ∧ s''.Inv) s') s := by
  unfold bytes_view core.ptr.from_mut
  simp only [Std.bind_assoc, bind_ok]
  apply HeapWP.Spec.bind
    (HeapWP.allocExposure_encoded.spec raw_box.u32Repr word (word_exposure_encoding word)
      s F hi hm)
  rintro p s₁ ⟨_, h, hd, hm₁, hi₁, a, b, hab, rfl, ha, hp⟩
  simp only [ext.transmute_mut, bind_ok]
  have hdf := Fragment.disjoint_union_right.mpr
    ⟨hab.symm, Fragment.disjoint_union_left.mp hd |>.2⟩
  have hmf : Fragment.Matches s₁ (b ∪ (a ∪ F)) := by
    simpa only [← Fragment.union_assoc, Fragment.union_comm b a] using hm₁
  apply HeapWP.Spec.bind (ext.borrow_four.spec p p.address word b (a ∪ F) s₁ hp hdf hmf hi₁)
  rintro ⟨bytes, back⟩ s₂ ⟨equal, _, returns⟩
  apply HeapWP.Spec.pure _ _ _ |>.mpr
  refine ⟨equal, ?_⟩
  intro updated
  apply HeapWP.Spec.bind (returns updated)
  rintro _ s₃ ⟨cells, hdc, hmc, hic, restored⟩
  have combined : (a ∪ cells).Disjoint F := Fragment.disjoint_union_left.mpr
    ⟨Fragment.disjoint_union_left.mp hd |>.1, Fragment.disjoint_union_right.mp hdc |>.2⟩
  have matched : Fragment.Matches s₃ ((a ∪ cells) ∪ F) := by
    simpa only [← Fragment.union_assoc, Fragment.union_comm cells a] using hmc
  have resource : sep (alloc raw_box.u32Repr p p.address 1 false)
      (readable raw_box.u32Repr p p.address (fromLittleBytes updated)) (a ∪ cells) :=
    ⟨a, cells, (Fragment.disjoint_union_right.mp hdc).1.symm, rfl, ha, pointsTo_readable restored⟩
  apply HeapWP.Spec.mono
    (HeapWP.end_from_mut.spec raw_box.u32Repr p p.address (fromLittleBytes updated)
      (by decide) (a ∪ cells) F s₃ resource combined matched hic)
  rintro result s₄ ⟨empty, _, matching, invariant, result_eq, empty_eq⟩
  subst empty
  exact ⟨result_eq, by simpa using matching, invariant⟩

/-- info: 'raw_transmute_externals.raw_bytes_view.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_bytes_view.spec

/-- info: 'raw_transmute_externals.array_pointer_round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms array_pointer_round_trip.spec

/-- info: 'raw_transmute_externals.read_word_bytes.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_word_bytes.spec

/-- info: 'raw_transmute_externals.write_array_word.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms write_array_word.spec

/-- info: 'raw_transmute_externals.overwrite_word_bytes.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms overwrite_word_bytes.spec

/-- info: 'raw_transmute_externals.ext.borrow_four.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ext.borrow_four.spec

/-- info: 'raw_transmute_externals.bytes_view.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bytes_view.spec

end raw_transmute_externals
