module

public import RawTransmuteExternals.Properties
import all RawBoxProofs
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Separation

public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace raw_transmute_externals

def borrowedWord (p : MutRawPtr U32) : Assertion :=
  block raw_box.u32Repr p (Vector.replicate 4 (.borrowed : Cell U8)).toList

def pendingWord (p : MutRawPtr U32) : Assertion :=
  sep (alloc raw_box.u32Repr p 1 false) (borrowedWord p)

/- Access uses the array's alignment of one, while ownership retains the
original word-aligned byte resources. The two fragments are not equated. -/
theorem modify_array_word.spec (p : MutRawPtr U32)
    (old new : Vector (Cell U8) 4)
    (change : ∀ {r}, Vector (Cell U8) r → Option (Vector (Cell U8) r))
    (hc : ∀ {r} (bytes : Vector (Cell U8) r) (hb : p.byteOffset.val + 4 ≤ r),
      raw_box.u32Repr.select bytes p.byteOffset.val hb = old →
      change bytes = some (raw_box.u32Repr.update bytes p.byteOffset.val hb new)) :
    SepLogic.Triple (block raw_box.u32Repr p old.toList)
      (fun s (_ : Unit) s' =>
        Heap.modify arrayRepr (RawPtr.cast FourBytes p) change s = some s')
      (fun _ => block raw_box.u32Repr p new.toList) := by
  rintro h F s ⟨hpa, rfl⟩ hd hm hi
  obtain ⟨blk, hb, hl, ha, hs⟩ :=
    bytes_of_matches (by decide : 0 < raw_box.u32Repr.size)
      ((Fragment.matches_union _ _ _).mp hm).1
  have hrun := Heap.modify.spec arrayRepr (RawPtr.cast FourBytes p) change s blk _ hl
    (by simp [arrayRepr]) (by simp [arrayRepr, RawPtr.cast]) (hc blk.bytes hb hs)
  refine ⟨⟨(), _, hrun⟩, ?_⟩
  rintro _ s' he
  have he := Option.some.inj (hrun.symm.trans he)
  subst s'
  exact ⟨_, disjoint_cellsHeap_congr (old := old.toList) (new := new.toList)
      (by simp only [Vector.length_toList]) hd,
    (Fragment.matches_union _ _ _).mpr ⟨matches_update hl ha hb _, matches_update_frame hl hb hd
      ((Fragment.matches_union _ _ _).mp hm).2⟩, hi.storeRepr _ _, hpa, rfl⟩

theorem read_array_of_word {s : Heap} {p : MutRawPtr U32} {word : U32} {h : Fragment}
    (hp : pointsTo raw_box.u32Repr p word 0 h)
    (hm : Fragment.Matches s h) :
    Heap.read arrayRepr (RawPtr.cast FourBytes p) s = some (toLittleBytes word) := by
  obtain ⟨data, decoded, _, rfl⟩ := hp
  change Vector U8 4 at data
  obtain ⟨blk, hb, hl, _, hs⟩ :=
    bytes_of_matches (by decide : 0 < raw_box.u32Repr.size) hm
  have hs' : arrayRepr.select blk.bytes p.byteOffset.val hb =
      data.map (Cell.shared 0 ∘ some) := hs
  have hr : arrayRepr.read blk.bytes p.byteOffset.val = some (fourBytes data) := by
    unfold Repr.read
    rw [dite_eq_left ⟨by decide, hb⟩, hs']
    change (Repr.readBytes 4 (data.map (Cell.shared 0 ∘ some))).bind _ = _
    rw [Repr.readBytes_shared data 0]
    rfl
  have he : Heap.read arrayRepr (RawPtr.cast FourBytes p) s = some (fourBytes data) := by
    simpa [Heap.read, hl, RawPtr.cast, arrayRepr] using hr
  rw [bytes_of_word_decode data word decoded] at he
  exact he

@[step]
theorem raw_bytes_view.spec (words : MutRawPtr U32) :
    raw_bytes_view words ⦃ (result : MutRawPtr FourBytes) =>
      result = RawPtr.cast FourBytes words ⦄ := by
  simp [raw_bytes_view, ext.transmute_mut]

@[step]
theorem array_pointer_round_trip.spec (words : MutRawPtr U32) :
    array_pointer_round_trip words ⦃ (result : MutRawPtr U32) => result = words ⦄ := by
  simp [array_pointer_round_trip, raw_bytes_view, ext.transmute_mut, RawPtr.cast]

theorem read_word_bytes.spec (words : MutRawPtr U32) (word : U32) :
    HeapWP.Triple (pointsTo raw_box.u32Repr words word) (read_word_bytes words)
      (fun bytes h => bytes = toLittleBytes word ∧ pointsTo raw_box.u32Repr words word 0 h) := by
  simp only [read_word_bytes, raw_bytes_view, ext.transmute_mut, bind_ok, ext.read_four]
  apply HeapWP.Triple.checkedModify
  intro h F s hp hd hm hi
  have hr := read_array_of_word hp ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨toLittleBytes word, s, hr, rfl⟩, ?_⟩
  rintro bytes s' ⟨hv, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hv.symm.trans hr), hp⟩

theorem write_array_word.spec (p : MutRawPtr U32) (word : U32) (value : FourBytes) :
    HeapWP.Triple (pointsTo raw_box.u32Repr p word)
      (MutRawPtr.write arrayRepr (RawPtr.cast FourBytes p) value)
      (fun _ => pointsTo raw_box.u32Repr p (fromLittleBytes value)) := by
  unfold MutRawPtr.write
  apply HeapWP.Triple.bind (HeapWP.Triple.choose _ arrayRepr value)
  rintro ⟨data, decoded⟩
  change Vector U8 4 at data
  have hv : fourBytes data = value := Option.some.inj decoded
  have hw : raw_box.u32Repr.decode data = some (fromLittleBytes value) := by
    rw [word_decode_bytes, hv]
  apply HeapWP.Triple.checkedModify
  apply SepLogic.Triple.conseq (fun _ h => h) (fun _ _ hp => ⟨data, hw, hp⟩)
  intro h F s ⟨old, _, hp⟩ hd hm hi
  change Vector U8 4 at old
  apply (modify_array_word.spec p (old.map (Cell.shared 0 ∘ some))
    (data.map (Cell.shared 0 ∘ some))
    (fun bytes => arrayRepr.write bytes p.byteOffset.val value data decoded) ?_) h F s hp hd hm hi
  intro r bytes hb he
  have he' : arrayRepr.select bytes p.byteOffset.val hb =
      old.map (Cell.shared 0 ∘ some) := he
  dsimp only [arrayRepr, raw_box.u32Repr] at he' ⊢
  unfold Repr.write
  rw [dite_eq_left ⟨by decide, hb⟩, he']
  have hwritten := Repr.writeBytes_shared (old.map some) data
  simp only [Vector.map_map, Function.comp_def] at hwritten
  simp only [Function.comp_def]
  rw [hwritten]
  rfl

theorem overwrite_word_bytes.spec (words : MutRawPtr U32) (word : U32) (bytes : FourBytes) :
    HeapWP.Triple (pointsTo raw_box.u32Repr words word) (overwrite_word_bytes words bytes)
      (fun result h => result = fromLittleBytes bytes ∧
        pointsTo raw_box.u32Repr words (fromLittleBytes bytes) 0 h) := by
  simp only [overwrite_word_bytes, raw_bytes_view, ext.transmute_mut, bind_ok,
    ext.write_four, ext.read_word]
  apply HeapWP.Triple.bind (write_array_word.spec words word bytes)
  intro _
  exact HeapWP.read.spec raw_box.u32Repr words (fromLittleBytes bytes) 0 (by decide)

theorem borrow_array_state.spec (p : MutRawPtr U32) (word : U32) :
    SepLogic.Triple (pointsTo raw_box.u32Repr p word)
      (fun s (_ : Unit) s' => Heap.borrow arrayRepr (RawPtr.cast FourBytes p) s = some s')
      (fun _ => borrowedWord p) := by
  intro h F s ⟨data, _, hp⟩ hd hm hi
  change Vector U8 4 at data
  apply (modify_array_word.spec p (data.map (Cell.shared 0 ∘ some))
    (Vector.replicate 4 .borrowed)
    (fun bytes => arrayRepr.borrow bytes p.byteOffset.val) ?_) h F s hp hd hm hi
  intro r bytes hb he
  have he' : arrayRepr.select bytes p.byteOffset.val hb =
      data.map (Cell.shared 0 ∘ some) := he
  unfold Repr.borrow
  rw [dite_eq_left ⟨by decide, hb⟩, he']
  dsimp only [arrayRepr, raw_box.u32Repr] at *
  simp only [Vector.mapM_map, Function.comp_def, Cell.borrow]
  rw [vector_mapM_some]
  have hm : data.map (fun _ => (Cell.borrowed : Cell U8)) = Vector.replicate 4 .borrowed := by
    apply Vector.ext
    intro i hi
    simp
  simp [Repr.update, hm]

theorem borrow_array.spec (p : MutRawPtr U32) (word : U32) :
    HeapWP.Triple (pointsTo raw_box.u32Repr p word)
      (RawPtr.borrow arrayRepr (RawPtr.cast FourBytes p))
      (fun bytes h => bytes = toLittleBytes word ∧ borrowedWord p h) := by
  have ht : HeapWP.Triple (pointsTo raw_box.u32Repr p word)
      (RawPtr.borrowRange arrayRepr (RawPtr.cast FourBytes p) 1)
      (fun bytes h => bytes = [toLittleBytes word] ∧ borrowedWord p h) := by
    apply HeapWP.Triple.checkedModify
    unfold State.borrowRange
    simp only [Heap.borrowRange_single]
    intro h F s hp hd hm hi
    have hr : Heap.readRange arrayRepr (RawPtr.cast FourBytes p) 1 s =
        some [toLittleBytes word] := by
      rw [Heap.readRange_single,
        read_array_of_word hp ((Fragment.matches_union _ _ _).mp hm).1]
      rfl
    obtain ⟨⟨_, s₁, hc⟩, hpost⟩ := borrow_array_state.spec p word h F s hp hd hm hi
    refine ⟨⟨[toLittleBytes word], s₁, hr, hc⟩, ?_⟩
    rintro bytes s₁ ⟨hv, hc⟩
    obtain ⟨h₁, hd₁, hm₁, hi₁, hq⟩ := hpost () s₁ hc
    exact ⟨h₁, hd₁, hm₁, hi₁, Option.some.inj (hv.symm.trans hr), hq⟩
  unfold RawPtr.borrow
  apply HeapWP.Triple.bind ht
  intro bytes
  apply HeapWP.Triple.pure_pre
  intro he
  subst bytes
  exact HeapWP.Triple.pure _ (toLittleBytes word)

theorem restore_array_state.spec (p : MutRawPtr U32) (value : FourBytes)
    (data : Vector U8 4) (decoded : arrayRepr.decode data = some value) :
    SepLogic.Triple (borrowedWord p)
      (fun s (_ : Unit) s' =>
        Heap.endBorrow arrayRepr (RawPtr.cast FourBytes p) value data decoded s = some s')
      (fun _ => pointsTo raw_box.u32Repr p (fromLittleBytes value)) := by
  have hv : fourBytes data = value := Option.some.inj decoded
  have hw : raw_box.u32Repr.decode data = some (fromLittleBytes value) := by
    rw [word_decode_bytes, hv]
  apply SepLogic.Triple.conseq (fun _ h => h) (fun _ _ hp => ⟨data, hw, hp⟩)
  apply modify_array_word.spec p (Vector.replicate 4 .borrowed)
    (data.map (Cell.shared 0 ∘ some))
    (fun bytes => arrayRepr.endBorrow bytes p.byteOffset.val value data decoded)
  intro r bytes hb he
  have he' : arrayRepr.select bytes p.byteOffset.val hb =
      Vector.replicate 4 .borrowed := he
  unfold Repr.endBorrow
  rw [dite_eq_left ⟨by decide, hb⟩, he']
  dsimp only [arrayRepr, raw_box.u32Repr] at *
  have hz : (Vector.replicate 4 (Cell.borrowed : Cell U8)).zip data =
      data.map (fun byte => (Cell.borrowed, byte)) := by
    apply Vector.ext
    intro i hi
    simp
  rw [hz, Vector.mapM_map]
  simp only [Function.comp_def, Cell.endBorrow]
  rw [vector_mapM_some]
  rfl

theorem restore_array.spec (p : MutRawPtr U32) (value : FourBytes) :
    HeapWP.Triple (borrowedWord p)
      (RawPtr.endBorrow arrayRepr (RawPtr.cast FourBytes p) value)
      (fun _ => pointsTo raw_box.u32Repr p (fromLittleBytes value)) := by
  unfold RawPtr.endBorrow RawPtr.endBorrowRange
  apply HeapWP.Triple.bind (HeapWP.Triple.chooseList _ arrayRepr [value])
  rintro ⟨encodings, hd⟩
  have he : ∃ encoding, encodings = [encoding] ∧ arrayRepr.decode encoding = some value := by
    cases encodings
    · simp at hd
    · rename_i encoding tail
      have h := List.cons.inj hd
      have ht : tail = [] := by simpa using h.2
      exact ⟨encoding, by simp [ht], h.1⟩
  obtain ⟨encoding, rfl, decoded⟩ := he
  apply HeapWP.Triple.checkedModify
  simpa only [Heap.endBorrowRange_single arrayRepr (RawPtr.cast FourBytes p) encoding value decoded]
    using restore_array_state.spec p value encoding decoded

theorem ext.borrow_four.spec (p : MutRawPtr U32) (word : U32) :
    HeapWP.Triple (pointsTo raw_box.u32Repr p word)
      (ext.borrow_four (RawPtr.cast FourBytes p))
      (fun (bytes, back) h => bytes = toLittleBytes word ∧ borrowedWord p h ∧
        ∀ updated, HeapWP.Triple (borrowedWord p) (back updated)
          (fun _ => pointsTo raw_box.u32Repr p (fromLittleBytes updated))) := by
  unfold ext.borrow_four
  apply HeapWP.Triple.bind (borrow_array.spec p word)
  intro bytes
  apply HeapWP.Triple.pure_pre
  intro he
  subst bytes
  apply HeapWP.Triple.conseq (fun _ hp => hp) ?_ (HeapWP.Triple.pure _ _)
  rintro _ _ ⟨rfl, hp⟩
  exact ⟨rfl, hp, fun updated => restore_array.spec p updated⟩

/-- Heap-aware step contract: exact forward bytes and restoration of every
replacement, consuming the exposure before returning the safe word. -/
theorem bytes_view.spec (word : U32) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F)
    (hc : s.next.val + 1 < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Spec (bytes_view word)
      (fun (bytes, back) s' =>
        bytes = toLittleBytes word ∧
        ∃ (p : MutRawPtr U32) (h : Fragment),
          h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          pendingWord p h ∧
          ∀ updated, HeapWP.Triple (pendingWord p) (back updated)
            (fun result h' => result = fromLittleBytes updated ∧ emp h')) s := by
  unfold bytes_view core.ptr.from_mut
  simp only [Std.bind_assoc, bind_ok]
  have hfit : raw_box.u32Repr.size < 2 ^ UScalarTy.numBits .Usize := by
    change 4 < 2 ^ UScalarTy.numBits .Usize
    scalar_tac
  apply HeapWP.Spec.bind
    (HeapWP.allocExposure.spec raw_box.u32Repr word s F hi hm hc hfit)
  rintro p s₁ ⟨_, h, hd, hm₁, hi₁, hp⟩
  simp only [ext.transmute_mut, bind_ok]
  have ht := HeapWP.Triple.conseq
    (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ _ hp => hp)
    (HeapWP.frame (R := alloc raw_box.u32Repr p 1 false) (ext.borrow_four.spec p word))
  apply HeapWP.Spec.bind (ht h F s₁ hp hd hm₁ hi₁)
  rintro ⟨bytes, back⟩ s₂ ⟨h₂, hd₂, hm₂, hi₂, hb⟩
  obtain ⟨cells, owned, hdis, heq, ⟨hbytes, hcell, hback⟩, ho⟩ := hb
  apply HeapWP.Spec.pure _ _ _ |>.mpr
  refine ⟨hbytes, p, h₂, hd₂, hm₂, hi₂, ?_, ?_⟩
  · exact (sep_comm _ _ h₂).mp ⟨cells, owned, hdis, heq, hcell, ho⟩
  · intro updated
    apply HeapWP.Triple.bind
      (HeapWP.Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp)
        (fun _ h hp => (sep_comm _ _ h).mp hp)
        (HeapWP.frame (R := alloc raw_box.u32Repr p 1 false) (hback updated)))
    intro _
    exact HeapWP.end_from_mut.spec raw_box.u32Repr p (fromLittleBytes updated) (by decide)

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
