module

public import Aeneas.Std.Heap.Ranges
public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Heap.Ranges
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Separation

/-! Range returns require the matching backward continuation's authority.
Borrowed cells alone do not exclude conflicting observers in other views. -/

@[expose] public section

namespace Aeneas.Std.Heap

theorem storeRepr_same (s : Heap) (base : Nat) (blk : Block)
    (hl : s.allocations base = some blk) : s.storeRepr base blk.repr = s := by
  rcases s with ⟨allocations, next⟩
  change allocations base = some blk at hl
  apply congrArg (fun a => Heap.mk a next)
  funext other
  by_cases he : other = base
  · subst other
    simp [update, hl]
  · simp [update, he]

theorem storeRepr_storeRepr (s : Heap) (base : Nat) (old new : List Cell) :
    (s.storeRepr base old).storeRepr base new = s.storeRepr base new := by
  rcases s with ⟨allocations, next⟩
  apply congrArg (fun a => Heap.mk a next)
  funext other
  by_cases he : other = base
  · subst other
    simp [storeRepr, update, Option.map_map, Function.comp_def]
  · simp [storeRepr, update, he]

theorem modifyRange_empty (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (hinv : s.Inv) (hl : s.allocations p.provenance = some blk) (live : s.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (bound : p.address.val ≤ blk.bptr.val + blk.repr.length) :
    Heap.modifyRange repr p 0 change s = some s := by
  have hb : p.offsetFrom blk.bptr ≤ blk.repr.length := by
    dsimp [RawPtr.offsetFrom]
    grind
  simp [Heap.modifyRange, Heap.modify, hl, live, lower, aligned, hb, Block.bytes,
    storeRepr_same s p.provenance blk hl, Heap.commit, hinv.2]

end Aeneas.Std.Heap

namespace Aeneas.Std

private theorem update_update (repr : Repr T) (bytes : Vector Cell r)
    (offset : Nat) (hb : offset + repr.size ≤ r)
    (old new : Vector Cell repr.size) :
    repr.update (repr.update bytes offset hb old) offset hb new =
      repr.update bytes offset hb new := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem?
  intro i
  by_cases inside : offset ≤ i ∧ i < offset + repr.size
  · obtain ⟨j, hj, rfl⟩ : ∃ j, j < repr.size ∧ i = offset + j :=
      ⟨i - offset, by grind, by grind⟩
    rw [Repr.update_inside _ _ _ _ _ j hj, Repr.update_inside _ _ _ _ _ j hj]
  · have outside : i < offset ∨ offset + repr.size ≤ i := by grind
    rw [Repr.update_outside _ _ _ _ _ i outside,
      Repr.update_outside _ _ _ _ _ i outside,
      Repr.update_outside _ _ _ _ _ i outside]

private theorem endBorrow_after_borrow (repr : Repr T) (p : RawPtr T)
    (s₀ s₁ : Heap) (blk : Block) (old : Vector Byte repr.size)
    (value : T) (data : Vector Byte repr.size) (encoded : repr.encode value data)
    (hsize : 0 < repr.size) (hb : p.offsetFrom blk.bptr + repr.size ≤ blk.repr.length)
    (hl : s₀.allocations p.provenance = some blk) (live : s₀.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = old.map (Cell.shared 0))
    (borrowed : Heap.borrow repr p s₀ = some s₁) :
    Heap.endBorrow repr p data s₁ = Heap.write repr p value data encoded s₀ := by
  let suspended := repr.update blk.bytes (p.offsetFrom blk.bptr) hb
    (Vector.replicate repr.size .borrowed)
  have change : repr.borrow blk.bytes (p.offsetFrom blk.bptr) = some suspended := by
    have same : old.map (fun _ => Cell.borrowed) =
        Vector.replicate repr.size Cell.borrowed := by
      apply Vector.ext
      intro i hi
      simp
    simp [Repr.borrow, hsize, hb, selected, Vector.mapM_map, Function.comp_def,
      Cell.borrow, vector_mapM_some, same, suspended]
  have commit : Heap.commit (s₀.storeRepr p.provenance suspended.toList) = some s₁ := by
    simpa [Heap.borrow, Heap.modify, hl, live, lower, aligned, change] using borrowed
  obtain ⟨state, _⟩ := Heap.commit_success _ _ commit
  subst s₁
  have hb₁ : p.offsetFrom blk.bptr + repr.size ≤ suspended.toList.length := by
    simpa using hb
  have bytes : ({ blk with repr := suspended.toList } : Block).bytes =
      suspended.cast (by simp) := by
    apply Vector.toArray_inj.mp
    simp [Block.bytes, Vector.toList, Array.toArray_toList]
  have selected₁ :
      repr.select ({ blk with repr := suspended.toList } : Block).bytes
        (p.offsetFrom blk.bptr) hb₁ = Vector.replicate repr.size .borrowed := by
    apply Vector.toList_inj.mp
    simpa only [Repr.select_toList, bytes, Vector.toList_cast] using
      congrArg Vector.toList (Repr.select_update repr blk.bytes (p.offsetFrom blk.bptr) hb
        (Vector.replicate repr.size .borrowed))
  have zipped : (Vector.replicate repr.size (Cell.borrowed : Cell)).zip data =
      data.map (fun byte => (Cell.borrowed, byte)) := by
    apply Vector.ext
    intro i hi
    simp
  have updated :
      (repr.update ({ blk with repr := suspended.toList } : Block).bytes
        (p.offsetFrom blk.bptr) hb₁ (data.map (Cell.shared 0))).toList =
      (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (data.map (Cell.shared 0))).toList := by
    simpa only [bytes, Vector.toList_cast, suspended, Repr.update_toList] using
      congrArg Vector.toList
      (update_update repr blk.bytes (p.offsetFrom blk.bptr) hb
        (Vector.replicate repr.size .borrowed) (data.map (Cell.shared 0)))
  simp [Heap.endBorrow, Heap.write, Heap.modify, hl, live, lower, aligned,
    Heap.live_storeRepr_updated, Repr.endBorrow, Repr.write, hsize, hb,
    selected, selected₁, zipped, Vector.mapM_map, Function.comp_def, Cell.endBorrow,
    vector_mapM_some, Repr.writeBytes_shared, updated, Heap.storeRepr_storeRepr]

private theorem zipIdx_vector [Inhabited α] (data : Vector α count) :
    data.toList.zipIdx = (List.range count).map (fun i => (data[i]!, i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    have bound : i < count := by simpa using hi
    simp [bound]

private theorem endBorrowRange_update (repr : Repr T)
    (data : Vector (Vector Byte repr.size) count) (bytes : Vector Cell r)
    (offset : Nat) (hb : offset + count * repr.size ≤ r)
    (selected : (repr.region count).select bytes offset hb =
      Vector.replicate (count * repr.size) .borrowed)
    (hsize : 0 < repr.size) :
    data.toList.zipIdx.foldlM (fun current (encoding, i) =>
      repr.endBorrow current (offset + i * repr.size) encoding) bytes =
      some ((repr.region count).update bytes offset hb
        (data.flatMap (fun encoding => encoding.map (Cell.shared 0)))) := by
  rw [zipIdx_vector, List.foldlM_map]
  let old : Vector (Vector Cell repr.size) count :=
    Vector.replicate count (Vector.replicate repr.size .borrowed)
  let new := data.map fun encoding => encoding.map (Cell.shared 0)
  have step : ∀ current i (hi : i < count),
      repr.select current (offset + i * repr.size) (range_element_bound hi hb) = old[i] →
      repr.endBorrow current (offset + i * repr.size) data[i]! =
        some (repr.update current (offset + i * repr.size) (range_element_bound hi hb) new[i]) := by
    intro current i hi hs
    have hz : (Vector.replicate repr.size (Cell.borrowed : Cell)).zip data[i] =
        data[i].map (fun byte => (Cell.borrowed, byte)) := by
      apply Vector.ext
      intro j hj
      simp
    simp [Repr.endBorrow, hsize, range_element_bound hi hb, hs, old, hz, new, hi,
      Vector.mapM_map, Function.comp_def, Cell.endBorrow, vector_mapM_some]
  simpa only [new, Vector.flatMap_map, Function.comp_def, id_eq] using
    repr.fold_region bytes offset count old new
      (fun current i => repr.endBorrow current (offset + i * repr.size) data[i]!) hb
      (by simpa [old, Vector.flatMap_replicate] using selected) step hsize

private theorem encodeList_length (repr : Repr T) (values : List T)
    (data : List (Vector Byte repr.size)) (encoded : repr.encodeList values data) :
    data.length = values.length := by
  induction values generalizing data
  · cases data
    · rfl
    · contradiction
  · rename_i value values ih
    cases data
    · contradiction
    · rename_i bytes data
      exact congrArg Nat.succ (ih data encoded.2)

private theorem encodeList_get (repr : Repr T) (values : List T)
    (data : List (Vector Byte repr.size)) (encoded : repr.encodeList values data)
    (i : Nat) (hv : i < values.length) (hd : i < data.length) :
    repr.encode values[i] data[i] := by
  induction values generalizing data i
  · simp at hv
  · rename_i value values ih
    cases data
    · contradiction
    · rename_i bytes data
      cases i
      · exact encoded.1
      · rename_i i
        exact ih data encoded.2 i (by simpa using hv) (by simpa using hd)

end Aeneas.Std

namespace Aeneas.Std.SepLogic

/-- Every successful encoding return preserves the frame. This is preservation,
not an enabledness theorem from borrowed cells alone. -/
theorem endBorrowRange_encoding.post (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (data : Vector (Vector Byte repr.size) count)
    (encoded : ∀ i : Fin count, repr.encode values[i.val] data[i.val])
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (h F : Fragment) (s next : Heap)
    (hp : block repr p bptr (List.replicate (count * repr.size) .borrowed) h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s (h ∪ F)) (hinv : s.Inv)
    (run : Heap.endBorrowRange repr p data.toList s = some next) :
    ∃ h', h'.Disjoint F ∧ Fragment.Matches next (h' ∪ F) ∧ next.Inv ∧
      pointsToRange repr p bptr values 0 h' := by
  obtain ⟨lower, aligned, rfl⟩ := hp
  let old := Vector.replicate (count * repr.size) (Cell.borrowed : Cell)
  let new := data.flatMap (fun encoding => encoding.map (Cell.shared 0))
  have matched : Fragment.Matches s
      (cellsHeap bptr p.provenance (p.offsetFrom bptr) old.toList) := by
    simpa [old] using ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨blk, hb, hl, live, hbase, selected⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit) (data := old)
      (Nat.mul_pos hcount hsize) matched
  subst bptr
  change p.offsetFrom blk.bptr + count * repr.size ≤ blk.repr.length at hb
  change s.allocations p.provenance = some blk at hl
  change (repr.region count).select blk.bytes (p.offsetFrom blk.bptr) hb = old at selected
  let change := fun {r} (bytes : Vector Cell r) offset =>
    if (count = 0 ∨ 0 < repr.size) && offset + count * repr.size ≤ bytes.size then
      data.toList.zipIdx.foldlM (fun current (encoding, i) =>
        repr.endBorrow current (offset + i * repr.size) encoding) bytes
    else none
  have hc : change blk.bytes (p.offsetFrom blk.bptr) =
      some ((repr.region count).update blk.bytes (p.offsetFrom blk.bptr) hb new) := by
    simp only [change, hsize, or_true, decide_true, Bool.true_and, Vector.size, hb, ↓reduceIte]
    exact endBorrowRange_update repr data blk.bytes _ hb selected hsize
  have commit : Heap.commit
      (s.storeRepr p.provenance ((repr.region count).update blk.bytes
        (p.offsetFrom blk.bptr) hb new).toList) = some next := by
    simp [Heap.endBorrowRange, Heap.modify, hl, live, lower, aligned, hsize, hb] at run
    rw [endBorrowRange_update repr data blk.bytes _ hb selected hsize] at run
    simpa only [new, bind, Option.bind_some] using run
  obtain ⟨he, valid⟩ := Heap.commit_success _ _ commit
  have valid' : (s.storeRepr p.provenance ((repr.region count).update blk.bytes
      (p.offsetFrom blk.bptr) hb new).toList).check = true := he ▸ valid
  have ht := modify.spec (repr.region count) (p.cast Unit) s blk old new
    change hb hl live aligned hc valid'
  have run' : Heap.modify (repr.region count) (p.cast Unit) change s = some next := by
    change Heap.modify repr p change s = some next
    simpa [Heap.modify, hl, live, lower, aligned, hc] using commit
  obtain ⟨h', hd', hm', hi', hp'⟩ :=
    (ht _ F ⟨lower, aligned, rfl⟩ hd hm hinv).2 () next run'
  exact ⟨h', hd', hm', hi', data, encoded, hp'⟩

end Aeneas.Std.SepLogic

namespace Aeneas.Std.HeapWP

open SepLogic

/-- The forward conversion supplies the matching backward computation, with
return enabledness proved from the original exclusive footprint. The callback
contract applies at the returned state: intervening heap effects require their
own scope-preservation argument, not borrowed-cell ownership alone. -/
theorem borrowWithBack.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (initial : T) (hsize : 0 < repr.size)
    (h F : Fragment) (s₀ : Heap) (hp : pointsTo repr p bptr initial 0 h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s₀ (h ∪ F)) (hinv : s₀.Inv) :
    Spec (RawPtr.borrowWithBack repr p)
      (fun (value, back) s₁ => value = initial ∧
        (∃ h₁, h₁.Disjoint F ∧ Fragment.Matches s₁ (h₁ ∪ F) ∧ s₁.Inv ∧
          block repr p bptr (List.replicate repr.size .borrowed) h₁) ∧
        ∀ updated, (∀ q, ¬ repr.Carries updated q) →
          Spec (back updated)
            (fun _ s₂ => ∃ h₂, h₂.Disjoint F ∧ Fragment.Matches s₂ (h₂ ∪ F) ∧
              s₂.Inv ∧ pointsTo repr p bptr updated 0 h₂) s₁) s₀ := by
  have forward := borrowRange_single.spec repr p bptr initial hsize h F s₀ hp hd hm hinv
  obtain ⟨enabled, post⟩ := Spec.checkedModify.mp forward
  obtain ⟨old, encoded, lower, aligned, he⟩ := hp
  have localMatch : Fragment.Matches s₀
      (cellsHeap bptr p.provenance (p.offsetFrom bptr) (old.map (Cell.shared 0)).toList) := by
    rw [he] at hm
    exact ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨blk, hb, hl, live, base, selected⟩ := bytes_of_matches hsize localMatch
  subst bptr
  have borrowing : Spec (RawPtr.borrow repr p)
      (fun value s₁ => value = initial ∧ Heap.borrow repr p s₀ = some s₁ ∧
        ∃ h₁, h₁.Disjoint F ∧ Fragment.Matches s₁ (h₁ ∪ F) ∧ s₁.Inv ∧
          block repr p blk.bptr (List.replicate repr.size .borrowed) h₁) s₀ := by
    unfold RawPtr.borrow
    have transfer : Spec (RawPtr.borrowRange repr p 1)
        (fun values s₁ => State.borrowRange repr p 1 s₀ values s₁ ∧
          ∃ h₁, h₁.Disjoint F ∧ Fragment.Matches s₁ (h₁ ∪ F) ∧ s₁.Inv ∧
            values = [initial] ∧
              block repr p blk.bptr (Vector.replicate repr.size .borrowed).toList h₁) s₀ :=
      Spec.checkedModify.mpr ⟨enabled, fun values s₁ run => ⟨run, post values s₁ run⟩⟩
    apply Spec.bind transfer
    rintro values s₁ ⟨⟨_, _, borrowed⟩, h₁, hd₁, hm₁, hi₁, rfl, hp₁⟩
    apply Spec.pure _ _ _ |>.mpr
    exact ⟨rfl, by simpa only [Heap.borrowRange_single] using borrowed,
      h₁, hd₁, hm₁, hi₁, hp₁⟩
  unfold RawPtr.borrowWithBack
  apply Spec.bind borrowing
  rintro value s₁ ⟨value_eq, borrowed, h₁, hd₁, hm₁, hi₁, hp₁⟩
  subst value
  apply Spec.pure _ _ _ |>.mpr
  refine ⟨rfl, ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩, ?_⟩
  intro updated noPointers
  have write := SepLogic.write_pointsTo.spec repr p blk.bptr initial updated noPointers hsize
    h F s₀ ⟨old, encoded, lower, aligned, he⟩ hd hm hinv
  have restore : ∀ data (encoded : repr.encode updated data),
      Heap.endBorrow repr p data s₁ = Heap.write repr p updated data encoded s₀ :=
    fun data encoded => endBorrow_after_borrow repr p s₀ s₁ blk old updated data encoded
      hsize hb hl live lower aligned selected borrowed
  apply Spec.checkedModify.mpr
  constructor
  · obtain ⟨_, s₂, data, encoded, run⟩ := write.1
    exact ⟨(), s₂, [data], ⟨encoded, trivial⟩, by
      simpa only [Heap.endBorrowRange_single, restore data encoded] using run⟩
  · rintro _ s₂ ⟨data, encoded, run⟩
    cases data
    · simp [Repr.encodeList] at encoded
    · rename_i bytes tail
      cases tail
      · exact write.2 () s₂ ⟨bytes, encoded.1, by
          simpa only [Heap.endBorrowRange_single, restore bytes encoded.1] using run⟩
      · simp [Repr.encodeList] at encoded

/-- Pure safe code can update a borrowed value and call its backward function
without exposing any global invariant or overlap obligation to the client. -/
theorem withBorrow.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (initial : T) (update : T → T)
    (noPointers : ∀ q, ¬ repr.Carries (update initial) q) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr initial) (RawPtr.withBorrow repr p update)
      (fun value h => value = initial ∧ pointsTo repr p bptr (update initial) 0 h) := by
  intro h F s₀ hp hd hm hinv
  unfold RawPtr.withBorrow
  apply Spec.bind (borrowWithBack.spec repr p bptr initial hsize h F s₀ hp hd hm hinv)
  rintro ⟨value, back⟩ s₁ ⟨value_eq, _, returns⟩
  subst value
  apply Spec.bind (returns (update initial) noPointers)
  rintro _ s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
  exact Spec.pure _ _ _ |>.mpr ⟨h₂, hd₂, hm₂, hi₂, rfl, hp₂⟩

/-- State-specific boundary for a matching return protocol. One compatible
encoding enables the operation; the postcondition covers all permitted encodings.
Deriving this premise from a backward-function resource remains separate work. -/
theorem endBorrowRange.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (s : Heap) (hcount : 0 < count) (hsize : 0 < repr.size)
    (enabled : ∃ next, State.endBorrowRange repr p values.toList s () next) :
    TripleAt (block repr p bptr (List.replicate (count * repr.size) .borrowed))
      (RawPtr.endBorrowRange repr p values.toList)
      (fun _ => pointsToRange repr p bptr values) s := by
  apply TripleAt.checkedModify
  intro h F hp hd hm hinv
  obtain ⟨next, hn⟩ := enabled
  refine ⟨⟨(), next, hn⟩, ?_⟩
  rintro _ next ⟨encodings, encoded, run⟩
  have hlen : encodings.length = count := by
    simpa using encodeList_length repr values.toList encodings encoded
  let data : Vector (Vector Byte repr.size) count := ⟨encodings.toArray, by simp [hlen]⟩
  have hlist : data.toList = encodings := by simp [data]
  have each : ∀ i : Fin count, repr.encode values[i.val] data[i.val] := by
    intro i
    have hi : i.val < encodings.length := by simp [hlen]
    simpa [data] using encodeList_get repr values.toList encodings encoded i.val
      (by simp) hi
  exact SepLogic.endBorrowRange_encoding.post repr p bptr values data each hcount hsize
    h F s next hp hd hm hinv (by simpa only [hlist] using run)

theorem emptyRange_transfer.spec (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (hinv : s.Inv) (hl : s.allocations p.provenance = some blk) (live : s.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (bound : p.address.val ≤ blk.bptr.val + blk.repr.length) :
    Spec (Result.checkedModify (fun s result s' =>
      Heap.readRange repr p 0 s = some result ∧ Heap.modifyRange repr p 0 change s = some s'))
      (fun result s' => result = [] ∧ s' = s) s := by
  have hr : Heap.readRange repr p 0 s = some [] := by
    simp [Heap.readRange, hl, live, lower, aligned, bound]
  have hc := Heap.modifyRange_empty repr p s blk change hinv hl live lower aligned bound
  apply Spec.checkedModify.mpr
  refine ⟨⟨[], s, hr, hc⟩, ?_⟩
  rintro result s' ⟨he, he'⟩
  exact ⟨Option.some.inj (he.symm.trans hr), Option.some.inj (he'.symm.trans hc)⟩

/-- Empty transfers require a live aligned view and an in-bounds position.
They neither restore permissions nor change the heap. -/
theorem emptyRanges.spec (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (hinv : s.Inv) (hl : s.allocations p.provenance = some blk) (live : s.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (bound : p.address.val ≤ blk.bptr.val + blk.repr.length) :
    Spec (RawPtr.borrowRange repr p 0) (fun result s' => result = [] ∧ s' = s) s ∧
    Spec (RawPtr.shareRange repr p 0) (fun result s' => result = [] ∧ s' = s) s ∧
    Spec (RawPtr.endShareRange repr p []) (fun _ s' => s' = s) s ∧
    Spec (RawPtr.endBorrowRange repr p []) (fun _ s' => s' = s) s := by
  have hr : Heap.readRange repr p 0 s = some [] := by
    simp [Heap.readRange, hl, live, lower, aligned, bound]
  have hc : ∀ change, Heap.modifyRange repr p 0 change s = some s :=
    fun change => Heap.modifyRange_empty repr p s blk change hinv hl live lower aligned bound
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Spec.checkedModify.mpr
    have mutable : State.mutableValues repr p [] s := ⟨blk, hl, by simp⟩
    refine ⟨⟨[], s, hr, mutable, hc _⟩, ?_⟩
    rintro result next ⟨read, _, run⟩
    exact ⟨Option.some.inj (read.symm.trans hr), Option.some.inj (run.symm.trans (hc _))⟩
  · exact emptyRange_transfer.spec repr p s blk _ hinv hl live lower aligned bound
  · apply Spec.checkedModify.mpr
    refine ⟨⟨(), s, hr, hc _⟩, ?_⟩
    rintro _ next ⟨_, run⟩
    exact Option.some.inj (run.symm.trans (hc _))
  · apply Spec.checkedModify.mpr
    have run : Heap.endBorrowRange repr p [] s = some s := by
      simpa [Heap.endBorrowRange, Heap.modifyRange] using hc (fun bytes _ => some bytes)
    refine ⟨⟨(), s, [], trivial, run⟩, ?_⟩
    rintro _ next ⟨data, encoded, run'⟩
    have empty : data = [] := by
      cases data
      · rfl
      · simp [Repr.encodeList] at encoded
    subst data
    exact Option.some.inj (run'.symm.trans run)

end Aeneas.Std.HeapWP
