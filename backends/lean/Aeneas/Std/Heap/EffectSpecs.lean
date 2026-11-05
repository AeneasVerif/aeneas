module

public import Aeneas.Std.Heap.Effects
public import Aeneas.Std.Heap.Borrowing
public import Aeneas.Std.Heap.PointerMovement
public import Aeneas.Std.Alloc.Boxed
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Alloc.Boxed

/-! Contracts for actual checked Rust effects, with arbitrary indexed frames and
all permitted successors. Ordinary access derives enabledness from resources.
Allocation accepts OOM if compatible placement is unavailable. Low-level
restoration is state-specific; scoped rules derive it from return authority. -/

@[expose] public section

namespace Aeneas.Std.HeapWP

open SepLogic

theorem read.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (value : T)
    (depth : Nat) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr value depth) (RawPtr.read repr p)
      (fun x h => x = value ∧ pointsTo repr p bptr value depth h) :=
  Triple.checkedModify (SepLogic.read.spec repr p bptr value depth hsize)

theorem read_exposed.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (value : T)
    (depth : Nat) (hsize : 0 < repr.size) :
    Triple (readable repr p bptr value depth) (RawPtr.read repr p)
      (fun x h => x = value ∧ readable repr p bptr value depth h) := by
  apply Triple.checkedModify
  intro h F s hp hd hm hi
  have hr := read_of_readable hsize hp ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨value, s, hr, rfl⟩, ?_⟩
  rintro x s' ⟨hx, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hx.symm.trans hr), hp⟩

theorem write.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (old value : T)
    (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr old) (MutRawPtr.write repr p value)
      (fun _ => pointsTo repr p bptr value) :=
  Triple.checkedModify (SepLogic.write_pointsTo.spec repr p bptr old value noPointers hsize)

theorem write_readable.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old value : T) (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    Triple (readable repr p bptr old) (MutRawPtr.write repr p value)
      (fun _ => pointsTo repr p bptr value) :=
  Triple.checkedModify (SepLogic.write_readable.spec repr p bptr old value noPointers hsize)

theorem write_supported.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old value : T) (R : Assertion)
    (support : ∀ h, R h → SupportsValue repr value h) (hsize : 0 < repr.size) :
    Triple (sep (pointsTo repr p bptr old) R) (MutRawPtr.write repr p value)
      (fun _ => sep (pointsTo repr p bptr value) R) :=
  Triple.checkedModify
    (SepLogic.write_pointsTo_supported.spec repr p bptr old value R support hsize)

theorem write_local.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old value : T) (R : Assertion)
    (support : ∀ h, sep (pointsTo repr p bptr old) R h → SupportsValue repr value h)
    (hsize : 0 < repr.size) :
    Triple (sep (pointsTo repr p bptr old) R) (MutRawPtr.write repr p value)
      (fun _ => sep (pointsTo repr p bptr value) R) :=
  Triple.checkedModify
    (SepLogic.write_pointsTo_local.spec repr p bptr old value R support hsize)

theorem readRange_single.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (depth : Nat) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr value depth) (RawPtr.readRange repr p 1)
      (fun values h => values = [value] ∧ pointsTo repr p bptr value depth h) := by
  apply Triple.checkedModify
  intro h F s hp hd hm hi
  have hr : Heap.readRange repr p 1 s = some [value] := by
    rw [Heap.readRange_single, read_of_pointsTo hsize hp
      ((Fragment.matches_union _ _ _).mp hm).1]
    rfl
  refine ⟨⟨[value], s, hr, rfl⟩, ?_⟩
  rintro values s' ⟨hv, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hv.symm.trans hr), hp⟩

private theorem mutable_single {repr : Repr T} {p : RawPtr T} {bptr : BasePtr}
    {value : T} {h : Fragment} {s : Heap} (hsize : 0 < repr.size)
    (hp : pointsTo repr p bptr value 0 h) (hm : Fragment.Matches s h) :
    State.mutableValues repr p [value] s := by
  obtain ⟨data, encoded, _, _, rfl⟩ := hp
  obtain ⟨blk, hb, hl, _, hbase, selected⟩ := bytes_of_matches hsize hm
  subst bptr
  refine ⟨blk, hl, ?_⟩
  intro i hi
  have he : i = 0 := by simp only [List.length_singleton] at hi; agrind
  subst i
  exact ⟨data, by simpa using hb,
    by simpa using selected ▸ Repr.readBytes_shared data 0, encoded⟩

theorem borrowRange_single.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr value) (RawPtr.borrowRange repr p 1)
      (fun values h => values = [value] ∧
        block repr p bptr (Vector.replicate repr.size .borrowed).toList h) := by
  apply Triple.checkedModify
  intro h F s hp hd hm hi
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have hr : Heap.readRange repr p 1 s = some [value] := by
    rw [Heap.readRange_single, read_of_pointsTo hsize hp localMatch]
    rfl
  have mutable := mutable_single hsize hp localMatch
  obtain ⟨⟨_, s', hb⟩, post⟩ :=
    SepLogic.borrow_pointsTo.spec repr p bptr value hsize h F s hp hd hm hi
  refine ⟨⟨[value], s', hr, mutable, by simpa [Heap.borrowRange_single] using hb⟩, ?_⟩
  rintro values s' ⟨hv, _, hb⟩
  obtain ⟨h', hd', hm', hi', hq⟩ := post () s' (by simpa [Heap.borrowRange_single] using hb)
  exact ⟨h', hd', hm', hi', Option.some.inj (hv.symm.trans hr), hq⟩

theorem borrow.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (value : T)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr value) (RawPtr.borrow repr p)
      (fun result h => result = value ∧
        block repr p bptr (Vector.replicate repr.size .borrowed).toList h) := by
  unfold RawPtr.borrow
  apply Triple.bind (borrowRange_single.spec repr p bptr value hsize)
  intro values
  apply Triple.pure_pre
  intro hv
  subst values
  exact Triple.pure _ value

private theorem read_transfer_single.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (depth : Nat) (change : Heap → Option Heap) (Q : Assertion)
    (hsize : 0 < repr.size)
    (ht : SepLogic.Triple (pointsTo repr p bptr value depth)
      (fun s (_ : Unit) s' => change s = some s') (fun _ => Q)) :
    SepLogic.Triple (pointsTo repr p bptr value depth)
      (fun s values s' => Heap.readRange repr p 1 s = some values ∧ change s = some s')
      (fun values h => values = [value] ∧ Q h) := by
  intro h F s hp hd hm hi
  have hr : Heap.readRange repr p 1 s = some [value] := by
    rw [Heap.readRange_single, read_of_pointsTo hsize hp ((Fragment.matches_union _ _ _).mp hm).1]
    rfl
  obtain ⟨⟨_, s', hc⟩, post⟩ := ht h F s hp hd hm hi
  refine ⟨⟨[value], s', hr, hc⟩, ?_⟩
  rintro values s' ⟨hv, hc⟩
  obtain ⟨h', hd', hm', hi', hq⟩ := post () s' hc
  exact ⟨h', hd', hm', hi', Option.some.inj (hv.symm.trans hr), hq⟩

theorem shareRange_single.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (depth : Nat) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr value depth) (RawPtr.shareRange repr p 1)
      (fun values h => values = [value] ∧ pointsTo repr p bptr value (depth + 1) h) := by
  apply Triple.checkedModify
  unfold State.shareRange
  simp only [Heap.shareRange_single]
  exact read_transfer_single.spec repr p bptr value depth (Heap.share repr p) _ hsize
    (SepLogic.share_pointsTo.spec repr p bptr value depth hsize)

private theorem modify_post (repr : Repr T) (p : RawPtr T) (s s' : Heap) (blk : Block)
    (old new : Vector Cell repr.size)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (hb : p.offsetFrom blk.bptr + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (hc : change blk.bytes (p.offsetFrom blk.bptr) =
      some (repr.update blk.bytes (p.offsetFrom blk.bptr) hb new))
    (h F : Fragment) (hp : block repr p blk.bptr old.toList h) (hd : h.Disjoint F)
    (hm : Fragment.Matches s (h ∪ F)) (hinv : s.Inv)
    (hrun : Heap.modify repr p change s = some s') :
    ∃ h', h'.Disjoint F ∧ Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧
      block repr p blk.bptr new.toList h' := by
  have commit : Heap.commit
      (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hb new).toList) =
      some s' := by
    simpa [Heap.modify, hl, hlive, hp.1, ha, hc] using hrun
  obtain ⟨he, valid⟩ := Heap.commit_success _ _ commit
  have valid' : (s.storeRepr p.provenance
      (repr.update blk.bytes (p.offsetFrom blk.bptr) hb new).toList).check = true :=
    he ▸ valid
  exact (SepLogic.modify.spec repr p s blk old new change hb hl hlive ha hc valid'
    h F hp hd hm hinv).2 () s' hrun

/-- Low-level decrement contract. Enabledness must come from the matching return
protocol; borrowed/positive-depth ownership alone cannot exclude alias readers. -/
theorem endShareRange_single.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (depth : Nat) (s : Heap) (hsize : 0 < repr.size)
    (enabled : ∃ s', Heap.endShare repr p s = some s') :
    TripleAt (pointsTo repr p bptr value (depth + 1))
      (RawPtr.endShareRange repr p [value]) (fun _ => pointsTo repr p bptr value depth) s := by
  apply TripleAt.checkedModify
  intro h F hp hd hm hinv
  have hr : Heap.readRange repr p 1 s = some [value] := by
    rw [Heap.readRange_single, read_of_pointsTo hsize hp ((Fragment.matches_union _ _ _).mp hm).1]
    rfl
  obtain ⟨next, hn⟩ := enabled
  refine ⟨⟨(), next, hr, by simpa [Heap.endShareRange_single] using hn⟩, ?_⟩
  rintro _ next ⟨_, hn⟩
  obtain ⟨data, encoded, hlo, ha, rfl⟩ := hp
  obtain ⟨blk, hb, hl, hlive, hbase, selected⟩ :=
    bytes_of_matches hsize ((Fragment.matches_union _ _ _).mp hm).1
  subst bptr
  have hc : repr.endShare blk.bytes (p.offsetFrom blk.bptr) =
      some (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (data.map (Cell.shared depth))) := by
    simp [Repr.endShare, hsize, hb, selected, Vector.mapM_map, Function.comp_def,
      Cell.endShare, vector_mapM_some]
  obtain ⟨h', hd', hm', hi', hp'⟩ := modify_post repr p s next blk _ _
    (fun bytes i => repr.endShare bytes i) hb hl hlive ha hc _ F ⟨hlo, ha, rfl⟩ hd hm hinv
    (by simpa [Heap.endShareRange_single, Heap.endShare] using hn)
  exact ⟨h', hd', hm', hi', data, encoded, hp'⟩

private theorem encode_single (repr : Repr T) (value : T)
    (data : List (Vector Byte repr.size)) (h : repr.encodeList [value] data) :
    ∃ bytes, data = [bytes] ∧ repr.encode value bytes := by
  cases data
  · contradiction
  · rename_i bytes tail
    cases tail
    · exact ⟨bytes, rfl, h.1⟩
    · simp [Repr.encodeList] at h

/-- This explicitly requires an enabled return at the input state, not just
borrowed cells. It preserves all frames and covers every permitted encoding. -/
theorem endBorrowRange_single.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (s : Heap) (hsize : 0 < repr.size)
    (enabled : ∃ s', State.endBorrowRange repr p [value] s () s') :
    TripleAt (block repr p bptr (Vector.replicate repr.size .borrowed).toList)
      (RawPtr.endBorrowRange repr p [value]) (fun _ => pointsTo repr p bptr value) s := by
  apply TripleAt.checkedModify
  intro h F hp hd hm hinv
  obtain ⟨next, hn⟩ := enabled
  refine ⟨⟨(), next, hn⟩, ?_⟩
  rintro _ next ⟨data, encoded, hn⟩
  obtain ⟨bytes, hdata, hencoded⟩ := encode_single repr value data encoded
  subst data
  obtain ⟨hlo, ha, rfl⟩ := hp
  obtain ⟨blk, hb, hl, hlive, hbase, selected⟩ :=
    bytes_of_matches hsize ((Fragment.matches_union _ _ _).mp hm).1
  subst bptr
  have hz : (Vector.replicate repr.size (Cell.borrowed : Cell)).zip bytes =
      bytes.map (fun byte => (Cell.borrowed, byte)) := by
    apply Vector.ext
    intro i hi
    simp
  have hc : repr.endBorrow blk.bytes (p.offsetFrom blk.bptr) bytes =
      some (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (bytes.map (Cell.shared 0))) := by
    simp [Repr.endBorrow, hsize, hb, selected, hz, Vector.mapM_map, Function.comp_def,
      Cell.endBorrow, vector_mapM_some]
  obtain ⟨h', hd', hm', hi', hp'⟩ := modify_post repr p s next blk _ _
    (fun data i => repr.endBorrow data i bytes) hb hl hlive ha hc _ F ⟨hlo, ha, rfl⟩ hd hm hinv
    (by simpa [Heap.endBorrowRange_single, Heap.endBorrow] using hn)
  exact ⟨h', hd', hm', hi', bytes, hencoded, hp'⟩

theorem endBorrow.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (s : Heap) (hsize : 0 < repr.size)
    (enabled : ∃ s', State.endBorrowRange repr p [value] s () s') :
    TripleAt (block repr p bptr (Vector.replicate repr.size .borrowed).toList)
      (RawPtr.endBorrow repr p value) (fun _ => pointsTo repr p bptr value) s :=
  endBorrowRange_single.spec repr p bptr value s hsize enabled

private theorem offset_eq_byteOffset (repr : Repr T) (p : RawPtr T) (count : Int)
    (s : Heap) :
    Heap.offset repr p count s = Heap.byteOffset p (count * repr.size) s := by
  unfold Heap.byteOffset
  dsimp only [RawPtr.cast]
  unfold Heap.offset
  cases hl : s.allocations p.provenance
  · rfl
  · rename_i blk
    simp only [Repr.byteStride, Nat.cast_one, mul_one]
    change (if _ then some _ else none) =
      Option.map _ (if _ then some _ else none)
    split
    · rfl
    · rfl

theorem offset.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (count : Isize) (length : Nat) (own : Bool)
    (hstart : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * repr.size)
    (hlo : (bptr.val : Int) ≤ (p.address.val : Int) + count.val * repr.size)
    (hhi : (p.address.val : Int) + count.val * repr.size ≤ bptr.val + length * repr.size)
    (hfit : (p.address.val : Int) + count.val * repr.size < (2 ^ UScalarTy.numBits .Usize : Nat)) :
    Triple (alloc repr ⟨p.provenance, bptr⟩ bptr length own) (RawPtr.offset repr p count)
      (fun q h => q.provenance = p.provenance ∧
        (q.address.val : Int) = (p.address.val : Int) + count.val * repr.size ∧
        alloc repr ⟨p.provenance, bptr⟩ bptr length own h) := by
  apply Triple.checkedModify
  have ht := SepLogic.byteOffset.spec repr p bptr (count.val * repr.size)
    length own hstart hlo hhi hfit
  change SepLogic.Triple _ (fun s q s' =>
    Heap.offset repr p count.val s = some q ∧ s' = s) _
  simpa only [offset_eq_byteOffset] using ht

theorem add.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (count : Usize) (length : Nat) (own : Bool)
    (hstart : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * repr.size)
    (hhi : p.address.val + count.val * repr.size ≤ bptr.val + length * repr.size)
    (hfit : p.address.val + count.val * repr.size < 2 ^ UScalarTy.numBits .Usize) :
    Triple (alloc repr ⟨p.provenance, bptr⟩ bptr length own) (RawPtr.add repr p count)
      (fun q h => q.provenance = p.provenance ∧
        q.address.val = p.address.val + count.val * repr.size ∧
        alloc repr ⟨p.provenance, bptr⟩ bptr length own h) := by
  have hlo : (bptr.val : Int) ≤ (p.address.val : Int) + count.val * repr.size := by agrind
  have hhi' : (p.address.val : Int) + count.val * repr.size ≤ bptr.val + length * repr.size := by
    exact_mod_cast hhi
  have hfit' : (p.address.val : Int) + count.val * repr.size <
      (2 ^ UScalarTy.numBits .Usize : Nat) := by exact_mod_cast hfit
  have ht := SepLogic.byteOffset.spec repr p bptr ((count.val : Int) * repr.size)
    length own hstart hlo hhi' hfit'
  have lifted : Triple (alloc repr ⟨p.provenance, bptr⟩ bptr length own) (RawPtr.add repr p count)
      (fun q h => q.provenance = p.provenance ∧
        (q.address.val : Int) = (p.address.val : Int) + count.val * repr.size ∧
        alloc repr ⟨p.provenance, bptr⟩ bptr length own h) := by
    apply Triple.checkedModify
    change SepLogic.Triple _ (fun s q s' =>
      Heap.offset repr p count.val s = some q ∧ s' = s) _
    simpa only [offset_eq_byteOffset] using ht
  apply Triple.conseq (fun _ hp => hp) ?_ lifted
  intro q h hp
  exact ⟨hp.1, by exact_mod_cast hp.2.1, hp.2.2⟩

/-- Allocation is demonic over compatible placement and representation together.
Exposure promises decodability, not an admissible scalar encoding of pointer lanes. -/
theorem newBlock.spec (repr : Repr T) (value : T) (own : Bool) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F) :
    Spec (RawPtr.newBlock repr [value] own)
      (fun p s' => s'.next = s.next + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p p.address 1 own)
            (if own then pointsTo repr p p.address value else readable repr p p.address value) h) s := by
  apply Spec.allocatingModify.mpr
  rintro p s' ⟨data, bptr, root, encoded, hn⟩
  have single : ∃ bytes, data = [bytes] ∧
      (if own then repr.encode value bytes else State.exposes repr s bptr.val value bytes) := by
    cases data
    · cases own
      · contradiction
      · contradiction
    · rename_i bytes tail
      cases tail
      · refine ⟨bytes, rfl, ?_⟩
        cases own
        · exact encoded.1
        · exact encoded.1
      · cases own
        · simp [State.exposesList] at encoded
        · simp [Repr.encodeList] at encoded
  obtain ⟨bytes, rfl, hbytes⟩ := single
  obtain ⟨hnext, h, hd, hm', hi', a, b, hab, hh, ha, hb⟩ :=
    newBlock_single.resources repr bytes own bptr root hi hm hn
  refine ⟨hnext, h, hd, hm', hi', a, b, hab, hh, ha, ?_⟩
  cases own
  · exact ⟨bytes, hbytes.1, hb⟩
  · exact ⟨bytes, hbytes, hb⟩

theorem intoRaw.spec (repr : Repr T) (value : T) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F) :
    Spec (alloc.boxed.Box.into_raw repr value)
      (fun p s' => s'.next = s.next + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p p.address 1 true) (pointsTo repr p p.address value) h) s :=
  newBlock.spec repr value true s F hi hm

/-- Owned conversion supplies lexical return authority as well as its bytes. -/
theorem intoRaw_return.spec (repr : Repr T) (value : T) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F) :
    Spec (alloc.boxed.Box.into_raw repr value)
      (fun p s' => RootReturn s' p.provenance ∧ s'.next = s.next + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p p.address 1 true) (pointsTo repr p p.address value) h) s := by
  have ordinary := Spec.allocatingModify.mp (intoRaw.spec repr value s F hi hm)
  apply Spec.allocatingModify.mpr
  intro p s' run
  obtain ⟨data, bptr, root, encoded, allocated⟩ := run
  exact ⟨owned_newBlock_root hi allocated,
    ordinary p s' ⟨data, bptr, root, encoded, allocated⟩⟩

/-- Allocating another owner preserves the return authority of existing live views. -/
theorem intoRaw_preserving.spec (repr : Repr T) (value : T) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F) :
    Spec (alloc.boxed.Box.into_raw repr value)
      (fun p s' =>
        (∀ base actual, s.allocations base = some actual → actual.active = true →
          RootReturn s base → RootReturn s' base) ∧
        RootReturn s' p.provenance ∧ s'.next = s.next + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p p.address 1 true) (pointsTo repr p p.address value) h) s := by
  have ordinary := Spec.allocatingModify.mp (intoRaw_return.spec repr value s F hi hm)
  apply Spec.allocatingModify.mpr
  intro p s' run
  obtain ⟨data, bptr, root, encoded, allocated⟩ := run
  exact ⟨fun _ _ old active authority => authority.newOwned hi old active allocated,
    ordinary p s' ⟨data, bptr, root, encoded, allocated⟩⟩

theorem allocExposure.spec (repr : Repr T) (value : T) (s : Heap) (F : Fragment)
    (hi : s.Inv) (hm : Fragment.Matches s F) :
    Spec (RawPtr.allocExposure repr [value])
      (fun p s' => s'.next = s.next + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p p.address 1 false) (readable repr p p.address value) h) s :=
  newBlock.spec repr value false s F hi hm

/-- A static descriptor calibration recovers an admissible representation from
exclusive exposure. The alias exclusion argument stays inside the library. -/
theorem allocExposure_encoded.spec (repr : Repr T) (value : T)
    (calibrated : ∀ bytes, repr.decode bytes = some value →
      (∀ i : Fin repr.size, ∀ q lane, bytes[i.val] = .pointer q lane → repr.Carries value q) →
      repr.encode value bytes)
    (s : Heap) (F : Fragment) (hi : s.Inv) (hm : Fragment.Matches s F) :
    Spec (RawPtr.allocExposure repr [value])
      (fun p s' => s'.next = s.next + 1 ∧
        ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧
          sep (alloc repr p p.address 1 false) (pointsTo repr p p.address value) h) s := by
  apply Spec.allocatingModify.mpr
  rintro p s' ⟨data, bptr, root, exposed, created⟩
  cases data
  · contradiction
  · rename_i bytes tail
    cases tail
    · have encoded := calibrated bytes exposed.1.1
        (Heap.newBlock_exposure_carries repr value bytes bptr root hi exposed.1 created)
      obtain ⟨next, h, hd, hm', hi', a, b, hab, hh, ha, hb⟩ :=
        newBlock_single.resources repr bytes false bptr root hi hm created
      exact ⟨next, h, hd, hm', hi', a, b, hab, hh, ha, bytes, encoded, hb⟩
    · simp [State.exposesList] at exposed

/-- Return to implicit safe memory, not physical deallocation. Only the owned
case needs additional root authority; nonowning baseline retirement is uniform. -/
theorem read_free.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (own : Bool) (s : Heap) (hsize : 0 < repr.size)
    (authority : own = true → RootReturn s p.provenance) :
    TripleAt (sep (alloc repr p bptr 1 own) (readable repr p bptr value))
      (do let value ← RawPtr.read repr p
          Result.checkedModify (fun s (_ : Unit) s' =>
            (if own then Heap.returnOwned repr p 1 s else Heap.endExposureAt repr p 1 0 s) = some s')
          pure value)
      (fun x h => x = value ∧ empty h) s := by
  intro h F hp hd hm hinv
  obtain ⟨a, b, hab, hh, ha, hv⟩ := hp
  have readableMatch : Fragment.Matches s b := by
    rw [hh, Fragment.matches_union] at hm
    exact ((Fragment.matches_union _ _ _).mp hm.1).2
  have hr := read_of_readable hsize hv readableMatch
  have readSpec : Spec (RawPtr.read repr p) (fun x s' => x = value ∧ s' = s) s := by
    apply Spec.checkedModify.mpr
    refine ⟨⟨value, s, hr, rfl⟩, ?_⟩
    rintro x s' ⟨hx, rfl⟩
    exact ⟨Option.some.inj (hx.symm.trans hr), rfl⟩
  apply Spec.bind readSpec
  rintro x state ⟨hx, hs⟩
  subst x
  subst state
  apply Spec.bind (TripleAt.checkedModify
    (SepLogic.returnView.spec repr p bptr value own s hsize authority) h F
      ⟨a, b, hab, hh, ha, hv⟩ hd hm hinv)
  rintro _ s' ⟨h', hd', hm', hi', hemp⟩
  exact (Spec.pure _ _ _).mpr ⟨h', hd', hm', hi', rfl, hemp⟩

theorem fromRaw.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (s : Heap) (hsize : 0 < repr.size) (authority : RootReturn s p.provenance) :
    TripleAt (sep (alloc repr p bptr 1 true) (pointsTo repr p bptr value))
      (alloc.boxed.Box.from_raw repr p) (fun x h => x = value ∧ empty h) s := by
  intro h F hp hd hm hinv
  obtain ⟨a, b, hab, hh, ha, hb⟩ := hp
  exact read_free.spec repr p bptr value true s hsize (fun _ => authority) h F
    ⟨a, b, hab, hh, ha, pointsTo_readable hb⟩ hd hm hinv

theorem end_from_mut.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (hsize : 0 < repr.size) :
    Triple (sep (alloc repr p bptr 1 false) (readable repr p bptr value))
      (core.ptr.end_from_mut repr p) (fun x h => x = value ∧ empty h) := by
  intro h F s hp hd hm hinv
  exact read_free.spec repr p bptr value false s hsize (by simp) h F hp hd hm hinv

theorem read_view.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (own : Bool) (hsize : 0 < repr.size) :
    Triple (sep (alloc repr p bptr 1 own) (readable repr p bptr value))
      (RawPtr.read repr p) (fun x h => x = value ∧
        sep (alloc repr p bptr 1 own) (readable repr p bptr value) h) := by
  apply Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp) ?_
    (frame (R := alloc repr p bptr 1 own) (read_exposed.spec repr p bptr value 0 hsize))
  intro x h hp
  obtain ⟨he, hp⟩ := (sep_and_left _ _ _ h).mp hp
  exact ⟨he, (sep_comm _ _ h).mp hp⟩

theorem write_view.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old value : T) (own : Bool) (noPointers : ∀ q, ¬ repr.Carries value q)
    (hsize : 0 < repr.size) :
    Triple (sep (alloc repr p bptr 1 own) (readable repr p bptr old))
      (MutRawPtr.write repr p value)
      (fun _ => sep (alloc repr p bptr 1 own) (readable repr p bptr value)) := by
  apply Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp) ?_
    (frame (R := alloc repr p bptr 1 own)
      (write_readable.spec repr p bptr old value noPointers hsize))
  intro _ h hp
  exact (sep_comm _ _ h).mp (sep_mono (fun _ => pointsTo_readable) (fun _ hp => hp) hp)

/-- A lexical ownership scope retains return authority alongside ordinary
separation resources. Byte operations preserve it; allocating new aliases is
not admitted by a blanket frame rule for this additional authority. -/
def RootTriple (roots : List Nat) (P : Assertion) (c : Result α)
    (Q : α → Assertion) : Prop :=
  ∀ h F s, P h → h.Disjoint F → Fragment.Matches s (h ∪ F) → s.Inv →
    (∀ root ∈ roots, RootReturn s root) →
    Spec c (fun x s' => (∀ root ∈ roots, RootReturn s' root) ∧
      ∃ h', h'.Disjoint F ∧ Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧ Q x h') s

namespace RootTriple

variable {roots : List Nat}

theorem toTriple (ht : RootTriple [] P c Q) : Triple P c Q := by
  intro h F s hp hd hm hi
  apply Spec.mono (ht h F s hp hd hm hi (by simp))
  rintro x s' ⟨_, h', hd', hm', hi', hq⟩
  exact ⟨h', hd', hm', hi', hq⟩

theorem pure (P : Assertion) (x : α) :
    RootTriple roots P (pure x) (fun y h => y = x ∧ P h) := by
  intro h F s hp hd hm hi hr
  exact (Spec.pure _ _ _).mpr ⟨hr, h, hd, hm, hi, rfl, hp⟩

theorem bind {c : Result α} {k : α → Result β} {Q : α → Assertion}
    (hc : RootTriple roots P c Q)
    (hk : ∀ x, RootTriple roots (Q x) (k x) R) :
    RootTriple roots P (Aeneas.Std.bind c k) R := by
  intro h F s hp hd hm hi hr
  apply Spec.bind (hc h F s hp hd hm hi hr)
  rintro x s' ⟨hr', h', hd', hm', hi', hq⟩
  exact hk x h' F s' hq hd' hm' hi' hr'

theorem conseq (hp : ∀ h, P h → P' h)
    (hq : ∀ x h, Q' x h → Q x h) (ht : RootTriple roots P' c Q') :
    RootTriple roots P c Q := by
  intro h F s hP hd hm hi hr
  apply Spec.mono (ht h F s (hp h hP) hd hm hi hr)
  rintro x s' ⟨hr', h', hd', hm', hi', hQ⟩
  exact ⟨hr', h', hd', hm', hi', hq x h' hQ⟩

theorem pure_pre (ht : A → RootTriple roots P c Q) :
    RootTriple roots (fun h => A ∧ P h) c Q := by
  intro h F s ⟨ha, hp⟩ hd hm hi hr
  exact ht ha h F s hp hd hm hi hr

theorem frame (ht : RootTriple roots P c Q) :
    RootTriple roots (sep P R) c (fun x => sep (Q x) R) := by
  intro h F s ⟨a, b, hab, he, hp, hr⟩ hf hm hi roots'
  subst h
  obtain ⟨haF, hbF⟩ := Fragment.disjoint_union_left.mp hf
  rw [Fragment.union_assoc] at hm
  apply Spec.mono (ht a (b ∪ F) s hp
    (Fragment.disjoint_union_right.mpr ⟨hab, haF⟩) hm hi roots')
  rintro x s' ⟨roots'', a', hd, hm', hi', hq⟩
  obtain ⟨ha'b, ha'F⟩ := Fragment.disjoint_union_right.mp hd
  exact ⟨roots'', a' ∪ b, Fragment.disjoint_union_left.mpr ⟨ha'F, hbF⟩,
    by simpa [Fragment.union_assoc] using hm', hi', a', b, ha'b, rfl, hq, hr⟩

theorem checkedModify {modify : State → α → State → Prop}
    (ht : SepLogic.Triple P modify Q)
    (preserve : ∀ s x s', modify s x s' →
      ∀ root, RootReturn s root → RootReturn s' root) :
    RootTriple roots P (Result.checkedModify modify) Q := by
  intro h F s hp hd hm hi hr
  obtain ⟨enabled, post⟩ := ht h F s hp hd hm hi
  exact Spec.checkedModify.mpr ⟨enabled, fun x s' hx =>
    ⟨fun root mem => preserve s x s' hx root (hr root mem), post x s' hx⟩⟩

theorem read (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (value : T)
    (depth : Nat) (hsize : 0 < repr.size) :
    RootTriple roots (pointsTo repr p bptr value depth) (RawPtr.read repr p)
      (fun x h => x = value ∧ pointsTo repr p bptr value depth h) := by
  apply checkedModify (SepLogic.read.spec repr p bptr value depth hsize)
  rintro s x s' ⟨_, rfl⟩ root authority
  exact authority

theorem write (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (old value : T)
    (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    RootTriple roots (pointsTo repr p bptr old) (MutRawPtr.write repr p value)
      (fun _ => pointsTo repr p bptr value) := by
  apply checkedModify
    (SepLogic.write_pointsTo.spec repr p bptr old value noPointers hsize)
  rintro s _ s' ⟨data, encoded, run⟩ root authority
  exact authority.modify run

theorem write_local (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (old value : T)
    (R : Assertion) (support : ∀ h, sep (pointsTo repr p bptr old) R h →
      SupportsValue repr value h) (hsize : 0 < repr.size) :
    RootTriple roots (sep (pointsTo repr p bptr old) R) (MutRawPtr.write repr p value)
      (fun _ => sep (pointsTo repr p bptr value) R) := by
  apply checkedModify
    (SepLogic.write_pointsTo_local.spec repr p bptr old value R support hsize)
  rintro s _ s' ⟨data, encoded, run⟩ root authority
  exact authority.modify run

theorem read_owned (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (own : Bool) (hsize : 0 < repr.size) :
    RootTriple roots (sep (alloc repr p bptr 1 own) (pointsTo repr p bptr value))
      (RawPtr.read repr p) (fun x h => x = value ∧
        sep (alloc repr p bptr 1 own) (pointsTo repr p bptr value) h) := by
  apply conseq (fun h hp => (sep_comm _ _ h).mp hp) ?_
    (frame (R := alloc repr p bptr 1 own) (read repr p bptr value 0 hsize))
  intro x h hp
  obtain ⟨he, hp⟩ := (sep_and_left _ _ _ h).mp hp
  exact ⟨he, (sep_comm _ _ h).mp hp⟩

theorem write_owned (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old value : T) (own : Bool) (noPointers : ∀ q, ¬ repr.Carries value q)
    (hsize : 0 < repr.size) :
    RootTriple roots (sep (alloc repr p bptr 1 own) (pointsTo repr p bptr old))
      (MutRawPtr.write repr p value)
      (fun _ => sep (alloc repr p bptr 1 own) (pointsTo repr p bptr value)) := by
  exact conseq (fun h hp => (sep_comm _ _ h).mp hp)
    (fun _ h hp => (sep_comm _ _ h).mp hp)
    (frame (R := alloc repr p bptr 1 own)
      (write repr p bptr old value noPointers hsize))

theorem add (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (count : Usize) (length : Nat) (own : Bool)
    (hstart : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * repr.size)
    (hhi : p.address.val + count.val * repr.size ≤ bptr.val + length * repr.size)
    (hfit : p.address.val + count.val * repr.size < 2 ^ UScalarTy.numBits .Usize) :
    RootTriple roots (alloc repr ⟨p.provenance, bptr⟩ bptr length own)
      (RawPtr.add repr p count)
      (fun q h => q.provenance = p.provenance ∧
        q.address.val = p.address.val + count.val * repr.size ∧
        alloc repr ⟨p.provenance, bptr⟩ bptr length own h) := by
  intro h F s hp hd hm hi hr
  have ordinary := Spec.checkedModify.mp
    (HeapWP.add.spec repr p bptr count length own hstart hhi hfit h F s hp hd hm hi)
  apply Spec.checkedModify.mpr
  refine ⟨ordinary.1, ?_⟩
  rintro q s' run
  exact ⟨run.2 ▸ hr, ordinary.2 q s' run⟩

theorem add_alloc (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (count : Usize) (length : Nat) (own : Bool) (within : count.val ≤ length) :
    RootTriple roots (alloc repr p bptr length own) (RawPtr.add repr p count)
      (fun q h => q.provenance = p.provenance ∧
        q.address.val = p.address.val + count.val * repr.size ∧
        alloc repr p bptr length own h) := by
  intro h F s hp hd hm hi hr
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have member : h (.cleanup p.provenance (length * repr.size) bptr own) := by
    rw [hp.2]
    rfl
  obtain ⟨blk, hl, hlen, _, hb, _⟩ := localMatch _ member
  have valid := hi.validBlock hl
  simp only [Heap.validBlock, Heap.bounded, Bool.and_eq_true,
    decide_eq_true_eq] at valid
  have bound : p.address.val + count.val * repr.size ≤ bptr.val + length * repr.size := by
    rw [hp.1]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right repr.size within) _
  have fit : p.address.val + count.val * repr.size < 2 ^ UScalarTy.numBits .Usize := by
    apply lt_of_le_of_lt bound
    simpa [hb, hlen] using valid.1.1.2
  have same : (⟨p.provenance, bptr⟩ : RawPtr T) = p := by
    exact congrArg (RawPtr.mk p.provenance) hp.1.symm
  simpa only [same] using
    add repr p bptr count length own (by rw [hp.1]; exact ⟨le_rfl, Nat.le_add_right _ _⟩)
      bound fit h F s (by simpa only [same] using hp) hd hm hi hr

theorem fromRaw (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (hsize : 0 < repr.size) (mem : p.provenance ∈ roots) :
    RootTriple roots (sep (alloc repr p bptr 1 true) (pointsTo repr p bptr value))
      (alloc.boxed.Box.from_raw repr p) (fun x h => x = value ∧ empty h) := by
  intro h F s hp hd hm hi hr
  obtain ⟨a, b, hab, hh, ha, hv⟩ := hp
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have readableMatch : Fragment.Matches s b := by
    rw [hh, Fragment.matches_union] at localMatch
    exact localMatch.2
  have observed := read_of_pointsTo hsize hv readableMatch
  have reading : Spec (RawPtr.read repr p) (fun x s' => x = value ∧ s' = s) s :=
    Spec.checkedModify.mpr ⟨⟨value, s, observed, rfl⟩,
      fun x s' ⟨hx, hs⟩ => ⟨Option.some.inj (hx.symm.trans observed), hs⟩⟩
  unfold alloc.boxed.Box.from_raw
  apply Spec.bind reading
  rintro x state ⟨hx, hs⟩
  subst x
  subst state
  have returning := SepLogic.returnView.spec repr p bptr value true s hsize
    (fun _ => hr p.provenance mem) h F
      ⟨a, b, hab, hh, ha, pointsTo_readable hv⟩ hd hm hi
  /- The executable return retires this view and cannot create aliases. -/
  have exactReturn : ∀ s'', Heap.returnOwned repr p 1 s = some s'' →
      s'' = s.retire p.provenance := by
    intro s'' run
    unfold Heap.returnOwned at run
    cases hl : s.allocations p.provenance
    · simp [hl] at run
    · simp only [hl, Bind.bind, Option.bind] at run
      split at run
      · contradiction
      · dsimp only at run
        split at run
        · exact (Heap.commit_success _ _ run).1
        · contradiction
  have returned : Spec (Result.checkedModify (State.returnOwned repr p 1))
      (fun (_ : Unit) s' => (∀ root ∈ roots, RootReturn s' root) ∧
        ∃ h', h'.Disjoint F ∧ Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧ empty h') s := by
    exact Spec.checkedModify.mpr ⟨returning.1, fun u s' run =>
      ⟨fun root member => (exactReturn s' run).symm ▸ (hr root member).retire p.provenance,
        returning.2 u s' run⟩⟩
  apply Spec.bind returned
  rintro _ s' ⟨hr', h', hd', hm', hi', hemp⟩
  exact (Spec.pure _ _ _).mpr ⟨hr', h', hd', hm', hi', rfl, hemp⟩

end RootTriple

end Aeneas.Std.HeapWP
