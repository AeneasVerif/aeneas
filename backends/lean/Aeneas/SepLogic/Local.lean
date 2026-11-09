module

public import Aeneas.SepLogic.Bytes
public import Aeneas.Std.Heap

/-! Local heap operations: the operations which, from every heap which matches a fragment of the
precondition together with a frame fragment, are enabled and keep the frame. These are the facts
about the operations of the byte heap from which the specifications of the raw-pointer functions are
proved (see `LocalOp.ispec_checkedModify`). The proofs about reads and writes are those of
fournet/wip-memory-model (`Heap/Specs.lean`). -/

@[expose] public section

namespace Aeneas.Std.Bytes

open Aeneas.SepLogic

universe u

/-- The heap operation `op` is local in the heap `s`, from the fragments of `A` to those of `B`. -/
def LocalAt {α : Type u} (A : Fragment → Prop) (op : Heap → α → Heap → Prop)
    (B : α → Fragment → Prop) (s : Heap) : Prop :=
  ∀ a frame, A a → a.Disjoint frame → Fragment.Matches s (a ∪ frame) → s.Inv →
    (∃ x s', op s x s') ∧
    ∀ x s', op s x s' →
      ∃ a', a'.Disjoint frame ∧ Fragment.Matches s' (a' ∪ frame) ∧ s'.Inv ∧ B x a'

/-- The heap operation `op` is local, from the fragments of `A` to those of `B`. -/
def LocalOp {α : Type u} (A : Fragment → Prop) (op : Heap → α → Heap → Prop)
    (B : α → Fragment → Prop) : Prop :=
  ∀ s, LocalAt A op B s

theorem read.local (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (value : ty) (depth : Nat) (hsize : 0 < repr.size) :
    LocalOp (pointsTo repr p bptr value depth) (State.read repr p)
      (fun x h => x = value ∧ pointsTo repr p bptr value depth h) := by
  intro s h F hp hd hm hi
  have hr := read_of_pointsTo hsize hp ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨value, s, hr, rfl⟩, ?_⟩
  rintro x s' ⟨hx, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hx.symm.trans hr), hp⟩

/-- A compatible exact update preserves every indexed frame, including overlapping
borrowed/shared views. -/
theorem modify.local (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (old new : Vector Cell repr.size)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (hc : change blk.bytes (p.offsetFrom blk.bptr) =
      some (repr.update blk.bytes (p.offsetFrom blk.bptr) hb new))
    (valid : (s.storeRepr p.provenance
      (repr.update blk.bytes (p.offsetFrom blk.bptr) hb new).toList).check = true) :
    LocalAt (block repr p blk.bptr old.toList)
      (fun s (_ : Unit) s' => Heap.modify repr p change s = some s')
      (fun _ => block repr p blk.bptr new.toList) s := by
  intro h F hp hd hm hinv
  obtain ⟨hlo, _, rfl⟩ := hp
  have hrun := Heap.modify.spec repr p change s blk _ hl hlive hlo ha hc valid
  refine ⟨⟨(), _, hrun⟩, ?_⟩
  rintro _ s' he
  have he := Option.some.inj (hrun.symm.trans he)
  subst s'
  have preserved := Heap.modify_Inv repr p s _ change hinv hrun
  exact ⟨_, disjoint_cellsHeap_congr (by simp) hd,
    (Fragment.matches_union _ _ _).mpr
      ⟨matches_update hl hlive hb _, matches_update_frame hl hb hd
        ((Fragment.matches_union _ _ _).mp hm).2⟩,
    preserved, hlo, ha, rfl⟩

/-- A particular admissible encoding can be written when its exact update is compatible. -/
theorem write_encoding.local (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (old : Vector Byte repr.size) (value : ty) (data : Vector Byte repr.size)
    (encoded : repr.encode value data)
    (hsize : 0 < repr.size) (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = old.map (Cell.shared 0))
    (valid : (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hb
      (data.map (Cell.shared 0))).toList).check = true) :
    LocalAt (block repr p blk.bptr (old.map (Cell.shared 0)).toList)
      (fun s (_ : Unit) s' => Heap.write repr p value data encoded s = some s')
      (fun _ => pointsTo repr p blk.bptr value) s := by
  have hc : Repr.write repr blk.bytes (p.offsetFrom blk.bptr) value data encoded =
      some (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (data.map (Cell.shared 0))) := by
    simp [Repr.write, hsize, hb, selected, Repr.writeBytes_shared]
  have ht := modify.local repr p s blk (old.map (Cell.shared 0)) (data.map (Cell.shared 0))
    (fun bytes i => repr.write bytes i value data encoded)
    hb hl hlive ha hc valid
  intro h F hp hd hm hi
  obtain ⟨enabled, post⟩ := ht h F hp hd hm hi
  refine ⟨enabled, fun x s' hrun => ?_⟩
  obtain ⟨h', hd', hm', hi', hp'⟩ := post x s' hrun
  exact ⟨h', hd', hm', hi', data, encoded, hp'⟩

/-- Every permitted `State.write` encoding receives an exact points-to post. -/
theorem writeAt.local (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (old : Vector Byte repr.size) (value : ty)
    (hsize : 0 < repr.size) (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = old.map (Cell.shared 0))
    (witness : ∃ data, repr.encode value data ∧
      (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hb
        (data.map (Cell.shared 0))).toList).check = true) :
    LocalAt (block repr p blk.bptr (old.map (Cell.shared 0)).toList)
      (State.write repr p value) (fun _ => pointsTo repr p blk.bptr value) s := by
  intro h F hp hd hm hinv
  have hlo := hp.1
  obtain ⟨data, encoded, valid⟩ := witness
  have ht := write_encoding.local repr p s blk old value data encoded
    hsize hb hl hlive ha selected valid
  obtain ⟨⟨x, s', hx⟩, _⟩ := ht h F hp hd hm hinv
  refine ⟨⟨x, s', data, encoded, hx⟩, ?_⟩
  rintro _ s' ⟨bytes, he, hrun⟩
  have hc : Repr.write repr blk.bytes (p.offsetFrom blk.bptr) value bytes he =
      some (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (bytes.map (Cell.shared 0))) := by
    simp [Repr.write, hsize, hb, selected, Repr.writeBytes_shared]
  have hcommit :
      Heap.commit (s.storeRepr p.provenance
        (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (bytes.map (Cell.shared 0))).toList) =
        some s' := by
    simpa [Heap.write, Heap.modify, hl, hlive, hlo, ha, hc] using hrun
  obtain ⟨hs, check⟩ := Heap.commit_success _ _ hcommit
  have hv : (s.storeRepr p.provenance
      (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (bytes.map (Cell.shared 0))).toList).check =
      true := hs ▸ check
  have ht' := write_encoding.local repr p s blk old value bytes he
    hsize hb hl hlive ha selected hv
  exact (ht' h F hp hd hm hinv).2 () s' hrun

/-- Exclusive cells authorize every admissible write of a value whose pointer payloads (if any)
have provenance in the heap. -/
theorem write.local (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (old : Vector Byte repr.size) (value : ty)
    (payloads : ∀ s : Heap, s.Inv → ∀ q, repr.Carries value q →
      (s.allocations q.provenance).isSome = true)
    (hsize : 0 < repr.size) :
    LocalOp (block repr p bptr (old.map (Cell.shared 0)).toList)
      (State.write repr p value) (fun _ => pointsTo repr p bptr value) := by
  intro s a F hp hd hm hinv
  obtain ⟨hlo, ha, rfl⟩ := hp
  obtain ⟨blk, hb, hl, hlive, hbase, selected⟩ :=
    bytes_of_matches hsize ((Fragment.matches_union _ _ _).mp hm).1
  subst bptr
  obtain ⟨data, encoded⟩ := repr.encode_complete value
  have valid := Heap.update_Inv hinv hl hb
    (old.map (Cell.shared 0)) (data.map (Cell.shared 0)) selected
    (fun i hi => by
      simpa only [Vector.getElem_map] using valid_encoding encoded (payloads s hinv) i hi)
    (fun i hi => by
      simp only [Vector.getElem_map]
      exact Cell.PermWeakens.writer _ _)
  exact writeAt.local repr p s blk old value hsize hb hl hlive ha selected
    ⟨data, encoded, valid.2⟩ _ F ⟨hlo, ha, rfl⟩ hd hm hinv

/-- Ordinary pointer-free writes need only their exclusive footprint. -/
theorem write_pointsTo.local (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (old value : ty) (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    LocalOp (pointsTo repr p bptr old) (State.write repr p value)
      (fun _ => pointsTo repr p bptr value) := by
  rintro s h F ⟨bytes, _, hp⟩ hd hm hinv
  exact write.local repr p bptr bytes value (fun _ _ q hq => (noPointers q hq).elim) hsize
    s h F hp hd hm hinv

end Aeneas.Std.Bytes
