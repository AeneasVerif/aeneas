module

public import Aeneas.Std.Heap.Resources

/-! Framed symbolic-byte contracts. Read is uniformly enabled by points-to.
General mutation/restoration needs input-state compatibility: a borrowed alias
is logically separable, but cannot authorize reintroducing a conflicting writer. -/

@[expose] public section

namespace Aeneas.Std.SepLogic

theorem read.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (value : ty) (depth : Nat) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr value depth) (State.read repr p)
      (fun x h => x = value ∧ pointsTo repr p bptr value depth h) := by
  intro h F s hp hd hm hi
  have hr := read_of_pointsTo hsize hp ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨value, s, hr, rfl⟩, ?_⟩
  rintro x s' ⟨hx, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hx.symm.trans hr), hp⟩

/-- A compatible exact update preserves every indexed frame, including overlapping
borrowed/shared views. `valid` is a concrete input-state obligation, not an axiom
that arbitrary restoration or permission decrements are always enabled. -/
theorem modify.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (old new : Vector Cell repr.size)
    (change : ∀ {r}, Vector Cell r → Option (Vector Cell r))
    (hb : p.byteOffset.val + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.base = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ blk.bptr.val + p.byteOffset.val)
    (hc : change blk.bytes = some (repr.update blk.bytes p.byteOffset.val hb new))
    (valid : (s.storeRepr p.base
      (repr.update blk.bytes p.byteOffset.val hb new).toList).check = true) :
    TripleAt (block repr p blk.bptr old.toList)
      (fun s (_ : Unit) s' => Heap.modify repr p change s = some s')
      (fun _ => block repr p blk.bptr new.toList) s := by
  intro h F hp hd hm hinv
  obtain ⟨_, rfl⟩ := hp
  have hrun := Heap.modify.spec repr p change s blk _ hl hlive ha hc valid
  refine ⟨⟨(), _, hrun⟩, ?_⟩
  rintro _ s' he
  have he := Option.some.inj (hrun.symm.trans he)
  subst s'
  have preserved := Heap.modify_Inv repr p s _ change hinv hrun
  exact ⟨_, disjoint_cellsHeap_congr (by simp) hd,
    (Fragment.matches_union _ _ _).mpr
      ⟨matches_update hl hlive hb _, matches_update_frame hl hb hd
        ((Fragment.matches_union _ _ _).mp hm).2⟩,
    preserved, ha, rfl⟩

/-- A particular initialized admissible encoding can be written when its exact
update is compatible. Metadata may occur only in payloads supplied by `value`. -/
theorem write_encoding.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (old : Vector Byte repr.size) (value : ty) (data : Vector Byte repr.size)
    (encoded : repr.encodes value data)
    (initialized : ∀ i : Fin repr.size, data[i.val] ≠ .uninit)
    (hsize : 0 < repr.size) (hb : p.byteOffset.val + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.base = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ blk.bptr.val + p.byteOffset.val)
    (selected : repr.select blk.bytes p.byteOffset.val hb = old.map (Cell.shared 0))
    (valid : (s.storeRepr p.base (repr.update blk.bytes p.byteOffset.val hb
      (data.map (Cell.shared 0))).toList).check = true) :
    TripleAt (block repr p blk.bptr (old.map (Cell.shared 0)).toList)
      (fun s (_ : Unit) s' => Heap.write repr p value data encoded s = some s')
      (fun _ => pointsTo repr p blk.bptr value) s := by
  have hc : Repr.write repr blk.bytes p.byteOffset.val value data encoded =
      some (repr.update blk.bytes p.byteOffset.val hb (data.map (Cell.shared 0))) := by
    simp [Repr.write, hsize, hb, selected, Repr.writeBytes_shared]
  have ht := modify.spec repr p s blk (old.map (Cell.shared 0)) (data.map (Cell.shared 0))
    (fun bytes => repr.write bytes p.byteOffset.val value data encoded)
    hb hl hlive ha hc valid
  intro h F hp hd hm hi
  obtain ⟨enabled, post⟩ := ht h F hp hd hm hi
  refine ⟨enabled, fun x s' hrun => ?_⟩
  obtain ⟨h', hd', hm', hi', hp'⟩ := post x s' hrun
  exact ⟨h', hd', hm', hi', data, encoded, initialized, hp'⟩

/-- Every permitted State.write encoding receives an exact points-to post.
One compatible witness establishes enabledness; the post covers all successors,
not just that witness. Initialization is an explicit descriptor obligation. -/
theorem write.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (old : Vector Byte repr.size) (value : ty)
    (hsize : 0 < repr.size) (hb : p.byteOffset.val + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.base = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ blk.bptr.val + p.byteOffset.val)
    (selected : repr.select blk.bytes p.byteOffset.val hb = old.map (Cell.shared 0))
    (initialized : ∀ data, repr.encodes value data →
      ∀ i : Fin repr.size, data[i.val] ≠ .uninit)
    (witness : ∃ data, repr.encodes value data ∧
      (s.storeRepr p.base (repr.update blk.bytes p.byteOffset.val hb
        (data.map (Cell.shared 0))).toList).check = true) :
    TripleAt (block repr p blk.bptr (old.map (Cell.shared 0)).toList)
      (State.write repr p value) (fun _ => pointsTo repr p blk.bptr value) s := by
  intro h F hp hd hm hinv
  obtain ⟨data, encoded, valid⟩ := witness
  have ht := write_encoding.spec repr p s blk old value data encoded
    (initialized data encoded) hsize hb hl hlive ha selected valid
  obtain ⟨⟨x, s', hx⟩, _⟩ := ht h F hp hd hm hinv
  refine ⟨⟨x, s', data, encoded, hx⟩, ?_⟩
  rintro _ s' ⟨bytes, he, hrun⟩
  have hc : Repr.write repr blk.bytes p.byteOffset.val value bytes he =
      some (repr.update blk.bytes p.byteOffset.val hb (bytes.map (Cell.shared 0))) := by
    simp [Repr.write, hsize, hb, selected, Repr.writeBytes_shared]
  have hcommit :
      Heap.commit (s.storeRepr p.base
        (repr.update blk.bytes p.byteOffset.val hb (bytes.map (Cell.shared 0))).toList) =
        some s' := by
    simpa [Heap.write, Heap.modify, hl, hlive, ha, hc] using hrun
  obtain ⟨hs, check⟩ := Heap.commit_success _ _ hcommit
  have hv : (s.storeRepr p.base
      (repr.update blk.bytes p.byteOffset.val hb (bytes.map (Cell.shared 0))).toList).check =
      true := hs ▸ check
  have ht' := write_encoding.spec repr p s blk old value bytes he
    (initialized bytes he) hsize hb hl hlive ha selected hv
  exact (ht' h F hp hd hm hinv).2 () s' hrun

end Aeneas.Std.SepLogic
