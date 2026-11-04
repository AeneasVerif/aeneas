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
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (hc : change blk.bytes (p.offsetFrom blk.bptr) =
      some (repr.update blk.bytes (p.offsetFrom blk.bptr) hb new))
    (valid : (s.storeRepr p.provenance
      (repr.update blk.bytes (p.offsetFrom blk.bptr) hb new).toList).check = true) :
    TripleAt (block repr p blk.bptr old.toList)
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

/-- Local permission weakening preserves arbitrary frames. Payload validity is
proved bytewise from the previous representation, never by a client heap check. -/
theorem modify_weaken.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (old new : Vector Cell repr.size)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (hsize : 0 < repr.size)
    (hc : ∀ {r} (bytes : Vector Cell r) offset (hb : offset + repr.size ≤ r),
      repr.select bytes offset hb = old →
      change bytes offset = some (repr.update bytes offset hb new))
    (valid : ∀ s i (hi : i < repr.size),
      (match old[i] with | .borrowed => True | .shared _ byte => Heap.validByte s byte = true) →
      (match new[i] with | .borrowed => True | .shared _ byte => Heap.validByte s byte = true))
    (weaker : ∀ i (hi : i < repr.size), old[i].PermWeakens new[i]) :
    Triple (block repr p bptr old.toList)
      (fun s (_ : Unit) s' => Heap.modify repr p change s = some s')
      (fun _ => block repr p bptr new.toList) := by
  rintro h F s ⟨hlo, ha, rfl⟩ hd hm hinv
  obtain ⟨blk, hb, hl, hlive, hbase, selected⟩ :=
    bytes_of_matches hsize ((Fragment.matches_union _ _ _).mp hm).1
  subst bptr
  have preserved := Heap.update_Inv hinv hl hb old new selected
    (fun i hi => valid s i hi (hinv.validSelected hl hb selected i hi)) weaker
  exact modify.spec repr p s blk old new change hb hl hlive ha
    (hc blk.bytes _ hb selected) preserved.2 _ F ⟨hlo, ha, rfl⟩ hd hm hinv

/-- A particular admissible encoding can be written when its exact
update is compatible. Metadata may occur only in payloads supplied by `value`. -/
theorem write_encoding.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (old : Vector Byte repr.size) (value : ty) (data : Vector Byte repr.size)
    (encoded : repr.encode value data)
    (hsize : 0 < repr.size) (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = old.map (Cell.shared 0))
    (valid : (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hb
      (data.map (Cell.shared 0))).toList).check = true) :
    TripleAt (block repr p blk.bptr (old.map (Cell.shared 0)).toList)
      (fun s (_ : Unit) s' => Heap.write repr p value data encoded s = some s')
      (fun _ => pointsTo repr p blk.bptr value) s := by
  have hc : Repr.write repr blk.bytes (p.offsetFrom blk.bptr) value data encoded =
      some (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (data.map (Cell.shared 0))) := by
    simp [Repr.write, hsize, hb, selected, Repr.writeBytes_shared]
  have ht := modify.spec repr p s blk (old.map (Cell.shared 0)) (data.map (Cell.shared 0))
    (fun bytes i => repr.write bytes i value data encoded)
    hb hl hlive ha hc valid
  intro h F hp hd hm hi
  obtain ⟨enabled, post⟩ := ht h F hp hd hm hi
  refine ⟨enabled, fun x s' hrun => ?_⟩
  obtain ⟨h', hd', hm', hi', hp'⟩ := post x s' hrun
  exact ⟨h', hd', hm', hi', data, encoded, hp'⟩

/-- Every permitted State.write encoding receives an exact points-to post.
One compatible witness establishes enabledness; the post covers all successors,
not just that witness. The descriptor validates value-bearing bytes. -/
theorem writeAt.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (old : Vector Byte repr.size) (value : ty)
    (hsize : 0 < repr.size) (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = old.map (Cell.shared 0))
    (witness : ∃ data, repr.encode value data ∧
      (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hb
        (data.map (Cell.shared 0))).toList).check = true) :
    TripleAt (block repr p blk.bptr (old.map (Cell.shared 0)).toList)
      (State.write repr p value) (fun _ => pointsTo repr p blk.bptr value) s := by
  intro h F hp hd hm hinv
  have hlo := hp.1
  obtain ⟨data, encoded, valid⟩ := witness
  have ht := write_encoding.spec repr p s blk old value data encoded
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
  have ht' := write_encoding.spec repr p s blk old value bytes he
    hsize hb hl hlive ha selected hv
  exact (ht' h F hp hd hm hinv).2 () s' hrun

/-- Exclusive cells authorize every admissible write. Pointer payload provenance
come from local resources `R`; no whole-heap compatibility check is exposed.
Every matching frame and every encoding successor is retained. -/
theorem write_local.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (old : Vector Byte repr.size) (value : ty) (R : Assertion)
    (support : ∀ h, sep (block repr p bptr (old.map (Cell.shared 0)).toList) R h →
      SupportsValue repr value h) (hsize : 0 < repr.size) :
    Triple (sep (block repr p bptr (old.map (Cell.shared 0)).toList) R)
      (State.write repr p value)
      (fun _ => sep (pointsTo repr p bptr value) R) := by
  rintro h F s ⟨a, b, hab, rfl, hp, hr⟩ hd hm hinv
  have matched := (Fragment.matches_union _ _ _).mp hm
  have parts := (Fragment.matches_union _ _ _).mp matched.1
  obtain ⟨hlo, ha, rfl⟩ := hp
  obtain ⟨blk, hb, hl, hlive, hbase, selected⟩ := bytes_of_matches hsize parts.1
  subst bptr
  have payloads := supportsValue_valid
    (support _ ⟨_, b, hab, rfl, ⟨hlo, ha, rfl⟩, hr⟩) matched.1 hinv
  obtain ⟨data, encoded⟩ := repr.encode_complete value
  have valid := Heap.update_Inv hinv hl hb
    (old.map (Cell.shared 0)) (data.map (Cell.shared 0)) selected
    (fun i hi => by
      simpa only [Vector.getElem_map] using valid_encoding encoded payloads i hi)
    (fun i hi => by
      simp only [Vector.getElem_map]
      exact Cell.PermWeakens.writer _ _)
  have ht := writeAt.spec repr p s blk old value hsize hb hl hlive ha selected
    ⟨data, encoded, valid.2⟩
  have framed := frameAt (R := R) ht
  exact framed _ F ⟨_, b, hab, rfl, ⟨hlo, ha, rfl⟩, hr⟩ hd hm hinv

theorem write_supported.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (old : Vector Byte repr.size) (value : ty) (R : Assertion)
    (support : ∀ h, R h → SupportsValue repr value h) (hsize : 0 < repr.size) :
    Triple (sep (block repr p bptr (old.map (Cell.shared 0)).toList) R)
      (State.write repr p value)
      (fun _ => sep (pointsTo repr p bptr value) R) := by
  apply write_local.spec repr p bptr old value R ?_ hsize
  rintro h ⟨a, b, _, rfl, _, hr⟩ q carried
  exact (support b hr q carried).mono (fun _ member => .inr member)

theorem write_pointsTo_local.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (old value : ty) (R : Assertion)
    (support : ∀ h, sep (pointsTo repr p bptr old) R h → SupportsValue repr value h)
    (hsize : 0 < repr.size) :
    Triple (sep (pointsTo repr p bptr old) R) (State.write repr p value)
      (fun _ => sep (pointsTo repr p bptr value) R) := by
  rintro h F s ⟨a, b, hab, rfl, ⟨bytes, encoded, hp⟩, hr⟩ hd hm hinv
  apply write_local.spec repr p bptr bytes value R ?_ hsize _ F s
    ⟨a, b, hab, rfl, hp, hr⟩ hd hm hinv
  rintro fragment ⟨cells, rest, disjoint, rfl, block, hr⟩
  exact support _ ⟨cells, rest, disjoint, rfl, ⟨bytes, encoded, block⟩, hr⟩

/-- Ordinary pointer-free writes need only their exclusive footprint. -/
theorem write.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (old : Vector Byte repr.size) (value : ty)
    (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    Triple (block repr p bptr (old.map (Cell.shared 0)).toList)
      (State.write repr p value) (fun _ => pointsTo repr p bptr value) := by
  have ht := write_supported.spec repr p bptr old value empty
    (fun h _ => supportsValue_noPointers repr value noPointers h) hsize
  apply Triple.conseq (fun h hp => (sep_empty_right _ h).mpr hp)
    (fun _ h hp => (sep_empty_right _ h).mp hp) ht

theorem write_pointsTo_supported.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (old value : ty) (R : Assertion)
    (support : ∀ h, R h → SupportsValue repr value h) (hsize : 0 < repr.size) :
    Triple (sep (pointsTo repr p bptr old) R) (State.write repr p value)
      (fun _ => sep (pointsTo repr p bptr value) R) := by
  rintro h F s ⟨a, b, hab, rfl, ⟨bytes, _, hp⟩, hr⟩ hd hm hinv
  exact write_supported.spec repr p bptr bytes value R support hsize _
    F s ⟨a, b, hab, rfl, hp, hr⟩ hd hm hinv

theorem write_pointsTo.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (old value : ty) (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr old) (State.write repr p value)
      (fun _ => pointsTo repr p bptr value) := by
  rintro h F s ⟨bytes, _, hp⟩ hd hm hinv
  exact write.spec repr p bptr bytes value noPointers hsize h F s hp hd hm hinv

theorem write_readable.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (old value : ty) (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    Triple (readable repr p bptr old) (State.write repr p value)
      (fun _ => pointsTo repr p bptr value) := by
  rintro h F s ⟨bytes, _, hp⟩ hd hm hinv
  exact write.spec repr p bptr bytes value noPointers hsize h F s hp hd hm hinv

end Aeneas.Std.SepLogic
