module

public import Aeneas.Std.Core.PtrOps
public import Aeneas.Std.Heap.Initialization
import all Aeneas.Std.Core.PtrOps
import all Aeneas.Std.Heap.Separation

@[expose] public section

namespace Aeneas.Std.HeapWP

open SepLogic

/-- Exclusive matching footprints are physically disjoint even across distinct
view IDs. Logical separation alone only separates their indexed resources. -/
theorem pointsTo_separated (repr : Repr T) (p q : RawPtr T) (a b : BasePtr)
    (left right : T) (h : Fragment) (s : Heap)
    (hp : sep (pointsTo repr p a left) (pointsTo repr q b right) h)
    (hm : Fragment.Matches s h) (hinv : s.Inv) :
    p.address.val + repr.size ≤ q.address.val ∨
      q.address.val + repr.size ≤ p.address.val := by
  obtain ⟨x, y, hd, rfl, ⟨l, _, hlo, _, rfl⟩, ⟨r, _, hro, _, rfl⟩⟩ := hp
  obtain ⟨hml, hmr⟩ := (Fragment.matches_union _ _ _).mp hm
  by_contra hover
  have hl : p.address.val < q.address.val + repr.size := by agrind
  have hr : q.address.val < p.address.val + repr.size := by agrind
  have collision (i j : Nat) (hi : i < repr.size) (hj : j < repr.size)
      (he : p.address.val + i = q.address.val + j) : False := by
    let lc := (l.map (Cell.shared 0))[i]
    let rc := (r.map (Cell.shared 0))[j]
    have lmem : cellsHeap a p.provenance (p.offsetFrom a) (l.map (Cell.shared 0)).toList
        (.cell p.provenance (p.offsetFrom a + i) a lc) := ⟨i, by simpa using hi, rfl⟩
    have rmem : cellsHeap b q.provenance (q.offsetFrom b) (r.map (Cell.shared 0)).toList
        (.cell q.provenance (q.offsetFrom b + j) b rc) := ⟨j, by simpa using hj, rfl⟩
    by_cases hb : p.provenance = q.provenance
    · obtain ⟨lb, hbl, _, hab, _⟩ := hml _ lmem
      obtain ⟨rb, hbr, _, hbb, _⟩ := hmr _ rmem
      have blocks : lb = rb := Option.some.inj (hbl.symm.trans (hb ▸ hbr))
      have bases : a = b := hab.symm.trans (blocks ▸ hbb)
      have hc := hd _ lmem _ rmem
      simp only [Resource.Compatible, Resource.base, Resource.key, hb, ne_eq,
        not_true_eq_false, false_or, Option.some.injEq] at hc
      exact hc (by simp only [RawPtr.offsetFrom]; rw [bases]; agrind)
    · have ha : a.val + (p.offsetFrom a + i) = b.val + (q.offsetFrom b + j) := by
        simp only [RawPtr.offsetFrom]
        agrind
      have hc := Resource.Holds.overlapCompatible hinv hb (hml _ lmem) (hmr _ rmem) ha
      simp [lc, rc, Cell.compatible] at hc
  by_cases order : p.address.val ≤ q.address.val
  · exact collision (q.address.val - p.address.val) 0 (by agrind) (by agrind) (by agrind)
  · exact collision 0 (p.address.val - q.address.val) (by agrind) (by agrind) (by agrind)

private theorem snapshot_update (repr : Repr T) (p : RawPtr T) (s : Heap)
    (blk : Block) (old new : Vector Byte repr.size)
    (hb : p.offsetFrom blk.bptr + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = old.map (Cell.shared 0))
    (valid : ∀ i (hi : i < repr.size), s.validByte new[i] = true)
    (h F : Fragment) (hp : block repr p blk.bptr (old.map (Cell.shared 0)).toList h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s (h ∪ F)) (hinv : s.Inv) :
    let next := s.storeRepr p.provenance
      (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (new.map (Cell.shared 0))).toList
    ∃ h', h'.Disjoint F ∧ Fragment.Matches next (h' ∪ F) ∧ next.Inv ∧
      block repr p blk.bptr (new.map (Cell.shared 0)).toList h' := by
  obtain ⟨hlo, ha, rfl⟩ := hp
  have preserved := Heap.update_Inv hinv hl hb
    (old.map (Cell.shared 0)) (new.map (Cell.shared 0)) selected
    (fun i hi => by simpa only [Vector.getElem_map] using valid i hi)
    (fun i hi => by
      simp only [Vector.getElem_map]
      exact Cell.PermWeakens.writer _ _)
  exact ⟨_, disjoint_cellsHeap_congr (by simp) hd,
    (Fragment.matches_union _ _ _).mpr ⟨matches_update hl hlive hb _,
      matches_update_frame hl hb hd ((Fragment.matches_union _ _ _).mp hm).2⟩,
    preserved, hlo, ha, rfl⟩

theorem frame_value (ht : Triple P c (fun x h => x = value ∧ Q h)) :
    Triple (sep P R) c (fun x h => x = value ∧ sep Q R h) :=
  Triple.conseq (fun _ h => h) (fun _ _ h => (sep_and_left _ _ _ _).mp h) (frame ht)

/-- Replacement returns the exact old value and installs the requested value. -/
theorem replace.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (old value : T)
    (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr old) (RawPtr.replace repr p value)
      (fun result h => result = old ∧ pointsTo repr p bptr value 0 h) := by
  unfold RawPtr.replace
  apply Triple.bind (read.spec repr p bptr old 0 hsize)
  intro result
  apply Triple.pure_pre
  intro he
  subst result
  apply Triple.bind (write.spec repr p bptr old value noPointers hsize)
  intro _
  exact Triple.pure _ old

/-- Pointer-bearing replacement obtains provenance from local support resources. -/
theorem replace_supported.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old value : T) (R : Assertion)
    (support : ∀ h, R h → SupportsValue repr value h) (hsize : 0 < repr.size) :
    Triple (sep (pointsTo repr p bptr old) R) (RawPtr.replace repr p value)
      (fun result h => result = old ∧ sep (pointsTo repr p bptr value) R h) := by
  unfold RawPtr.replace
  apply Triple.bind (frame_value (R := R) (read.spec repr p bptr old 0 hsize))
  intro result
  apply Triple.pure_pre
  intro he
  subst result
  apply Triple.bind (write_supported.spec repr p bptr old value R support hsize)
  intro _
  exact Triple.pure _ old

/-- Swapping exclusive footprints exchanges their actual encodings, including
symbolic pointer lanes and any uninitialized padding. -/
theorem swap.spec (repr : Repr T) (p q : RawPtr T) (a b : BasePtr)
    (left right : T) (hsize : 0 < repr.size) :
    Triple (sep (pointsTo repr p a left) (pointsTo repr q b right))
      (RawPtr.swap repr p q)
      (fun _ => sep (pointsTo repr p a right) (pointsTo repr q b left)) := by
  apply Triple.checkedModify
  intro h F s hp hd hm hinv
  have separated := pointsTo_separated repr p q a b left right h s hp
    ((Fragment.matches_union _ _ _).mp hm).1 hinv
  obtain ⟨x, y, hxy, rfl, ⟨l, el, hp⟩, ⟨r, er, hq⟩⟩ := hp
  obtain ⟨hxF, hyF⟩ := Fragment.disjoint_union_left.mp hd
  have matched : Fragment.Matches s (x ∪ (y ∪ F)) := by
    simpa [Fragment.union_assoc] using hm
  have parts := (Fragment.matches_union _ _ _).mp matched
  have others := (Fragment.matches_union _ _ _).mp parts.2
  obtain ⟨la, hpa, hla, hlive, habase, hls⟩ := bytes_of_matches hsize (hp.2.2 ▸ parts.1)
  obtain ⟨rb, hqb, hlb, hrive, hbbase, hrs⟩ := bytes_of_matches hsize (hq.2.2 ▸ others.1)
  subst a
  subst b
  have vl : ∀ i (hi : i < repr.size), s.validByte l[i] = true := by
    intro i hi
    simpa using hinv.validSelected hla hpa hls i hi
  have vr : ∀ i (hi : i < repr.size), s.validByte r[i] = true := by
    intro i hi
    simpa using hinv.validSelected hlb hqb hrs i hi
  let first := s.storeRepr p.provenance
    (repr.update la.bytes (p.offsetFrom la.bptr) hpa (r.map (Cell.shared 0))).toList
  obtain ⟨x', hx', hm', hi', hp'⟩ := snapshot_update repr p s la l r hpa hla hlive hls vr
    x (y ∪ F) hp (Fragment.disjoint_union_right.mpr ⟨hxy, hxF⟩) matched hinv
  change Fragment.Matches first (x' ∪ (y ∪ F)) at hm'
  change first.Inv at hi'
  have mq := (Fragment.matches_union _ _ _).mp
    ((Fragment.matches_union _ _ _).mp hm').2 |>.1
  obtain ⟨current, hqc, hlc, hclive, hcbase, hcs⟩ :=
    bytes_of_matches hsize (hq.2.2 ▸ mq)
  simp only [← hcbase] at hqc hcs
  have hqcurrent : block repr q current.bptr (r.map (Cell.shared 0)).toList y := by
    simpa only [hcbase] using hq
  have vl' : ∀ i (hi : i < repr.size), first.validByte l[i] = true := by
    intro i hi
    exact (Heap.validByte_storeRepr s _ _ _).trans (vl i hi)
  have hmy : Fragment.Matches first (y ∪ (x' ∪ F)) := by
    intro resource hr
    apply hm' resource
    rcases hr with hr | hr | hr
    · exact .inr (.inl hr)
    · exact .inl hr
    · exact .inr (.inr hr)
  have hdy : y.Disjoint (x' ∪ F) :=
    Fragment.disjoint_union_right.mpr
      ⟨(Fragment.disjoint_union_right.mp hx').1.symm, hyF⟩
  let final := first.storeRepr q.provenance
    (repr.update current.bytes (q.offsetFrom current.bptr) hqc (l.map (Cell.shared 0))).toList
  obtain ⟨y', hy', hmfinal, hifinal, hq'⟩ :=
    snapshot_update repr q first current r l hqc hlc hclive hcs vl'
      y (x' ∪ F) hqcurrent hdy hmy hi'
  change Fragment.Matches final (y' ∪ (x' ∪ F)) at hmfinal
  change final.Inv at hifinal
  have snapshotL : (la.repr.drop (p.offsetFrom la.bptr)).take repr.size =
      (l.map (Cell.shared 0)).toList := by
    simpa [Block.bytes] using congrArg Vector.toList hls
  have snapshotR : (rb.repr.drop (q.offsetFrom rb.bptr)).take repr.size =
      (r.map (Cell.shared 0)).toList := by
    simpa [Block.bytes] using congrArg Vector.toList hrs
  have depth (data : Vector Byte repr.size) :
      (data.map (Cell.shared 0)).toList.all (fun cell => cell.depth == some 0) = true := by
    simp [Cell.depth]
  have boundP : p.address.val + repr.size ≤ la.bptr.val + la.repr.length := by
    simp only [RawPtr.offsetFrom] at hpa
    have lower := hp.1
    agrind
  have boundQ : q.address.val + repr.size ≤ rb.bptr.val + rb.repr.length := by
    simp only [RawPtr.offsetFrom] at hqb
    have lower := hq.1
    agrind
  have changed : la.repr.take (p.offsetFrom la.bptr) ++ (r.map (Cell.shared 0)).toList ++
      la.repr.drop (p.offsetFrom la.bptr + repr.size) =
      (repr.update la.bytes (p.offsetFrom la.bptr) hpa (r.map (Cell.shared 0))).toList := by
    simp [Block.bytes]
  have run : Heap.swapBytes repr p q s = some final := by
    simp only [Heap.swapBytes, hla, hlb, Bind.bind, Option.bind]
    rw [ite_eq_left (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨hlive, hrive⟩, hp.2.1⟩, hq.2.1⟩, hp.1⟩,
        hq.1⟩, boundP⟩, boundQ⟩, Or.imp_right Or.inl separated⟩)]
    simp only [snapshotL, snapshotR, depth, Bool.and_self, ↓reduceIte]
    rw [changed]
    change (first.allocations q.provenance).bind _ = some final
    rw [hlc]
    change Heap.commit (first.storeRepr q.provenance _) = some final
    have hc : q.offsetFrom rb.bptr = q.offsetFrom current.bptr := by rw [hcbase]
    rw [hc]
    have updated : current.repr.take (q.offsetFrom current.bptr) ++
        (l.map (Cell.shared 0)).toList ++
        current.repr.drop (q.offsetFrom current.bptr + repr.size) =
        (repr.update current.bytes (q.offsetFrom current.bptr) hqc
          (l.map (Cell.shared 0))).toList := by
      simp [Block.bytes]
    rw [updated]
    change Heap.commit final = some final
    simp [Heap.commit, hifinal.2]
  refine ⟨⟨(), final, run⟩, ?_⟩
  intro result next hn
  have he := Option.some.inj (run.symm.trans hn)
  subst next
  refine ⟨x' ∪ y', Fragment.disjoint_union_left.mpr
    ⟨(Fragment.disjoint_union_right.mp hx').2,
      (Fragment.disjoint_union_right.mp hy').2⟩, ?_, hifinal, x', y',
    (Fragment.disjoint_union_right.mp hy').1.symm, rfl, ⟨r, er, hp'⟩, ?_⟩
  · intro resource hr
    apply hmfinal resource
    rcases hr with (hr | hr) | hr
    · exact .inr (.inl hr)
    · exact .inl hr
    · exact .inr (.inr hr)
  · exact ⟨l, el, by simpa only [hcbase] using hq'⟩

private theorem store_same (s : Heap) (id : Nat) (blk : Block)
    (hl : s.allocations id = some blk) : s.storeRepr id blk.repr = s := by
  have he : Std.update s.allocations id (some blk) = s.allocations := by
    funext key
    by_cases hk : key = id
    · subst key
      simp [Std.update, hl]
    · simp [Std.update, hk]
  simp only [Heap.storeRepr, hl, Option.map_some, he]

/-- Self-swap leaves the heap and its exact representation unchanged; it does
not choose a fresh encoding for padding or expose pointer lanes as integers. -/
theorem swap_same.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (value : T)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr value) (RawPtr.swap repr p p)
      (fun _ => pointsTo repr p bptr value) := by
  apply Triple.checkedModify
  intro h F s hp hd hm hinv
  have hp0 := hp
  obtain ⟨data, _, hlo, ha, he⟩ := hp
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  rw [he] at localMatch
  obtain ⟨blk, hb, hl, hlive, hbase, selected⟩ := bytes_of_matches hsize localMatch
  subst bptr
  have snapshot : (blk.repr.drop (p.offsetFrom blk.bptr)).take repr.size =
      (data.map (Cell.shared 0)).toList := by
    simpa [Block.bytes] using congrArg Vector.toList selected
  have depth : ((blk.repr.drop (p.offsetFrom blk.bptr)).take repr.size).all
      (fun cell => cell.depth == some 0) = true := by
    rw [snapshot]
    simp [Cell.depth]
  have bound : p.address.val + repr.size ≤ blk.bptr.val + blk.repr.length := by
    simp only [RawPtr.offsetFrom] at hb
    agrind
  have unchanged : blk.repr.take (p.offsetFrom blk.bptr) ++
      (blk.repr.drop (p.offsetFrom blk.bptr)).take repr.size ++
      blk.repr.drop (p.offsetFrom blk.bptr + repr.size) = blk.repr := by
    rw [← List.take_add, List.take_append_drop]
  have stored := store_same s p.provenance blk hl
  have run : Heap.swapBytes repr p p s = some s := by
    simp only [Heap.swapBytes, hl, Bind.bind, Option.bind]
    simp only [hlive, ha, hlo, bound, or_true, decide_true,
      Bool.and_self, ↓reduceIte, depth]
    rw [unchanged, stored]
    simp only [hl]
    rw [unchanged, stored]
    simp [Heap.commit, hinv.2]
  refine ⟨⟨(), s, run⟩, ?_⟩
  intro result next hn
  have he := Option.some.inj (run.symm.trans hn)
  subst next
  exact ⟨h, hd, hm, hinv, hp0⟩

/-- Unaligned reads relax alignment only, not validity or read permissions. -/
theorem read_unaligned.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (value : T) (depth : Nat)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr.unaligned p bptr value depth) (RawPtr.read_unaligned repr p)
      (fun result h => result = value ∧ pointsTo repr.unaligned p bptr value depth h) :=
  read.spec repr.unaligned p bptr value depth hsize

/-- Unaligned writes also initialize arbitrary writable bytes. -/
theorem write_unaligned.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old : Vector Byte repr.size) (value : T)
    (noPointers : ∀ q, ¬ repr.Carries value q) (hsize : 0 < repr.size) :
    Triple (block repr.unaligned p bptr (old.map (Cell.shared 0)).toList)
      (RawPtr.write_unaligned repr p value) (fun _ => pointsTo repr.unaligned p bptr value) :=
  write_writable.spec repr.unaligned p bptr old value noPointers hsize

/-- Unaligned pointer-bearing writes retain the local support fragment. -/
theorem write_unaligned_supported.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old : Vector Byte repr.size) (value : T) (R : Assertion)
    (support : ∀ h, R h → SupportsValue repr value h) (hsize : 0 < repr.size) :
    Triple (sep (block repr.unaligned p bptr (old.map (Cell.shared 0)).toList) R)
      (RawPtr.write_unaligned repr p value)
      (fun _ => sep (pointsTo repr.unaligned p bptr value) R) :=
  write_writable_supported.spec repr.unaligned p bptr old value R support hsize

end Aeneas.Std.HeapWP
