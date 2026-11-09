module

public import Aeneas.SepLogic.Resource
public import Aeneas.Std.Heap.Lemmas

/-! The byte contents of the heap as fragments (from fournet/wip-memory-model).
Indexed byte contributions carry their immutable concrete base address.
Separating two contributions does not assert that their numerical bytes differ. -/

@[expose] public section

namespace Aeneas.Std.Bytes

open Aeneas.SepLogic

def cellsHeap (bptr : BasePtr) (base start : Nat) (cells : List Cell) : Fragment :=
  fun r => ∃ (i : Nat) (hi : i < cells.length),
    r = .cell base (start + i) bptr cells[i]

def allocHeap (repr : Repr ty) (bptr : BasePtr) (base count : Nat) (own : Bool) : Fragment :=
  Fragment.single (.cleanup base (count * repr.size) bptr own)

def block (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr) (cells : List Cell) : Fragment → Prop :=
  fun h => bptr.val ≤ p.address.val ∧ repr.align.val ∣ p.address.val ∧
    h = cellsHeap bptr p.provenance (p.offsetFrom bptr) cells

def alloc (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr) (count : Nat)
    (own : Bool) : Fragment → Prop :=
  fun h => p.address = bptr ∧ h = allocHeap repr bptr p.provenance count own

theorem alloc_active {repr : Repr ty} {p : RawPtr ty} {bptr : BasePtr}
    {count : Nat} {own : Bool} {h : Fragment} {s : Heap}
    (hp : alloc repr p bptr count own h) (hm : Fragment.Matches s h) :
    ∃ blk, s.allocations p.provenance = some blk ∧ blk.active = true := by
  have member : h (.cleanup p.provenance (count * repr.size) bptr own) := by
    rw [hp.2]
    rfl
  obtain ⟨blk, hl, _, live, _, _⟩ := hm _ member
  simp only [Heap.live, Bool.and_eq_true] at live
  exact ⟨blk, hl, live.1⟩

/-- An admissible representation, including any permitted uninitialized padding,
not merely equal numerical bytes. Decodability follows from the encoding law. -/
def pointsTo (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr) (value : ty)
    (depth : Nat := 0) : Fragment → Prop :=
  fun h => ∃ data : Vector Byte repr.size, repr.encode value data ∧
    block repr p bptr (data.map (Cell.shared depth)).toList h

/-- A readable representation need not be an admissible write: scalar exposure
of a pointer lane preserves metadata rather than re-encoding the scalar. -/
def readable (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr) (value : ty)
    (depth : Nat := 0) : Fragment → Prop :=
  fun h => ∃ data : Vector Byte repr.size, repr.decode data = some value ∧
    block repr p bptr (data.map (Cell.shared depth)).toList h

theorem pointsTo_readable {repr : Repr ty} {p : RawPtr ty} {bptr : BasePtr}
    {value : ty} {depth : Nat} {h : Fragment} (hp : pointsTo repr p bptr value depth h) :
    readable repr p bptr value depth h := by
  obtain ⟨data, encoded, hp⟩ := hp
  exact ⟨data, repr.encode_decode value data encoded, hp⟩

def Resource.bptr : Resource → BasePtr
  | .cell _ _ bptr _ | .cleanup _ _ bptr _ => bptr

/-- Provenance metadata can come from the target view or from a stored pointer
lane. The latter also covers pointers to retired views. -/
def HasProvenance (h : Fragment) (id : Nat) : Prop :=
  (∃ r, h r ∧ r.base = id) ∨
    ∃ base index bptr depth q lane,
      h (.cell base index bptr (.shared depth (.pointer q lane))) ∧ q.provenance = id

theorem HasProvenance.mono {a b : Fragment} {id : Nat}
    (known : HasProvenance a id) (included : ∀ r, a r → b r) : HasProvenance b id := by
  rcases known with ⟨r, hr, same⟩ | ⟨base, index, bptr, depth, q, lane, hr, same⟩
  · exact .inl ⟨r, included r hr, same⟩
  · exact .inr ⟨base, index, bptr, depth, q, lane, included _ hr, same⟩

/-- Local provenance evidence for every pointer payload that an encoding may
retain; numerical pointer observation alone supplies no such evidence. -/
def SupportsValue (repr : Repr ty) (value : ty) (h : Fragment) : Prop :=
  ∀ p, repr.Carries value p → HasProvenance h p.provenance

theorem supportsValue_noPointers (repr : Repr ty) (value : ty)
    (none : ∀ p, ¬ repr.Carries value p) (h : Fragment) : SupportsValue repr value h := by
  intro p hp
  exact (none p hp).elim

theorem supportsValue_pointer_alloc (repr : Repr ty) (p : RawPtr T) (bptr : BasePtr)
    (count : Nat) (own : Bool) {h : Fragment}
    (ha : alloc repr (p.cast ty) bptr count own h) :
    SupportsValue (Repr.pointer T) p h := by
  intro q hq
  have he : q = p.cast Unit := (Repr.pointer_carries p q).mp hq
  subst q
  refine .inl ⟨.cleanup p.provenance (count * repr.size) bptr own, ?_, rfl⟩
  rw [ha.2]
  rfl

theorem supportsValue_valid {s : Heap} {repr : Repr ty} {value : ty} {h : Fragment}
    (support : SupportsValue repr value h) (hm : Fragment.Matches s h) (hinv : s.Inv) :
    ∀ p, repr.Carries value p → (s.allocations p.provenance).isSome = true := by
  intro p hp
  rcases support p hp with ⟨r, hr, hb⟩ | ⟨base, index, bptr, depth, q, lane, hr, hb⟩
  · obtain ⟨blk, hl⟩ := (hm r hr).live
    simp [← hb, hl]
  · obtain ⟨blk, hl, _, _, cell⟩ := hm _ hr
    obtain ⟨bound, byte⟩ := List.getElem?_eq_some_iff.mp cell
    have valid := hinv.validCell hl index bound
    simp only [byte, Heap.validByte, Bool.and_eq_true, decide_eq_true_eq] at valid
    simpa only [← hb] using valid.2

theorem valid_encoding {s : Heap} {repr : Repr ty} {value : ty}
    {data : Vector Byte repr.size} (encoded : repr.encode value data)
    (payloads : ∀ p, repr.Carries value p → (s.allocations p.provenance).isSome = true)
    (i : Nat) (hi : i < repr.size) : s.validByte data[i] = true := by
  have hs := repr.encode_valid value data ⟨i, hi⟩ encoded
  cases he : data[i]
  · rfl
  · rfl
  · rename_i p lane
    rw [he] at hs
    simp [Heap.validByte, hs, payloads p ⟨data, encoded, ⟨i, hi⟩, lane, he⟩]

@[simp] theorem cellsHeap_nil (bptr : BasePtr) (base start : Nat) :
    cellsHeap bptr base start [] = ∅ := by
  funext r
  apply propext
  constructor
  · rintro ⟨i, hi, _⟩
    exact (Nat.not_lt_zero i hi).elim
  · exact False.elim

theorem cellsHeap_append (bptr : BasePtr) (base start : Nat) (a b : List Cell) :
    cellsHeap bptr base start (a ++ b) =
      cellsHeap bptr base start a ∪ cellsHeap bptr base (start + a.length) b := by
  funext r
  apply propext
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases ha : i < a.length
    · left
      exact ⟨i, ha, by simp [List.getElem_append_left ha]⟩
    · right
      have hb : i - a.length < b.length := by simp only [List.length_append] at hi; grind
      refine ⟨i - a.length, hb, ?_⟩
      have he : a.length + (i - a.length) = i := by grind
      simp [Nat.add_assoc, he, List.getElem_append_right (Nat.le_of_not_gt ha)]
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, by simp; grind, by simp [List.getElem_append_left hi]⟩
    · refine ⟨a.length + i, by simp; grind, ?_⟩
      simp [Nat.add_assoc]

theorem disjoint_cellsHeap_append (bptr : BasePtr) (base start : Nat) (a b : List Cell) :
    (cellsHeap bptr base start a).Disjoint
      (cellsHeap bptr base (start + a.length) b) := by
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  right
  simp only [Resource.key, ne_eq, Option.some.injEq]
  grind

/-- Independent lifetime contributions use different view IDs, even at the
same physical address. Heap matching plus `Inv` must still justify compatibility. -/
theorem disjoint_views (a b : BasePtr) (i j start finish : Nat) (x y : List Cell)
    (different : i ≠ j) :
    (cellsHeap a i start x).Disjoint (cellsHeap b j finish y) := by
  rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
  exact .inl different

theorem matches_cellsHeap {s : Heap} {bptr : BasePtr} {base start : Nat}
    {cells : List Cell} :
    Fragment.Matches s (cellsHeap bptr base start cells) ↔
      ∀ (i : Nat) (hi : i < cells.length), ∃ block,
        s.allocations base = some block ∧ s.live block = true ∧ block.bptr = bptr ∧
        block.repr[start + i]? = some cells[i] := by
  constructor
  · intro h i hi
    exact h _ ⟨i, hi, rfl⟩
  · rintro h _ ⟨i, hi, rfl⟩
    exact h i hi

theorem bytes_of_matches {s : Heap} {repr : Repr ty} {p : RawPtr ty} {bptr : BasePtr}
    {data : Vector Cell repr.size} (hsize : 0 < repr.size)
    (hm : Fragment.Matches s (cellsHeap bptr p.provenance (p.offsetFrom bptr) data.toList)) :
    ∃ (blk : Block) (hi : p.offsetFrom bptr + repr.size ≤ blk.repr.length),
      s.allocations p.provenance = some blk ∧ s.live blk = true ∧ blk.bptr = bptr ∧
      repr.select blk.bytes (p.offsetFrom bptr) hi = data := by
  obtain ⟨blk, hs, hlive, ha, _⟩ := matches_cellsHeap.mp hm 0 (by simpa using hsize)
  have hp : ∀ (i : Nat) (hi : i < repr.size),
      blk.repr[p.offsetFrom bptr + i]? = some data[i] := by
    intro i hi
    obtain ⟨actual, hs', _, _, hv⟩ := matches_cellsHeap.mp hm i (by simpa using hi)
    have he : actual = blk := Option.some.inj (hs'.symm.trans hs)
    simpa [he] using hv
  have hb : p.offsetFrom bptr + repr.size ≤ blk.repr.length := by
    have hx := hp (repr.size - 1) (by grind)
    have hh := List.getElem?_eq_some_iff.mp hx |>.1
    grind
  refine ⟨blk, hb, hs, hlive, ha, ?_⟩
  apply Vector.toList_inj.mp
  apply List.ext_getElem?
  intro i
  rw [Repr.select_toList]
  by_cases hi : i < repr.size
  · simpa [hi, Block.bytes] using hp i hi
  · simp [hi]
    grind

theorem read_of_readable {s : Heap} {repr : Repr ty} {p : RawPtr ty} {bptr : BasePtr}
    {value : ty} {depth : Nat} {h : Fragment} (hs : 0 < repr.size)
    (hp : readable repr p bptr value depth h) (hm : Fragment.Matches s h) :
    Heap.read repr p s = some value := by
  obtain ⟨data, decoded, hlo, hpa, rfl⟩ := hp
  obtain ⟨blk, hi, hl, hlive, ha, he⟩ := bytes_of_matches hs hm
  simp [Heap.read, hl, hlive, ha, hlo, hpa, Repr.read, hs, hi, he,
    Repr.readBytes_shared data depth, decoded]

theorem read_of_pointsTo {s : Heap} {repr : Repr ty} {p : RawPtr ty} {bptr : BasePtr}
    {value : ty} {depth : Nat} {h : Fragment} (hs : 0 < repr.size)
    (hp : pointsTo repr p bptr value depth h) (hm : Fragment.Matches s h) :
    Heap.read repr p s = some value :=
  read_of_readable hs (pointsTo_readable hp) hm

theorem disjoint_cellsHeap_congr {bptr : BasePtr} {base start : Nat}
    {old new : List Cell} {F : Fragment}
    (hl : old.length = new.length) (hd : (cellsHeap bptr base start old).Disjoint F) :
    (cellsHeap bptr base start new).Disjoint F := by
  rintro _ ⟨i, hi, rfl⟩ r hr
  have hi' : i < old.length := by grind
  exact hd _ ⟨i, hi', rfl⟩ r hr

theorem matches_update {s : Heap} {repr : Repr ty} {p : RawPtr ty} {blk : Block}
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (hi : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length) (data : Vector Cell repr.size) :
    Fragment.Matches
      (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hi data).toList)
      (cellsHeap blk.bptr p.provenance (p.offsetFrom blk.bptr) data.toList) := by
  rw [matches_cellsHeap]
  intro i hi'
  refine ⟨{ blk with repr := (repr.update blk.bytes (p.offsetFrom blk.bptr) hi data).toList },
    by simp [hl], by simpa using hlive, rfl, ?_⟩
  simpa using Repr.update_inside repr blk.bytes (p.offsetFrom blk.bptr) hi data i (by simpa using hi')

/-- All indexed frames are preserved: disjoint cells in this view, cells of
physical aliases in other views, and immutable cleanup layout resources. -/
theorem matches_update_frame {s : Heap} {repr : Repr ty} {p : RawPtr ty}
    {blk : Block} {old data : Vector Cell repr.size} {F : Fragment}
    (hl : s.allocations p.provenance = some blk)
    (hi : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hd : (cellsHeap blk.bptr p.provenance (p.offsetFrom blk.bptr) old.toList).Disjoint F)
    (hm : Fragment.Matches s F) :
    Fragment.Matches
      (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hi data).toList) F := by
  intro resource hr
  have hh := hm resource hr
  by_cases hb : resource.base = p.provenance
  · cases resource
    · rename_i base index bptr value
      obtain ⟨actual, hs, hlive, ha, hv⟩ := hh
      change base = p.provenance at hb
      subst base
      have he : actual = blk := Option.some.inj (hs.symm.trans hl)
      subst actual
      have hout : index < (p.offsetFrom blk.bptr) ∨ (p.offsetFrom blk.bptr) + repr.size ≤ index := by
        by_cases hlt : index < (p.offsetFrom blk.bptr)
        · exact .inl hlt
        right
        by_cases hge : (p.offsetFrom blk.bptr) + repr.size ≤ index
        · exact hge
        have hidx : index - (p.offsetFrom blk.bptr) < old.toList.length := by
          simp only [Vector.length_toList]
          grind
        have hc := hd _ ⟨index - (p.offsetFrom blk.bptr), hidx, rfl⟩ _ hr
        have he : (p.offsetFrom blk.bptr) + (index - (p.offsetFrom blk.bptr)) = index := by grind
        simp [Resource.Compatible, Resource.base, Resource.key, he] at hc
      refine ⟨{ blk with repr := (repr.update blk.bytes (p.offsetFrom blk.bptr) hi data).toList },
        by simp [hl], by simpa using hlive, ha, ?_⟩
      rw [Repr.update_outside _ _ _ _ _ index hout]
      simpa [Block.bytes] using hv
    · rename_i base size bptr own
      obtain ⟨actual, hs, hn, hlive, ha, ho⟩ := hh
      change base = p.provenance at hb
      subst base
      have he : actual = blk := Option.some.inj (hs.symm.trans hl)
      subst actual
      exact ⟨{ blk with repr := (repr.update blk.bytes (p.offsetFrom blk.bptr) hi data).toList },
        by simp [hl], by simpa only [Vector.length_toList] using hn,
        by simpa using hlive, ha, ho⟩
  · cases resource
    · rename_i base index bptr value
      obtain ⟨actual, hs, hlive, ha, hv⟩ := hh
      change base ≠ p.provenance at hb
      exact ⟨actual, by simpa [hb] using hs,
        by rw [Heap.live_storeRepr]; exact hlive, ha, hv⟩
    · rename_i base size bptr own
      obtain ⟨actual, hs, hn, hlive, ha, ho⟩ := hh
      change base ≠ p.provenance at hb
      exact ⟨actual, by simpa [hb] using hs, hn,
        by rw [Heap.live_storeRepr]; exact hlive, ha, ho⟩

end Aeneas.Std.Bytes
