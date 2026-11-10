/- Separation-logic specifications of the copies (`ptr::copy`, `ptr::copy_nonoverlapping`) and of
`ptr::write_bytes`, on readable ranges and possibly uninitialized ranges (`p ↦?* values`). -/
module
public import Aeneas.Std.UninitSpecs
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Core.Pointee
import all Aeneas.Std.Core.RawPtrOps
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
@[expose] public section

namespace Aeneas.Std

open Aeneas.SepLogic Aeneas.Std.WP core.mem.maybe_uninit

/-! # Copies and `write_bytes`

The models (`Aeneas/Std/Core/RawPtrOps.lean`) copy bytes with `Heap.copyBytes` (a `memmove` which
snapshots the source bytes, including uninitialized and pointer bytes, and needs exclusive
destination cells). Since the bytes are copied as they are, element by element, the copied elements
keep their description: an element whose bytes decode to `v` gives an element whose bytes decode to
`v`, and an uninitialized element (`⟨none⟩`) gives an uninitialized element.

The core is `Bytes.copyBytes_cells` (a copy over an exclusive contiguous fragment, from a snapshot
of source bytes, which may overlap the destination), used by `Bytes.copy_sep.run` (from a separate
range whose element bytes satisfy any `valid`, at any depth) and `Bytes.copy_within.run` (within one
`↦?*` range). The pure side conditions of the models (alignment, and the non-overlap check of
`copy_nonoverlapping`) are shown in every heap which realizes the precondition (`copy_sep.facts`,
`copy_within.facts`, used through `ispec_realEntails_pre`): two separate ranges, one exclusive,
never overlap numerically (`Bytes.nonoverlap_of_cells`).

Specifications (`count` may be `0`, but the ranges must be non-empty: `0 < xs.length`,
`0 < ys.length`; the byte count must fit `isize`, `hfits`, as in `RawPtr.byteCount`):
- `core.ptr.copy_nonoverlapping.spec_readable` (`@[step]`), `.spec_range`, `.spec_uninit`, and the
  generic `.spec_rangeWith`: from `src.elem j` of a readable range / range of values / `↦?*`
  range, into `dst.elem i` of a `↦?*` range;
- `core.ptr.copy.spec_uninit_within` (`@[step]`): `memmove` within one `↦?*` range;
  `core.ptr.copy.spec_readable` and `.spec_rangeWith` between separate ranges;
- `core.ptr.write_bytes.spec_uninit` (`@[step]`, bytes);
- the variants at the start of the ranges (`_src_head`, `_dst_head`, `_head`), for the programs
  which use the pointer of a range itself;
- `RawPtr.readable_uscalar_toLEBytes`: the readable view of an unsigned integer is a readable view of
  its little-endian bytes through `p.cast U8`. -/

set_option maxHeartbeats 1000000

/-! ## Lists -/

/-- The elements of `L` with `[o, o + n)` replaced by `R`. -/
theorem List.getElem?_splice {α : Type} (L R : List α) (o n i : Nat) (hR : R.length = n)
    (hle : o + n ≤ L.length) :
    (L.take o ++ R ++ L.drop (o + n))[i]? =
      if i < o then L[i]? else if i < o + n then R[i - o]? else L[i]? := by
  have hto : (L.take o).length = o := by simp; omega
  by_cases h1 : i < o
  · simp only [h1, ite_true, List.append_assoc]
    rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt h1]
  · simp only [h1, ite_false, List.append_assoc]
    rw [List.getElem?_append_right (by omega), hto]
    by_cases h2 : i < o + n
    · simp only [h2, ite_true]
      rw [List.getElem?_append_left (by omega)]
    · simp only [h2, ite_false]
      rw [List.getElem?_append_right (by omega), hR, List.getElem?_drop]
      congr 1
      omega

theorem List.mapM_range'_some {β : Type} (f : Nat → Option β) :
    ∀ (l : List β) (a : Nat), (∀ i (h : i < l.length), f (a + i) = some l[i]) →
      (List.range' a l.length).mapM f = some l
  | [], _, _ => rfl
  | x :: l, a, h => by
    have hx := h 0 (by simp)
    have ih := List.mapM_range'_some f l (a + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    simp only [List.length_cons, List.range'_succ, List.mapM_cons]
    simp only [Nat.add_zero, List.getElem_cons_zero] at hx
    simp [hx, ih]

theorem List.mapM_range_some {β : Type} (f : Nat → Option β) (l : List β)
    (h : ∀ i (h : i < l.length), f i = some l[i]) : (List.range l.length).mapM f = some l := by
  rw [List.range_eq_range']
  exact List.mapM_range'_some f l 0 (fun i hi => by simpa using h i hi)

/-- Three lists of the same lengths, related element by element. -/
theorem List.getElem_append3_rel {α β : Type} {R : α → β → Prop} (a₁ a₂ a₃ : List α)
    (b₁ b₂ b₃ : List β) (h₁ : a₁.length = b₁.length) (h₂ : a₂.length = b₂.length)
    (r₁ : ∀ k (ha : k < a₁.length) (hb : k < b₁.length), R a₁[k] b₁[k])
    (r₂ : ∀ k (ha : k < a₂.length) (hb : k < b₂.length), R a₂[k] b₂[k])
    (r₃ : ∀ k (ha : k < a₃.length) (hb : k < b₃.length), R a₃[k] b₃[k]) :
    ∀ k (ha : k < (a₁ ++ a₂ ++ a₃).length) (hb : k < (b₁ ++ b₂ ++ b₃).length),
      R (a₁ ++ a₂ ++ a₃)[k] (b₁ ++ b₂ ++ b₃)[k] := by
  intro k ha hb
  have ha' := ha
  have hb' := hb
  simp only [List.length_append] at ha' hb'
  simp only [List.getElem_append, List.length_append]
  by_cases k₁ : k < a₁.length
  · simp only [show k < a₁.length + a₂.length by omega, show k < b₁.length + b₂.length by omega,
      k₁, show k < b₁.length by omega, dite_true]
    exact r₁ k k₁ (by omega)
  · by_cases k₂ : k < a₁.length + a₂.length
    · simp only [k₂, show k < b₁.length + b₂.length by omega, k₁,
        show ¬ k < b₁.length by omega, dite_true, dite_false]
      have e : k - b₁.length = k - a₁.length := by omega
      simp only [e]
      exact r₂ _ (by omega) (by omega)
    · simp only [k₂, show ¬ k < b₁.length + b₂.length by omega, dite_false]
      have e : k - (b₁.length + b₂.length) = k - (a₁.length + a₂.length) := by omega
      simp only [e]
      exact r₃ _ (by omega) (by omega)

namespace Bytes

/-! ## Ranges as lists of chunks -/

/-- The bytes of a list of chunks, one after the other. -/
def chunkBytes {size : Nat} (ds : List (Vector Byte size)) : List Byte := ds.flatMap Vector.toList

@[simp] theorem chunkBytes_nil {size : Nat} : chunkBytes ([] : List (Vector Byte size)) = [] := rfl

@[simp] theorem chunkBytes_append {size : Nat} (a b : List (Vector Byte size)) :
    chunkBytes (a ++ b) = chunkBytes a ++ chunkBytes b := by
  simp [chunkBytes, List.flatMap_append]

@[simp] theorem chunkBytes_length {size : Nat} (ds : List (Vector Byte size)) :
    (chunkBytes ds).length = ds.length * size := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [chunkBytes, List.flatMap_cons, List.length_append, Vector.length_toList] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul]
    omega

theorem chunkBytes_cells {size : Nat} (ds : List (Vector Byte size)) (d : Nat) :
    ds.flatMap (fun b => (b.map (Cell.shared d)).toList) = (chunkBytes ds).map (Cell.shared d) := by
  induction ds with
  | nil => rfl
  | cons x ds ih =>
    simp only [List.flatMap_cons, chunkBytes, List.map_append, Vector.toList_map] at ih ⊢
    rw [ih]

/-- The chunks `[j, j + n)` of a list of chunks are the bytes `[j * size, (j + n) * size)`. -/
theorem chunkBytes_split {size : Nat} (ds : List (Vector Byte size)) (j n : Nat) :
    chunkBytes ds = chunkBytes (ds.take j) ++ chunkBytes ((ds.drop j).take n) ++
      chunkBytes (ds.drop (j + n)) := by
  rw [← chunkBytes_append, ← chunkBytes_append, List.append_assoc, ← List.drop_drop,
    List.take_append_drop, List.take_append_drop]

/-- `rangeWith` on a list of values, with the chunks of bytes as a list. -/
theorem rangeWith_iff_list {T V : Type} (repr : Repr T) (valid : V → Vector Byte repr.size → Prop)
    (p : RawPtr T) (bptr : BasePtr) (vs : List V) (d : Nat) (h : Fragment) :
    rangeWith repr valid p bptr (listVec vs) d h ↔
      ∃ ds : List (Vector Byte repr.size), ds.length = vs.length ∧
        (∀ k (hv : k < vs.length) (hd : k < ds.length), valid vs[k] ds[k]) ∧
        block repr p bptr ((chunkBytes ds).map (Cell.shared d)) h := by
  constructor
  · rintro ⟨data, hv, hb⟩
    refine ⟨data.toList, by simp, fun k hk _ => ?_, ?_⟩
    · have := hv ⟨k, hk⟩
      simpa [listVec] using this
    · rw [Vector.toList_flatMap', chunkBytes_cells] at hb
      exact hb
  · rintro ⟨ds, hlen, hv, hb⟩
    refine ⟨⟨ds.toArray, by simp [hlen]⟩, fun k => ?_, ?_⟩
    · have := hv k.val k.isLt (by omega)
      simpa [listVec] using this
    · rw [Vector.toList_flatMap', chunkBytes_cells]
      simpa using hb

/-! ## The copy of bytes, in the heap -/

/-- The bytes `bs` are the bytes of the cells from `src` on, which hold in the heap `s` (at any
depth: they need not be exclusive, but they must not be borrowed). -/
def SourceBytes {T : Type} (s : Heap) (src : RawPtr T) (bs : List Byte) : Prop :=
  ∃ blk, s.allocations src.provenance = some blk ∧ s.live blk = true ∧
    blk.bptr.val ≤ src.address.val ∧
    src.address.val + bs.length ≤ blk.bptr.val + blk.repr.length ∧
    ∀ k (hk : k < bs.length), ∃ d, blk.repr[src.offsetFrom blk.bptr + k]? = some (.shared d bs[k])

/-- The block and the cells of a non-empty matching contiguous fragment. -/
theorem block_of_cellsHeap {s : Heap} {bptr : BasePtr} {prov off : Nat} {C : List Cell}
    (hm : Fragment.Matches s (cellsHeap bptr prov off C)) (hne : 0 < C.length) :
    ∃ blk, s.allocations prov = some blk ∧ s.live blk = true ∧ blk.bptr = bptr ∧
      off + C.length ≤ blk.repr.length ∧ ∀ k (hk : k < C.length), blk.repr[off + k]? = some C[k] := by
  obtain ⟨blk, hl, hlive, hb, _⟩ := matches_cellsHeap.mp hm 0 hne
  have hcell : ∀ k (hk : k < C.length), blk.repr[off + k]? = some C[k] := by
    intro k hk
    obtain ⟨blk', hl', _, _, hc⟩ := matches_cellsHeap.mp hm k hk
    rw [hl] at hl'
    cases hl'
    exact hc
  refine ⟨blk, hl, hlive, hb, ?_, hcell⟩
  have := hcell (C.length - 1) (by omega)
  have := (List.getElem?_eq_some_iff.mp this).1
  omega

theorem sourceBytes_of_cellsHeap {T : Type} {s : Heap} {bptr : BasePtr} {off d : Nat}
    {C₁ bs C₃ : List Byte} {src : RawPtr T}
    (hm : Fragment.Matches s (cellsHeap bptr src.provenance off ((C₁ ++ bs ++ C₃).map (Cell.shared d))))
    (hne : 0 < (C₁ ++ bs ++ C₃).length)
    (haddr : src.address.val = bptr.val + off + C₁.length) : SourceBytes s src bs := by
  obtain ⟨blk, hl, hlive, hb, hlen, hcell⟩ := block_of_cellsHeap hm (by simpa using hne)
  simp only [List.length_map, List.length_append] at hlen
  subst hb
  refine ⟨blk, hl, hlive, by omega, by omega, fun k hk => ⟨d, ?_⟩⟩
  have hoff : src.offsetFrom blk.bptr + k = off + (C₁.length + k) := by
    simp only [RawPtr.offsetFrom]; omega
  rw [hoff, hcell _ (by simp; omega)]
  simp only [List.getElem_map, Option.some.injEq, Cell.shared.injEq, true_and]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

/-- A fragment which has no cell where the bytes of a block change keeps matching. -/
theorem matches_storeRepr_frame {s : Heap} {id : Nat} {blk : Block} {bytes : List Cell}
    {G : Fragment} (hl : s.allocations id = some blk) (hlen : bytes.length = blk.repr.length)
    (hsame : ∀ idx bptr c, G (.cell id idx bptr c) → bytes[idx]? = blk.repr[idx]?)
    (hm : Fragment.Matches s G) : Fragment.Matches (s.storeRepr id bytes) G := by
  intro r hr
  have hh := hm r hr
  cases r with
  | cell base index bptr c =>
    obtain ⟨actual, hs, hlive, ha, hv⟩ := hh
    by_cases hb : base = id
    · subst hb
      rw [hl] at hs
      cases hs
      refine ⟨{ blk with repr := bytes }, by simp [hl], by simpa using hlive, ha, ?_⟩
      simp only
      rw [hsame _ _ _ hr]
      exact hv
    · exact ⟨actual, by simp [hb, hs], by rw [Heap.live_storeRepr]; exact hlive, ha, hv⟩
  | cleanup base size bptr own =>
    obtain ⟨actual, hs, hn, hlive, ha, ho⟩ := hh
    by_cases hb : base = id
    · subst hb
      rw [hl] at hs
      cases hs
      exact ⟨{ blk with repr := bytes }, by simp [hl], by simpa [hlen] using hn,
        by simpa using hlive, ha, ho⟩
    · exact ⟨actual, by simp [hb, hs], hn, by rw [Heap.live_storeRepr]; exact hlive, ha, ho⟩

/-- The copy of the bytes `bs` (the snapshot of the source, `SourceBytes`) over the bytes `old` of
an exclusive contiguous fragment, at `dst`: it succeeds, and the fragment then holds `bs` there,
with every disjoint frame kept. The source may overlap the destination. -/
theorem copyBytes_cells {T U : Type} {s : Heap} (hinv : s.Inv) {src : RawPtr T} {dst : RawPtr U}
    {dbptr : BasePtr} {doff : Nat} {B₁ old B₃ bs : List Byte} {G : Fragment}
    (hlen : old.length = bs.length) (hne : 0 < (B₁ ++ old ++ B₃).length)
    (hdaddr : dst.address.val = dbptr.val + doff + B₁.length)
    (hm : Fragment.Matches s
      (cellsHeap dbptr dst.provenance doff ((B₁ ++ old ++ B₃).map (Cell.shared 0)) ∪ G))
    (hd : (cellsHeap dbptr dst.provenance doff ((B₁ ++ old ++ B₃).map (Cell.shared 0))).Disjoint G)
    (hsrc : SourceBytes s src bs) :
    ∃ s', Heap.copyBytes src dst bs.length s = some s' ∧ s'.Inv ∧
      Fragment.Matches s'
        (cellsHeap dbptr dst.provenance doff ((B₁ ++ bs ++ B₃).map (Cell.shared 0)) ∪ G) ∧
      ∀ base, AllExclusive s' base →
        AllExclusive s base ∧ (Bytes.RootReturn s base → Bytes.RootReturn s' base) := by
  obtain ⟨hmD, hmG⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨dblk, hdl, hdlive, hdb, hdlen, hdcell⟩ := block_of_cellsHeap hmD (by simpa using hne)
  obtain ⟨sblk, hsl, hslive, hslo, hshi, hscell⟩ := hsrc
  simp only [List.length_map, List.length_append] at hdlen hdcell
  subst hdb
  set n := bs.length with hn
  set o := doff + B₁.length with ho
  have hdoff : dst.offsetFrom dblk.bptr = o := by simp only [RawPtr.offsetFrom]; omega
  -- The cells of the destination fragment
  have hdcell' : ∀ k (hk : k < n), dblk.repr[o + k]? = some (.shared 0 old[k]) := by
    intro k hk
    have := hdcell (B₁.length + k) (by omega)
    rw [show doff + (B₁.length + k) = o + k by omega] at this
    rw [this]
    simp only [List.getElem_map, Option.some.injEq, Cell.shared.injEq, true_and]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
    simp
  -- The destination is exclusive
  have hexcl : ((dblk.repr.drop o).take n).all (fun cell => cell.depth == some 0) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have hk' : k < n := by simp at hk; omega
    have := hdcell' k hk'
    simp only [List.getElem_take, List.getElem_drop]
    rw [List.getElem?_eq_getElem (by simp at hk; omega)] at this
    rw [Option.some.inj this]
    rfl
  -- The new bytes of the destination block
  set bytes := dblk.repr.take o ++ Cell.full bs ++ dblk.repr.drop (o + n) with hbytes
  have hfull : (Cell.full bs).length = n := by simp [Cell.full, hn]
  have hblen : bytes.length = dblk.repr.length := by
    simp only [hbytes, List.length_append, List.length_take, List.length_drop, hfull]; omega
  have hget : ∀ i, bytes[i]? =
      if i < o then dblk.repr[i]? else if i < o + n then (Cell.full bs)[i - o]? else dblk.repr[i]? :=
    fun i => List.getElem?_splice _ _ o n i hfull (by omega)
  have hInv : (s.storeRepr dst.provenance bytes).Inv := by
    apply Heap.storeRepr_Inv hinv hdl bytes hblen
    · intro cell hc
      obtain ⟨i, hi, he⟩ := List.getElem_of_mem hc
      have hgi := hget i
      rw [List.getElem?_eq_getElem hi, he] at hgi
      split at hgi
      · have := hinv.validCell hdl i (by omega)
        rw [List.getElem?_eq_getElem (by omega)] at hgi
        rw [Option.some.inj hgi]
        exact this
      · split at hgi
        · rename_i h1 h2
          simp only [Cell.full, List.getElem?_map] at hgi
          rw [List.getElem?_eq_getElem (by omega)] at hgi
          simp only [Option.map_some, Option.some.injEq] at hgi
          subst hgi
          obtain ⟨d, hc⟩ := hscell (i - o) (by omega)
          have hsi := (List.getElem?_eq_some_iff.mp hc)
          have := hinv.validCell hsl _ hsi.1
          rw [hsi.2] at this
          exact this
        · have := hinv.validCell hdl i (by omega)
          rw [List.getElem?_eq_getElem (by omega)] at hgi
          rw [Option.some.inj hgi]
          exact this
    · intro i hi
      have hgi := hget i
      rw [List.getElem?_eq_getElem (by omega)] at hgi
      split at hgi
      · rw [List.getElem?_eq_getElem hi] at hgi
        rw [Option.some.inj hgi]
        exact Cell.PermWeakens.refl _
      · split at hgi
        · simp only [Cell.full, List.getElem?_map] at hgi
          rw [List.getElem?_eq_getElem (by omega)] at hgi
          simp only [Option.map_some, Option.some.injEq] at hgi
          rw [hgi]
          have := hdcell' (i - o) (by omega)
          rw [show o + (i - o) = i by omega, List.getElem?_eq_getElem hi] at this
          rw [Option.some.inj this]
          exact Cell.PermWeakens.writer _ _
        · rw [List.getElem?_eq_getElem hi] at hgi
          rw [Option.some.inj hgi]
          exact Cell.PermWeakens.refl _
  have hrun : Heap.copyBytes src dst n s = some (s.storeRepr dst.provenance bytes) := by
    unfold Heap.copyBytes
    simp only [hsl, hdl, Option.bind_eq_bind, Option.bind_some, hslive, hdlive, Bool.true_and,
      hdoff, hexcl, ite_true]
    have c1 : sblk.bptr.val ≤ src.address.val := hslo
    have c2 : dblk.bptr.val ≤ dst.address.val := by omega
    have c3 : src.address.val + n ≤ sblk.bptr.val + sblk.repr.length := hshi
    have c4 : dst.address.val + n ≤ dblk.bptr.val + dblk.repr.length := by omega
    simp only [c1, c2, c3, c4, decide_true, Bool.and_self, ite_true, Heap.commit]
    rw [hn, List.mapM_range_some _ bs (fun i hi => by
      obtain ⟨d, hc⟩ := hscell i hi
      simp [hc])]
    simp only [Option.bind_some, ← hn, ← hbytes, hInv.2, ite_true]
  refine ⟨_, hrun, hInv, (Fragment.matches_union _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · -- The new cells of the destination
    rw [matches_cellsHeap]
    intro k hk
    simp only [List.length_map, List.length_append] at hk
    refine ⟨{ dblk with repr := bytes }, by simp [hdl], by simpa using hdlive, rfl, ?_⟩
    simp only
    rw [hget]
    simp only [List.getElem_map, List.getElem_append]
    by_cases k₁ : k < B₁.length
    · have := hdcell k (by omega)
      simp only [show doff + k < o by omega, ite_true, this, List.getElem_map, Option.some.injEq,
        Cell.shared.injEq, true_and]
      simp [k₁]; intro h; omega
    · by_cases k₂ : k < B₁.length + n
      · simp only [show ¬ doff + k < o by omega, ite_false, show doff + k < o + n by omega, ite_true,
          Cell.full, List.getElem?_map]
        rw [List.getElem?_eq_getElem (by omega)]
        simp only [Option.map_some, Option.some.injEq, Cell.shared.injEq, true_and]
        simp [k₁, show doff + k - o = k - B₁.length by omega]; intro h; omega
      · have := hdcell k (by omega)
        simp only [show ¬ doff + k < o by omega, ite_false, show ¬ doff + k < o + n by omega, this,
          List.getElem_map, Option.some.injEq, Cell.shared.injEq, true_and]
        simp only [List.getElem_append, List.length_append, k₁, dite_false]
        simp only [show ¬ k < B₁.length + old.length by omega,
          show ¬ k < B₁.length + bs.length by omega, ↓reduceDIte]
        congr 1
        omega
  · -- The frame
    apply matches_storeRepr_frame hdl hblen _ hmG
    intro idx bptr c hc
    rw [hget]
    split
    · rfl
    · split
      · exfalso
        rename_i h1 h2
        have hk : idx - doff < ((B₁ ++ old ++ B₃).map (Cell.shared 0)).length := by
          simp; omega
        have := hd _ ⟨idx - doff, hk, rfl⟩ _ hc
        simp only [Resource.Compatible, Resource.base, Resource.key, ne_eq, not_true_eq_false,
          false_or, Option.some.injEq] at this
        omega
      · rfl
  · -- The authority
    intro base hEx
    refine ⟨?_, fun h => h.storeRepr hdl bytes hblen⟩
    intro blk hl i hi
    by_cases hb : base = dst.provenance
    · subst hb
      rw [hdl] at hl
      cases hl
      have hgi := hget i
      have hEx' := hEx { dblk with repr := bytes } (by simp [hdl]) i (by simp; omega)
      rw [List.getElem?_eq_getElem (by omega)] at hgi
      split at hgi
      · simp only [List.getElem?_eq_getElem hi, Option.some.injEq] at hgi
        simp only [hgi] at hEx'
        exact hEx'
      · split at hgi
        · have := hdcell' (i - o) (by omega)
          rw [show o + (i - o) = i by omega, List.getElem?_eq_getElem hi] at this
          rw [Option.some.inj this]
          rfl
        · simp only [List.getElem?_eq_getElem hi, Option.some.injEq] at hgi
          simp only [hgi] at hEx'
          exact hEx'
    · exact hEx blk (by simp [hb, hl]) i hi

/-! ## The copies, at the level of fragments -/

/-- The successor heap of a copy of `n` elements from the `j`-th element of a range (whose element
bytes satisfy `valid`, at any depth) into the `i`-th element of a separate possibly uninitialized
range. The copied elements become `f x` (`hf`: the bytes which satisfy `valid x` describe `f x`). -/
theorem copy_sep.run {T V : Type} [Pointee T]
    (valid : V → Vector Byte (Pointee.repr (T := T)).size → Prop) (f : V → MaybeUninit T)
    (hf : ∀ v bytes, valid v bytes → MaybeUninit.Decodes (Pointee.repr (T := T)) (f v) bytes)
    (src dst : RawPtr T) (bS bD : BasePtr) (xs : List V) (ys : List (MaybeUninit T))
    (d j i n : Nat) (hj : j + n ≤ xs.length) (hi : i + n ≤ ys.length) (hxs : 0 < xs.length)
    (hys : 0 < ys.length) (hsize : 0 < (Pointee.repr (T := T)).size)
    (h F : Fragment) (s : Heap)
    (hA : (rangeWith (Pointee.repr (T := T)) valid src bS (listVec xs) d ∗ᵇ
      uninitRange (Pointee.repr (T := T)) dst bD (listVec ys)) h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s (h ∪ F)) (hinv : s.Inv) :
    ∃ s', Heap.copyBytes (src.elem j) (dst.elem i) (n * (Pointee.repr (T := T)).size) s = some s' ∧
      ∃ h', h'.Disjoint F ∧ Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧
        (rangeWith (Pointee.repr (T := T)) valid src bS (listVec xs) d ∗ᵇ
          uninitRange (Pointee.repr (T := T)) dst bD
            (listVec (ys.take i ++ ((xs.drop j).take n).map f ++ ys.drop (i + n)))) h' ∧
        ∀ base, AllExclusive s' base →
          AllExclusive s base ∧ (Bytes.RootReturn s base → Bytes.RootReturn s' base) := by
  obtain ⟨a, b, hab, rfl, ha, hb⟩ := hA
  obtain ⟨hmab, hmF⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨hma, hmb⟩ := (Fragment.matches_union _ _ _).mp hmab
  obtain ⟨haF, hbF⟩ := Fragment.disjoint_union_left.mp hd
  have boundS := rangeWith_bound _ valid src bS (listVec xs) d hxs hsize a s ha hma hinv
  have boundD := rangeWith_bound _ _ dst bD (listVec ys) 0 hys hsize b s hb hmb hinv
  obtain ⟨dsS, hlS, hvS, hloS, halS, rfl⟩ := (rangeWith_iff_list _ _ _ _ _ _ _).mp ha
  obtain ⟨dsD, hlD, hvD, hloD, halD, rfl⟩ := (rangeWith_iff_list _ _ _ _ _ _ _).mp hb
  have mj := Nat.mul_le_mul_right (Pointee.repr (T := T)).size (show j ≤ xs.length by omega)
  have mi := Nat.mul_le_mul_right (Pointee.repr (T := T)).size (show i ≤ ys.length by omega)
  have hsj := RawPtr.elem_address src j (by omega)
  have hdi := RawPtr.elem_address dst i (by omega)
  have eS := chunkBytes_split dsS j n
  have eD := chunkBytes_split dsD i n
  have lt : ∀ (ds : List (Vector Byte (Pointee.repr (T := T)).size)) (k : Nat), k ≤ ds.length →
      (chunkBytes (ds.take k)).length = k * (Pointee.repr (T := T)).size := by
    intro ds k hk; simp; left; omega
  have lm : ∀ (ds : List (Vector Byte (Pointee.repr (T := T)).size)) (k : Nat), k + n ≤ ds.length →
      (chunkBytes ((ds.drop k).take n)).length = n * (Pointee.repr (T := T)).size := by
    intro ds k hk; simp; left; omega
  rw [eD] at hmb hbF hab
  rw [eS] at hma
  have hsrc := sourceBytes_of_cellsHeap (src := src.elem j) hma
    (by rw [← eS]; simp; exact ⟨by omega, hsize⟩)
    (by rw [hsj, lt dsS j (by omega)]; simp only [RawPtr.offsetFrom]; omega)
  have hlen := lm dsS j (by omega)
  obtain ⟨s', hrun, hinv', hm', hauth⟩ := copyBytes_cells (src := src.elem j) (dst := dst.elem i)
    (G := cellsHeap bS src.provenance (src.offsetFrom bS)
      ((chunkBytes dsS).map (Cell.shared d)) ∪ F) hinv
    (by rw [lm dsD i (by omega), hlen]) (by rw [← eD]; simp; exact ⟨by omega, hsize⟩)
    (by rw [hdi, lt dsD i (by omega)]; simp only [RawPtr.offsetFrom]; omega)
    ((Fragment.matches_union _ _ _).mpr ⟨hmb, (Fragment.matches_union _ _ _).mpr
      ⟨by rw [eS]; exact hma, hmF⟩⟩)
    (Fragment.disjoint_union_right.mpr ⟨hab.symm, hbF⟩) hsrc
  rw [hlen] at hrun
  refine ⟨s', hrun, cellsHeap bS src.provenance (src.offsetFrom bS)
      ((chunkBytes dsS).map (Cell.shared d)) ∪ cellsHeap bD dst.provenance (dst.offsetFrom bD)
      ((chunkBytes (dsD.take i) ++ chunkBytes ((dsS.drop j).take n) ++
        chunkBytes (dsD.drop (i + n))).map (Cell.shared 0)), ?_, ?_, hinv',
    ⟨_, _, ?_, rfl, ha, ?_⟩, hauth⟩
  · exact Fragment.disjoint_union_left.mpr
      ⟨haF, disjoint_cellsHeap_congr (by simp; left; omega) hbF⟩
  · obtain ⟨hm'1, hm'2⟩ := (Fragment.matches_union _ _ _).mp hm'
    obtain ⟨hm'3, hm'4⟩ := (Fragment.matches_union _ _ _).mp hm'2
    exact (Fragment.matches_union _ _ _).mpr
      ⟨(Fragment.matches_union _ _ _).mpr ⟨hm'3, hm'1⟩, hm'4⟩
  · exact (disjoint_cellsHeap_congr (by simp; left; omega) hab.symm).symm
  · refine (rangeWith_iff_list _ _ _ _ _ _ _).mpr
      ⟨dsD.take i ++ (dsS.drop j).take n ++ dsD.drop (i + n), ?_, ?_, hloD, halD, ?_⟩
    · simp; omega
    · apply List.getElem_append3_rel
      · simp; omega
      · simp; omega
      · intro k hk hk'
        simp only [List.getElem_take]
        exact hvD k (by simp at hk; omega) (by simp at hk'; omega)
      · intro k hk hk'
        simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
        exact hf _ _ (hvS (j + k) (by simp at hk; omega) (by simp at hk'; omega))
      · intro k hk hk'
        simp only [List.getElem_drop]
        exact hvD _ (by simp at hk; omega) (by simp at hk'; omega)
    · simp only [chunkBytes_append]

/-- The successor heap of a copy of `n` elements from the `j`-th element to the `i`-th element of a
possibly uninitialized range (the two parts may overlap: snapshot semantics of `memmove`). -/
theorem copy_within.run {T : Type} [Pointee T] (p : RawPtr T) (bptr : BasePtr)
    (vs : List (MaybeUninit T)) (j i n : Nat) (hj : j + n ≤ vs.length) (hi : i + n ≤ vs.length)
    (hvs : 0 < vs.length) (hsize : 0 < (Pointee.repr (T := T)).size)
    (h F : Fragment) (s : Heap)
    (hA : uninitRange (Pointee.repr (T := T)) p bptr (listVec vs) h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s (h ∪ F)) (hinv : s.Inv) :
    ∃ s', Heap.copyBytes (p.elem j) (p.elem i) (n * (Pointee.repr (T := T)).size) s = some s' ∧
      ∃ h', h'.Disjoint F ∧ Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧
        uninitRange (Pointee.repr (T := T)) p bptr
            (listVec (vs.take i ++ (vs.drop j).take n ++ vs.drop (i + n))) h' ∧
        ∀ base, AllExclusive s' base →
          AllExclusive s base ∧ (Bytes.RootReturn s base → Bytes.RootReturn s' base) := by
  obtain ⟨hmh, hmF⟩ := (Fragment.matches_union _ _ _).mp hm
  have bound := rangeWith_bound _ _ p bptr (listVec vs) 0 hvs hsize h s hA hmh hinv
  obtain ⟨ds, hl, hv, hlo, hal, rfl⟩ := (rangeWith_iff_list _ _ _ _ _ _ _).mp hA
  have mj := Nat.mul_le_mul_right (Pointee.repr (T := T)).size (show j ≤ vs.length by omega)
  have mi := Nat.mul_le_mul_right (Pointee.repr (T := T)).size (show i ≤ vs.length by omega)
  have hsj := RawPtr.elem_address p j (by omega)
  have hdi := RawPtr.elem_address p i (by omega)
  have eS := chunkBytes_split ds j n
  have eD := chunkBytes_split ds i n
  have lt : ∀ (k : Nat), k ≤ ds.length →
      (chunkBytes (ds.take k)).length = k * (Pointee.repr (T := T)).size := by
    intro k hk; simp; left; omega
  have lm : ∀ (k : Nat), k + n ≤ ds.length →
      (chunkBytes ((ds.drop k).take n)).length = n * (Pointee.repr (T := T)).size := by
    intro k hk; simp; left; omega
  have hsrc := sourceBytes_of_cellsHeap (src := p.elem j) (by rw [← eS]; exact hmh)
    (by rw [← eS]; simp; exact ⟨by omega, hsize⟩)
    (by rw [hsj, lt j (by omega)]; simp only [RawPtr.offsetFrom]; omega)
  have hlen := lm j (by omega)
  rw [eD] at hmh hd
  obtain ⟨s', hrun, hinv', hm', hauth⟩ := copyBytes_cells (src := p.elem j) (dst := p.elem i)
    (G := F) hinv (by rw [lm i (by omega), hlen]) (by rw [← eD]; simp; exact ⟨by omega, hsize⟩)
    (by rw [hdi, lt i (by omega)]; simp only [RawPtr.offsetFrom]; omega)
    ((Fragment.matches_union _ _ _).mpr ⟨hmh, hmF⟩) hd hsrc
  rw [hlen] at hrun
  refine ⟨s', hrun, _, ?_, hm', hinv', ?_, hauth⟩
  · exact disjoint_cellsHeap_congr (by simp; left; omega) hd
  · refine (rangeWith_iff_list _ _ _ _ _ _ _).mpr
      ⟨ds.take i ++ (ds.drop j).take n ++ ds.drop (i + n), ?_, ?_, hlo, hal, ?_⟩
    · simp; omega
    · apply List.getElem_append3_rel
      · simp; omega
      · simp; omega
      · intro k hk hk'
        simp only [List.getElem_take]
        exact hv k (by simp at hk; omega) (by simp at hk'; omega)
      · intro k hk hk'
        simp only [List.getElem_take, List.getElem_drop]
        exact hv (j + k) (by simp at hk; omega) (by simp at hk'; omega)
      · intro k hk hk'
        simp only [List.getElem_drop]
        exact hv _ (by simp at hk; omega) (by simp at hk'; omega)
    · simp only [chunkBytes_append]
      rfl


/-! ## Non-overlap of a range and a separate exclusive range -/

/-- Two separate ranges of cells, the second exclusive, which hold in the same heap, don't overlap
numerically: either they are in the same block, at different indices, or they are in different
blocks, which the invariant of the heap forbids to overlap where one is exclusive. -/
theorem nonoverlap_of_cells {s : Heap} (hinv : s.Inv) {bS bD : BasePtr} {pS pD offS offD dS : Nat}
    {XS XD : List Byte}
    (hmS : Fragment.Matches s (cellsHeap bS pS offS (XS.map (Cell.shared dS))))
    (hmD : Fragment.Matches s (cellsHeap bD pD offD (XD.map (Cell.shared 0))))
    (hdisj : (cellsHeap bS pS offS (XS.map (Cell.shared dS))).Disjoint
      (cellsHeap bD pD offD (XD.map (Cell.shared 0))))
    (u v N : Nat) (hu : u + N ≤ XS.length) (hv : v + N ≤ XD.length) :
    bS.val + offS + u + N ≤ bD.val + offD + v ∨ bD.val + offD + v + N ≤ bS.val + offS + u := by
  by_contra hc
  simp only [not_or, Nat.not_le] at hc
  set x := max (bS.val + offS + u) (bD.val + offD + v) with hx
  have kS : x - (bS.val + offS) < XS.length := by omega
  have kD : x - (bD.val + offD) < XD.length := by omega
  have memS : cellsHeap bS pS offS (XS.map (Cell.shared dS))
      (.cell pS (offS + (x - (bS.val + offS))) bS (Cell.shared dS XS[x - (bS.val + offS)])) :=
    ⟨x - (bS.val + offS), by simpa using kS, by simp⟩
  have memD : cellsHeap bD pD offD (XD.map (Cell.shared 0))
      (.cell pD (offD + (x - (bD.val + offD))) bD (Cell.shared 0 XD[x - (bD.val + offD)])) :=
    ⟨x - (bD.val + offD), by simpa using kD, by simp⟩
  have holdS := hmS _ memS
  have holdD := hmD _ memD
  by_cases hp : pS = pD
  · subst hp
    obtain ⟨blk, hl, _, hb, _⟩ := holdS
    obtain ⟨blk', hl', _, hb', _⟩ := holdD
    rw [hl] at hl'
    cases hl'
    have hbb : bS = bD := hb.symm.trans hb'
    subst hbb
    have := hdisj _ memS _ memD
    simp only [Resource.Compatible, Resource.base, Resource.key, ne_eq, not_true_eq_false,
      false_or, Option.some.injEq] at this
    omega
  · have := Resource.Holds.overlapCompatible hinv hp holdS holdD (by omega)
    simp [Cell.compatible] at this

end Bytes

/-! ## Lifting the copies to specifications -/

/-- A copy whose successor heap is given by `hrun`, lifted to the upward closures. -/
theorem ispec_copyBytes {T U : Type} {A B : Fragment → Prop} {src : RawPtr T} {dst : RawPtr U}
    {count : Nat} (hNoOwned : ∀ h, B h → NoOwned h)
    (hrun : ∀ h F s, A h → h.Disjoint F → Fragment.Matches s (h ∪ F) → s.Inv →
      ∃ s', Heap.copyBytes src dst count s = some s' ∧
        ∃ h', h'.Disjoint F ∧ Fragment.Matches s' (h' ∪ F) ∧ s'.Inv ∧ B h' ∧
          ∀ base, AllExclusive s' base →
            AllExclusive s base ∧ (Bytes.RootReturn s base → Bytes.RootReturn s' base)) :
    ispec (upClose A)
      (Result.checkedModify fun s (_ : Unit) s' => Heap.copyBytes src dst count s = some s')
      (fun _ => upClose B) := by
  have hLocal : Bytes.LocalOp A
      (fun s (_ : Unit) s' => Heap.copyBytes src dst count s = some s') (fun _ => B) := by
    intro h F s hA hd hm hi
    obtain ⟨s', hr, h', hd', hm', hi', hB, _⟩ := hrun h F s hA hd hm hi
    refine ⟨⟨(), s', hr⟩, fun x s'' hx => ?_⟩
    obtain rfl : s'' = s' := Option.some.inj (hx.symm.trans hr)
    exact ⟨h', hd', hm', hi', hB⟩
  have hAuth : Bytes.AuthPres A
      (fun s (_ : Unit) s' => Heap.copyBytes src dst count s = some s') (fun _ => B) := by
    refine Bytes.AuthPres.of_step (fun _ a hB => hNoOwned a hB) ?_
    intro h F s hA hd hm hi x s'' hx _ _ _ _ _ base hEx _
    obtain ⟨s', hr, _, _, _, _, _, hauth⟩ := hrun h F s hA hd hm hi
    obtain rfl : s'' = s' := Option.some.inj (hx.symm.trans hr)
    exact hauth base hEx
  exact ispec_checkedModify (Bytes.LocalOp.upClose hLocal hAuth)

theorem iexists_upClose_sep {A B : BasePtr → Fragment → Prop} :
    ((iexists fun b => upClose (A b)) ∗ (iexists fun b => upClose (B b))) ⊢
      iexists fun bb : BasePtr × BasePtr => upClose (Bytes.sep (A bb.1) (B bb.2)) := by
  rintro h ⟨h₁, h₂, hd, rfl, ⟨b₁, H₁⟩, ⟨b₂, H₂⟩⟩
  exact ⟨(b₁, b₂), sep_upClose _ ⟨h₁, h₂, hd, rfl, H₁, H₂⟩⟩

theorem upClose_sep_iexists {A B : BasePtr → Fragment → Prop} :
    (iexists fun bb : BasePtr × BasePtr => upClose (Bytes.sep (A bb.1) (B bb.2))) ⊢
      ((iexists fun b => upClose (A b)) ∗ (iexists fun b => upClose (B b))) := by
  rintro h ⟨bb, H⟩
  obtain ⟨h₁, h₂, hd, rfl, H₁, H₂⟩ := upClose_sep _ H
  exact ⟨h₁, h₂, hd, rfl, ⟨bb.1, H₁⟩, ⟨bb.2, H₂⟩⟩

/-- A range whose element bytes satisfy `valid`, shared `depth` times: `p.readable depth vs`,
`p.range depth vs` (`↦*` for depth `0`) and `p ↦?* vs` are instances, definitionally. -/
def RawPtr.rangeWith {T V : Type} [Pointee T] (valid : V → Vector Byte (Pointee.repr (T := T)).size → Prop)
    (p : RawPtr T) (depth : Nat) (values : List V) : IProp :=
  iexists fun bptr : BasePtr =>
    upClose (Bytes.rangeWith (Pointee.repr (T := T)) valid p bptr (listVec values) depth)

theorem RawPtr.readable_eq_rangeWith {T : Type} [Pointee T] (p : RawPtr T) (d : Nat) (vs : List T) :
    p.readable d vs =
      p.rangeWith (fun v bytes => (Pointee.repr (T := T)).decode bytes = some v) d vs := rfl

theorem RawPtr.range_eq_rangeWith {T : Type} [Pointee T] (p : RawPtr T) (d : Nat) (vs : List T) :
    p.range d vs = p.rangeWith (Pointee.repr (T := T)).encode d vs := rfl

theorem RawPtr.uninitRange_eq_rangeWith {T : Type} [Pointee T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) :
    (p ↦?* vs) = p.rangeWith (MaybeUninit.Decodes (Pointee.repr (T := T))) 0 vs := rfl

/-! ## Pure facts of the copies -/

/-- In every heap, the `j`-th element of a range and the `i`-th element of a separate exclusive range
are aligned, and the `n` elements from them don't overlap. -/
theorem copy_sep.facts {T V : Type} [Pointee T] [Pointee.Sized T]
    (valid : V → Vector Byte (Pointee.repr (T := T)).size → Prop) (src dst : RawPtr T)
    (xs : List V) (ys : List (MaybeUninit T)) (d j i n : Nat) (hj : j + n ≤ xs.length)
    (hi : i + n ≤ ys.length) (hxs : 0 < xs.length) (hys : 0 < ys.length) :
    RealEntails (src.rangeWith valid d xs ∗ dst ↦?* ys)
      (⌜(Pointee.repr (T := T)).align.val ∣ (src.elem j).address.val ∧
          (Pointee.repr (T := T)).align.val ∣ (dst.elem i).address.val ∧
          ((src.elem j).address.val + n * (Pointee.repr (T := T)).size ≤ (dst.elem i).address.val ∨
            (dst.elem i).address.val + n * (Pointee.repr (T := T)).size ≤
              (src.elem j).address.val)⌝ ∗
        src.rangeWith valid d xs ∗ dst ↦?* ys) := by
  refine RealEntails.of_matches fun s h hinv hm hP => (sep_pure_l _ _ h).mpr ⟨?_, hP⟩
  obtain ⟨h₁, h₂, hd, rfl, ⟨bS, a, ha, hsa⟩, ⟨bD, b, hb, hsb⟩⟩ := hP
  obtain ⟨hm₁, hm₂⟩ := (Fragment.matches_union _ _ _).mp hm
  have hma := Fragment.matches_of_subheap hsa hm₁
  have hmb := Fragment.matches_of_subheap hsb hm₂
  have hab : a.Disjoint b := by
    obtain ⟨r₁, _, rfl⟩ := PartialCommMonoid.subheap_iff.mp hsa
    obtain ⟨r₂, _, rfl⟩ := PartialCommMonoid.subheap_iff.mp hsb
    exact (Fragment.disjoint_union_right.mp (Fragment.disjoint_union_left.mp hd).1).1
  have hsize := Pointee.Sized.pos (T := T)
  have boundS := Bytes.rangeWith_bound _ valid src bS (listVec xs) d hxs hsize a s ha hma hinv
  have boundD := Bytes.rangeWith_bound _ _ dst bD (listVec ys) 0 hys hsize b s hb hmb hinv
  obtain ⟨dsS, hlS, -, hloS, halS, rfl⟩ := (Bytes.rangeWith_iff_list _ _ _ _ _ _ _).mp ha
  obtain ⟨dsD, hlD, -, hloD, halD, rfl⟩ := (Bytes.rangeWith_iff_list _ _ _ _ _ _ _).mp hb
  have mj := Nat.mul_le_mul_right (Pointee.repr (T := T)).size hj
  have mi := Nat.mul_le_mul_right (Pointee.repr (T := T)).size hi
  rw [Nat.add_mul] at mj mi
  have hsj := RawPtr.elem_address src j (by omega)
  have hdi := RawPtr.elem_address dst i (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [hsj]; exact Nat.dvd_add halS (Repr.aligned_stride _ j)
  · rw [hdi]; exact Nat.dvd_add halD (Repr.aligned_stride _ i)
  · have := Bytes.nonoverlap_of_cells hinv hma hmb hab (j * (Pointee.repr (T := T)).size)
      (i * (Pointee.repr (T := T)).size) (n * (Pointee.repr (T := T)).size)
      (by simp; rw [hlS]; omega) (by simp; rw [hlD]; omega)
    rw [hsj, hdi]
    simp only [RawPtr.offsetFrom] at this
    omega

/-- In every heap, the `j`-th and `i`-th elements of a range are aligned. -/
theorem copy_within.facts {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (j i : Nat) (hj : j ≤ vs.length) (hi : i ≤ vs.length)
    (hvs : 0 < vs.length) :
    RealEntails (p ↦?* vs)
      (⌜(Pointee.repr (T := T)).align.val ∣ (p.elem j).address.val ∧
          (Pointee.repr (T := T)).align.val ∣ (p.elem i).address.val⌝ ∗ p ↦?* vs) := by
  refine RealEntails.of_matches fun s h hinv hm hP => (sep_pure_l _ _ h).mpr ⟨?_, hP⟩
  obtain ⟨b, a, ha, hsa⟩ := hP
  have hma := Fragment.matches_of_subheap hsa hm
  have bound := Bytes.rangeWith_bound _ _ p b (listVec vs) 0 hvs Pointee.Sized.pos a s ha hma hinv
  obtain ⟨_, _, _, hal, _⟩ := ha
  have mj := Nat.mul_le_mul_right (Pointee.repr (T := T)).size hj
  have mi := Nat.mul_le_mul_right (Pointee.repr (T := T)).size hi
  refine ⟨?_, ?_⟩
  · rw [RawPtr.elem_address p j (by omega)]
    exact Nat.dvd_add hal (Repr.aligned_stride _ j)
  · rw [RawPtr.elem_address p i (by omega)]
    exact Nat.dvd_add hal (Repr.aligned_stride _ i)


/-! ## `ptr::copy` and `ptr::copy_nonoverlapping` between separate ranges -/

/-- `copy(src.elem j, dst.elem i, count)` from a range whose element bytes satisfy `valid` (at any
depth: it is only read) into a separate possibly uninitialized range: the elements `[i, i + count)`
of the destination become the elements `[j, j + count)` of the source, through `f` (`hf`: the
bytes which satisfy `valid x` describe `f x`). The generic form of the specifications below. -/
theorem core.ptr.copy.spec_rangeWith {T V : Type} [Pointee T] [Pointee.Sized T]
    (valid : V → Vector Byte (Pointee.repr (T := T)).size → Prop) (f : V → MaybeUninit T)
    (hf : ∀ v bytes, valid v bytes → MaybeUninit.Decodes (Pointee.repr (T := T)) (f v) bytes)
    (src dst : RawPtr T) (d : Nat) (xs : List V) (ys : List (MaybeUninit T)) (j i : Nat)
    (count : Usize) (hj : j + count.val ≤ xs.length) (hi : i + count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.rangeWith valid d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy (src.elem j) (dst.elem i) count
    ⦃ src.rangeWith valid d xs ∗
        dst ↦?* (ys.take i ++ ((xs.drop j).take count.val).map f ++ ys.drop (i + count.val)) ⦄ := by
  refine ispec_realEntails_pre (copy_sep.facts valid src dst xs ys d j i count.val hj hi hxs hys) ?_
  refine ispec_ipure.mpr fun ⟨hal₁, hal₂, _⟩ => ?_
  unfold core.ptr.copy
  simp only [RawPtr.byteCount, hfits, ite_true, bind_tc_ok, hal₁, hal₂, and_self]
  refine ispec_conseq (ispec_exists.mpr fun bb => ?_) iexists_upClose_sep
    (fun _ => upClose_sep_iexists)
  exact ispec_conseq (ispec_copyBytes
      (fun _ h => NoOwned.sep (fun _ h => Bytes.NoOwned_rangeWith h)
        (fun _ h => Bytes.NoOwned_rangeWith h) h)
      (Bytes.copy_sep.run valid f hf src dst bb.1 bb.2 xs ys d j i count.val hj hi hxs hys
        Pointee.Sized.pos))
    (entails_refl _) (fun _ _ hB => ⟨bb, hB⟩)

/-- `copy_nonoverlapping(src.elem j, dst.elem i, count)`: as `core.ptr.copy.spec_rangeWith` (the
two ranges, being separate, don't overlap in any heap). -/
theorem core.ptr.copy_nonoverlapping.spec_rangeWith {T V : Type} [Pointee T] [Pointee.Sized T]
    (valid : V → Vector Byte (Pointee.repr (T := T)).size → Prop) (f : V → MaybeUninit T)
    (hf : ∀ v bytes, valid v bytes → MaybeUninit.Decodes (Pointee.repr (T := T)) (f v) bytes)
    (src dst : RawPtr T) (d : Nat) (xs : List V) (ys : List (MaybeUninit T)) (j i : Nat)
    (count : Usize) (hj : j + count.val ≤ xs.length) (hi : i + count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.rangeWith valid d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping (src.elem j) (dst.elem i) count
    ⦃ src.rangeWith valid d xs ∗
        dst ↦?* (ys.take i ++ ((xs.drop j).take count.val).map f ++ ys.drop (i + count.val)) ⦄ := by
  refine ispec_realEntails_pre (copy_sep.facts valid src dst xs ys d j i count.val hj hi hxs hys) ?_
  refine ispec_ipure.mpr fun ⟨_, _, hno⟩ => ?_
  unfold core.ptr.copy_nonoverlapping
  simp only [RawPtr.byteCount, hfits, ite_true, bind_tc_ok, hno]
  exact core.ptr.copy.spec_rangeWith valid f hf src dst d xs ys j i count hj hi hxs hys hfits

/-- `copy_nonoverlapping` from a readable range (for instance a table exposed by `as_ptr`, or the
bytes of a value exposed by `from_ref`, at any depth) into a possibly uninitialized range. -/
@[step]
theorem core.ptr.copy_nonoverlapping.spec_readable {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (d : Nat) (xs : List T) (ys : List (MaybeUninit T)) (j i : Nat)
    (count : Usize) (hj : j + count.val ≤ xs.length) (hi : i + count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.readable d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping (src.elem j) (dst.elem i) count
    ⦃ src.readable d xs ∗ dst ↦?* (ys.take i ++
        ((xs.drop j).take count.val).map (fun v => ⟨some v⟩) ++ ys.drop (i + count.val)) ⦄ :=
  core.ptr.copy_nonoverlapping.spec_rangeWith _ (fun v => ⟨some v⟩)
    (fun _ _ h => (MaybeUninit.decodes_some _ _ _).mpr h) src dst d xs ys j i count hj hi hxs hys
    hfits

/-- `copy_nonoverlapping` from a range of values (`src.range d xs`; `src ↦* xs` for `d = 0`). -/
theorem core.ptr.copy_nonoverlapping.spec_range {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (d : Nat) (xs : List T) (ys : List (MaybeUninit T)) (j i : Nat)
    (count : Usize) (hj : j + count.val ≤ xs.length) (hi : i + count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.range d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping (src.elem j) (dst.elem i) count
    ⦃ src.range d xs ∗ dst ↦?* (ys.take i ++
        ((xs.drop j).take count.val).map (fun v => ⟨some v⟩) ++ ys.drop (i + count.val)) ⦄ :=
  core.ptr.copy_nonoverlapping.spec_rangeWith _ (fun v => ⟨some v⟩)
    (fun _ _ h => (MaybeUninit.decodes_some _ _ _).mpr ((Pointee.repr (T := T)).encode_decode _ _ h))
    src dst d xs ys j i count hj hi hxs hys hfits

/-- `copy_nonoverlapping` from a possibly uninitialized range: the elements are copied as they are
(an uninitialized element gives an uninitialized element). -/
theorem core.ptr.copy_nonoverlapping.spec_uninit {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (xs ys : List (MaybeUninit T)) (j i : Nat)
    (count : Usize) (hj : j + count.val ≤ xs.length) (hi : i + count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src ↦?* xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping (src.elem j) (dst.elem i) count
    ⦃ src ↦?* xs ∗ dst ↦?* (ys.take i ++ (xs.drop j).take count.val ++ ys.drop (i + count.val)) ⦄ := by
  have := core.ptr.copy_nonoverlapping.spec_rangeWith (MaybeUninit.Decodes _) (fun v => v)
    (fun _ _ h => h) src dst 0 xs ys j i count hj hi hxs hys hfits
  simp only [List.map_id'] at this
  rw [RawPtr.uninitRange_eq_rangeWith src xs]
  exact this

/-- `copy` between separate ranges, from a readable range. -/
theorem core.ptr.copy.spec_readable {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (d : Nat) (xs : List T) (ys : List (MaybeUninit T)) (j i : Nat)
    (count : Usize) (hj : j + count.val ≤ xs.length) (hi : i + count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.readable d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy (src.elem j) (dst.elem i) count
    ⦃ src.readable d xs ∗ dst ↦?* (ys.take i ++
        ((xs.drop j).take count.val).map (fun v => ⟨some v⟩) ++ ys.drop (i + count.val)) ⦄ :=
  core.ptr.copy.spec_rangeWith _ (fun v => ⟨some v⟩)
    (fun _ _ h => (MaybeUninit.decodes_some _ _ _).mpr h) src dst d xs ys j i count hj hi hxs hys
    hfits

/-! ## `ptr::copy` within a range (`memmove`) -/

/-- `copy(p.elem j, p.elem i, count)` within a possibly uninitialized range, the two parts possibly
overlapping: the elements `[i, i + count)` become the elements `[j, j + count)` of the range before
the copy (snapshot semantics of `memmove`). Uninitialized elements are copied as uninitialized. -/
@[step]
theorem core.ptr.copy.spec_uninit_within {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (j i : Nat) (count : Usize) (hj : j + count.val ≤ vs.length)
    (hi : i + count.val ≤ vs.length) (hvs : 0 < vs.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ p ↦?* vs ⦄ core.ptr.copy (p.elem j) (p.elem i) count
    ⦃ p ↦?* (vs.take i ++ (vs.drop j).take count.val ++ vs.drop (i + count.val)) ⦄ := by
  refine ispec_realEntails_pre (copy_within.facts p vs j i (by omega) (by omega) hvs) ?_
  refine ispec_ipure.mpr fun ⟨hal₁, hal₂⟩ => ?_
  unfold core.ptr.copy
  simp only [RawPtr.byteCount, hfits, ite_true, bind_tc_ok, hal₁, hal₂, and_self]
  refine ispec_exists.mpr fun b => ?_
  exact ispec_conseq (ispec_copyBytes (fun _ h => Bytes.NoOwned_rangeWith h)
      (Bytes.copy_within.run p b vs j i count.val hj hi hvs Pointee.Sized.pos))
    (entails_refl _) (fun _ _ hB => ⟨b, hB⟩)


/-! ## `ptr::write_bytes` -/

theorem List.take_set_replicate {α : Type} (ys : List α) (i n : Nat) (x : α) (hi : i < ys.length) :
    (ys.set i x).take (i + 1) ++ List.replicate n x ++ (ys.set i x).drop (i + 1 + n) =
      ys.take i ++ List.replicate (n + 1) x ++ ys.drop (i + (n + 1)) := by
  rw [List.set_eq_take_cons_drop _ hi]
  have hl : (ys.take i).length = i := by simp; omega
  rw [List.take_append, List.drop_append, hl]
  rw [List.drop_eq_nil_of_le (by omega : (ys.take i).length ≤ i + 1 + n)]
  simp [List.replicate_succ, show i + 1 + n - i = n + 1 by omega, List.drop_drop, List.take_take,
    show i + (n + 1) = i + 1 + n by omega]

/-- Sequencing, without frame. -/
theorem ispec_seq {α β : Type} {P : IPre} {m : Result α} {R : IPost α} {k : α → Result β}
    {Q : IPost β} (h₁ : ispec P m R) (h₂ : ∀ v, ispec (R v) (k v) Q) :
    ispec P (Aeneas.Std.bind m k) Q :=
  ispec_bind h₁ (entails_of_eq (sep_emp_r_eq _).symm) (fun v => by rw [sep_emp_r_eq]; exact h₂ v)

/-- The loop of `write_bytes`: `n` writes of the byte `b`, from the `i`-th element of a possibly
uninitialized range of bytes on. -/
theorem MutRawPtr.writeBytes.spec_uninit (p : MutRawPtr U8) (b : U8) :
    ∀ (n i : Nat) (ys : List (MaybeUninit U8)), i + n ≤ ys.length →
      ⦃ p ↦?* ys ⦄ MutRawPtr.writeBytes (p.elem i) b n
      ⦃ p ↦?* (ys.take i ++ List.replicate n ⟨some b⟩ ++ ys.drop (i + n)) ⦄
  | 0, i, ys, _ => by
    unfold MutRawPtr.writeBytes
    exact ispec_ok () (entails_of_eq (by simp))
  | n + 1, i, ys, h => by
    unfold MutRawPtr.writeBytes
    refine ispec_seq (MutRawPtr.write.spec_uninit p ys i b (by omega)) fun _ => ?_
    split
    · rename_i hn
      subst hn
      refine ispec_ok () (entails_of_eq ?_)
      rw [List.set_eq_take_cons_drop _ (by omega)]
      simp
    · refine ispec_seq (RawPtr.add.spec_uninit p (ys.set i ⟨some b⟩) i 1#usize (by simp; omega)
        (by simp; omega)) fun q => ?_
      refine ispec_ipure.mpr fun hq => ?_
      subst hq
      refine ispec_conseq (MutRawPtr.writeBytes.spec_uninit p b n (i + 1) (ys.set i ⟨some b⟩)
        (by simp; omega)) (entails_refl _) (fun _ => entails_of_eq ?_)
      rw [List.take_set_replicate _ _ _ _ (by omega)]

/-- `write_bytes(p.elem i, b, count)` on a possibly uninitialized range of bytes: the elements
`[i, i + count)` become `b`. -/
@[step]
theorem core.ptr.write_bytes.spec_uninit (p : MutRawPtr U8) (ys : List (MaybeUninit U8)) (i : Nat)
    (b : U8) (count : Usize) (hi : i + count.val ≤ ys.length)
    (hfits : (count.val : Int) ≤ IScalar.cMax .Isize) :
    ⦃ p ↦?* ys ⦄ core.ptr.write_bytes (p.elem i) b count
    ⦃ p ↦?* (ys.take i ++ List.replicate count.val ⟨some b⟩ ++ ys.drop (i + count.val)) ⦄ := by
  unfold core.ptr.write_bytes
  have h₁ : (Pointee.repr (T := U8)).size = 1 := rfl
  have h₂ : (Pointee.repr (T := U8)).align.val = 1 := rfl
  simp only [RawPtr.byteCount, h₁, Nat.mul_one, hfits, ite_true, bind_tc_ok, h₂, Nat.one_dvd,
    RawPtr.cast_self]
  exact MutRawPtr.writeBytes.spec_uninit p b count.val i ys hi

/-! ## At the start of the ranges

The programs use the pointer of a range itself for its first element (`copy(src, buffer, n)`,
`write_bytes(buffer, b, n)`, ...), which is `p.elem 0` only up to `RawPtr.elem_zero`: these are the
specifications above with the index `0`, at `p`. `step` doesn't backtrack between the
specifications whose programs have the same shape (see `UninitSpecs.lean`): for each shape, only
the variant on the same assertions as the `@[step]` specification on `p.elem i` is `@[step]`
(`copy_nonoverlapping.spec_readable_{src_head,dst_head,head}`, `copy.spec_uninit_within_{dst,src}_head`,
`write_bytes.spec_uninit_head`); the other ones are used with `step with`. -/

/-- `copy_nonoverlapping` from the start of a readable range into the `i`-th element of a `↦?*` range. -/
@[step]
theorem core.ptr.copy_nonoverlapping.spec_readable_src_head {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (d : Nat) (xs : List T) (ys : List (MaybeUninit T)) (i : Nat)
    (count : Usize) (hj : count.val ≤ xs.length) (hi : i + count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.readable d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping src (dst.elem i) count
    ⦃ src.readable d xs ∗ dst ↦?* (ys.take i ++ (xs.take count.val).map (fun v => ⟨some v⟩) ++ ys.drop (i + count.val)) ⦄ := by
  simpa only [RawPtr.elem_zero, List.drop_zero, List.take_zero, List.nil_append, Nat.zero_add]
    using core.ptr.copy_nonoverlapping.spec_readable src dst d xs ys 0 i count (by omega) (by omega)
      hxs hys hfits

/-- `copy_nonoverlapping` from the `j`-th element of a readable range to the start of a `↦?*` range. -/
@[step]
theorem core.ptr.copy_nonoverlapping.spec_readable_dst_head {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (d : Nat) (xs : List T) (ys : List (MaybeUninit T)) (j : Nat)
    (count : Usize) (hj : j + count.val ≤ xs.length) (hi : count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.readable d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping (src.elem j) dst count
    ⦃ src.readable d xs ∗ dst ↦?* (((xs.drop j).take count.val).map (fun v => ⟨some v⟩) ++ ys.drop count.val) ⦄ := by
  simpa only [RawPtr.elem_zero, List.drop_zero, List.take_zero, List.nil_append, Nat.zero_add]
    using core.ptr.copy_nonoverlapping.spec_readable src dst d xs ys j 0 count (by omega) (by omega)
      hxs hys hfits

/-- `copy_nonoverlapping` from the start of a readable range to the start of a `↦?*` range. -/
@[step]
theorem core.ptr.copy_nonoverlapping.spec_readable_head {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (d : Nat) (xs : List T) (ys : List (MaybeUninit T))
    (count : Usize) (hj : count.val ≤ xs.length) (hi : count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.readable d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping src dst count
    ⦃ src.readable d xs ∗ dst ↦?* ((xs.take count.val).map (fun v => ⟨some v⟩) ++ ys.drop count.val) ⦄ := by
  simpa only [RawPtr.elem_zero, List.drop_zero, List.take_zero, List.nil_append, Nat.zero_add]
    using core.ptr.copy_nonoverlapping.spec_readable src dst d xs ys 0 0 count (by omega) (by omega)
      hxs hys hfits

/-- `copy_nonoverlapping` from the start of a range of values into the `i`-th element of a `↦?*` range. -/
theorem core.ptr.copy_nonoverlapping.spec_range_src_head {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (d : Nat) (xs : List T) (ys : List (MaybeUninit T)) (i : Nat)
    (count : Usize) (hj : count.val ≤ xs.length) (hi : i + count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.range d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping src (dst.elem i) count
    ⦃ src.range d xs ∗ dst ↦?* (ys.take i ++ (xs.take count.val).map (fun v => ⟨some v⟩) ++ ys.drop (i + count.val)) ⦄ := by
  simpa only [RawPtr.elem_zero, List.drop_zero, List.take_zero, List.nil_append, Nat.zero_add]
    using core.ptr.copy_nonoverlapping.spec_range src dst d xs ys 0 i count (by omega) (by omega)
      hxs hys hfits

/-- `copy_nonoverlapping` from the `j`-th element of a range of values to the start of a `↦?*` range. -/
theorem core.ptr.copy_nonoverlapping.spec_range_dst_head {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (d : Nat) (xs : List T) (ys : List (MaybeUninit T)) (j : Nat)
    (count : Usize) (hj : j + count.val ≤ xs.length) (hi : count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.range d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping (src.elem j) dst count
    ⦃ src.range d xs ∗ dst ↦?* (((xs.drop j).take count.val).map (fun v => ⟨some v⟩) ++ ys.drop count.val) ⦄ := by
  simpa only [RawPtr.elem_zero, List.drop_zero, List.take_zero, List.nil_append, Nat.zero_add]
    using core.ptr.copy_nonoverlapping.spec_range src dst d xs ys j 0 count (by omega) (by omega)
      hxs hys hfits

/-- `copy_nonoverlapping` from the start of a range of values to the start of a `↦?*` range. -/
theorem core.ptr.copy_nonoverlapping.spec_range_head {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (d : Nat) (xs : List T) (ys : List (MaybeUninit T))
    (count : Usize) (hj : count.val ≤ xs.length) (hi : count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src.range d xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping src dst count
    ⦃ src.range d xs ∗ dst ↦?* ((xs.take count.val).map (fun v => ⟨some v⟩) ++ ys.drop count.val) ⦄ := by
  simpa only [RawPtr.elem_zero, List.drop_zero, List.take_zero, List.nil_append, Nat.zero_add]
    using core.ptr.copy_nonoverlapping.spec_range src dst d xs ys 0 0 count (by omega) (by omega)
      hxs hys hfits

/-- `copy_nonoverlapping` from the start of a possibly uninitialized range into the `i`-th element of a `↦?*` range. -/
theorem core.ptr.copy_nonoverlapping.spec_uninit_src_head {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (xs : List (MaybeUninit T)) (ys : List (MaybeUninit T)) (i : Nat)
    (count : Usize) (hj : count.val ≤ xs.length) (hi : i + count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src ↦?* xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping src (dst.elem i) count
    ⦃ src ↦?* xs ∗ dst ↦?* (ys.take i ++ xs.take count.val ++ ys.drop (i + count.val)) ⦄ := by
  simpa only [RawPtr.elem_zero, List.drop_zero, List.take_zero, List.nil_append, Nat.zero_add]
    using core.ptr.copy_nonoverlapping.spec_uninit src dst xs ys 0 i count (by omega) (by omega)
      hxs hys hfits

/-- `copy_nonoverlapping` from the `j`-th element of a possibly uninitialized range to the start of a `↦?*` range. -/
theorem core.ptr.copy_nonoverlapping.spec_uninit_dst_head {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (xs : List (MaybeUninit T)) (ys : List (MaybeUninit T)) (j : Nat)
    (count : Usize) (hj : j + count.val ≤ xs.length) (hi : count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src ↦?* xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping (src.elem j) dst count
    ⦃ src ↦?* xs ∗ dst ↦?* ((xs.drop j).take count.val ++ ys.drop count.val) ⦄ := by
  simpa only [RawPtr.elem_zero, List.drop_zero, List.take_zero, List.nil_append, Nat.zero_add]
    using core.ptr.copy_nonoverlapping.spec_uninit src dst xs ys j 0 count (by omega) (by omega)
      hxs hys hfits

/-- `copy_nonoverlapping` from the start of a possibly uninitialized range to the start of a `↦?*` range. -/
theorem core.ptr.copy_nonoverlapping.spec_uninit_head {T : Type} [Pointee T] [Pointee.Sized T]
    (src dst : RawPtr T) (xs : List (MaybeUninit T)) (ys : List (MaybeUninit T))
    (count : Usize) (hj : count.val ≤ xs.length) (hi : count.val ≤ ys.length)
    (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ src ↦?* xs ∗ dst ↦?* ys ⦄
      core.ptr.copy_nonoverlapping src dst count
    ⦃ src ↦?* xs ∗ dst ↦?* (xs.take count.val ++ ys.drop count.val) ⦄ := by
  simpa only [RawPtr.elem_zero, List.drop_zero, List.take_zero, List.nil_append, Nat.zero_add]
    using core.ptr.copy_nonoverlapping.spec_uninit src dst xs ys 0 0 count (by omega) (by omega)
      hxs hys hfits

/-- `ptr::copy` within a range, to its start. -/
@[step]
theorem core.ptr.copy.spec_uninit_within_dst_head {T : Type} [Pointee T] [Pointee.Sized T]
    (p : RawPtr T) (vs : List (MaybeUninit T)) (j : Nat) (count : Usize)
    (hj : j + count.val ≤ vs.length) (hi : count.val ≤ vs.length) (hvs : 0 < vs.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ p ↦?* vs ⦄ core.ptr.copy (p.elem j) p count
    ⦃ p ↦?* ((vs.drop j).take count.val ++ vs.drop count.val) ⦄ := by
  simpa only [RawPtr.elem_zero, List.take_zero, List.nil_append, Nat.zero_add] using
    core.ptr.copy.spec_uninit_within p vs j 0 count hj (by omega) hvs hfits

/-- `ptr::copy` within a range, from its start. -/
@[step]
theorem core.ptr.copy.spec_uninit_within_src_head {T : Type} [Pointee T] [Pointee.Sized T]
    (p : RawPtr T) (vs : List (MaybeUninit T)) (i : Nat) (count : Usize)
    (hj : count.val ≤ vs.length) (hi : i + count.val ≤ vs.length) (hvs : 0 < vs.length)
    (hfits : ((count.val * (Pointee.repr (T := T)).size : Nat) : Int) ≤ IScalar.cMax .Isize) :
    ⦃ p ↦?* vs ⦄ core.ptr.copy p (p.elem i) count
    ⦃ p ↦?* (vs.take i ++ vs.take count.val ++ vs.drop (i + count.val)) ⦄ := by
  simpa only [RawPtr.elem_zero, List.drop_zero] using
    core.ptr.copy.spec_uninit_within p vs 0 i count (by omega) hi hvs hfits

/-- `write_bytes` from the start of a range of bytes. -/
@[step]
theorem core.ptr.write_bytes.spec_uninit_head (p : MutRawPtr U8) (ys : List (MaybeUninit U8))
    (b : U8) (count : Usize) (hi : count.val ≤ ys.length)
    (hfits : (count.val : Int) ≤ IScalar.cMax .Isize) :
    ⦃ p ↦?* ys ⦄ core.ptr.write_bytes p b count
    ⦃ p ↦?* (List.replicate count.val ⟨some b⟩ ++ ys.drop count.val) ⦄ := by
  simpa only [RawPtr.elem_zero, List.take_zero, List.nil_append, Nat.zero_add] using
    core.ptr.write_bytes.spec_uninit p ys 0 b count (by omega) hfits

/-! ## The bytes of an unsigned integer -/

theorem List.mapM_some_getElem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {l : List β}, xs.mapM f = some l →
      ∀ k (h₁ : k < xs.length) (h₂ : k < l.length), f xs[k] = some l[k]
  | [], _, _, _, h₁, _ => absurd h₁ (Nat.not_lt_zero _)
  | x :: xs, l, h, k, h₁, h₂ => by
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hr : xs.mapM f with
      | none => simp [hx, hr] at h
      | some ys =>
        simp only [hx, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        cases k with
        | zero => simpa using hx
        | succ k => simpa using List.mapM_some_getElem hr k (by simpa using h₁) (by simpa using h₂)

/-- A byte decodes, as a `u8`, to its numerical value. -/
theorem Repr.decodeLE_u8 (x : U8) : (Repr.decodeLE 8 [x]).map (UScalar.mk (ty := .U8)) = some x := by
  unfold Repr.decodeLE
  simp only [List.length_singleton, Nat.mul_one, dite_true, Option.map_some, Option.some.injEq]
  cases x with
  | mk b =>
  congr 1
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_cast]
  rw [BitVec.fromLEBytes_getElem _ _ (by simp; exact hi)]
  have h₁ : i / 8 = 0 := by omega
  have h₂ : i % 8 = i := by omega
  simp only [h₁, h₂]
  show _root_.Byte.testBit b i = b[i]
  rw [BitVec.getElem_eq_testBit_toNat]

/-- A readable view of an unsigned integer `v` at `p` is a readable view of its little-endian bytes
at `p.cast U8` (read-only: the bytes decode, as `u8`, to the bytes of `v`, but may be pointer
bytes). For instance, the bytes of a `u64` exposed by `from_ref`. -/
theorem RawPtr.readable_uscalar_toLEBytes {ty : UScalarTy} (p : RawPtr (UScalar ty)) (d : Nat)
    (v : UScalar ty) :
    p.readable d [v] ⊢ (p.cast U8).readable d (v.bv.toLEBytes.map UScalar.mk) := by
  rintro h ⟨bptr, a, ha, hsub⟩
  refine ⟨bptr, a, ?_, hsub⟩
  rw [Bytes.readableRange_eq_rangeWith] at ha ⊢
  obtain ⟨ds, hl, hv, hlo, _, rfl⟩ := (Bytes.rangeWith_iff_list _ _ _ _ _ _ _).mp ha
  obtain ⟨bytes, rfl⟩ := List.length_eq_one_iff.mp hl
  have hdec : (bytes.toList.mapM Byte.numeric >>= fun l =>
      (Repr.decodeLE ty.numBits l).map UScalar.mk) = some v := hv 0 (by simp) (by simp)
  cases hm : bytes.toList.mapM Byte.numeric with
  | none => simp [hm] at hdec
  | some l =>
    simp only [hm, Option.bind_eq_bind, Option.bind_some] at hdec
    have hl' := Repr.uscalar_encode_decode ty l v hdec
    rw [hl']
    have hlen : l.length = bytes.toList.length := by
      rw [← hl']; simp [BitVec.toLEBytes_length]
      have := ty.numBits_mod_eight
      change (ty.numBits + 7) / 8 = ty.numBits / 8
      omega
    refine (Bytes.rangeWith_iff_list _ _ _ _ _ _ _).mpr
      ⟨bytes.toList.map (fun b => (⟨#[b], rfl⟩ : Vector Byte (Pointee.repr (T := U8)).size)),
        by simp [hlen], fun k hk hk' => ?_, hlo, Nat.one_dvd _, ?_⟩
    · simp only [List.getElem_map]
      have hn := List.mapM_some_getElem hm k (by simpa using hk') hk
      show ([bytes.toList[k]'(by simpa using hk')].mapM Byte.numeric >>= fun l =>
        (Repr.decodeLE UScalarTy.U8.numBits l).map (UScalar.mk (ty := .U8))) = some l[k]
      simp only [List.mapM_cons, List.mapM_nil, hn, Option.pure_def, Option.bind_eq_bind,
        Option.bind_some]
      exact Repr.decodeLE_u8 _
    · have hc : Bytes.chunkBytes (bytes.toList.map
          (fun b => (⟨#[b], rfl⟩ : Vector Byte (Pointee.repr (T := U8)).size))) = bytes.toList := by
        simp only [Bytes.chunkBytes, List.flatMap_map]
        induction bytes.toList with
        | nil => rfl
        | cons x xs ih => simp only [List.flatMap_cons, ih]; rfl
      rw [hc]
      simp [Bytes.chunkBytes, RawPtr.cast, RawPtr.offsetFrom]

/-! ## Sizes, for the side conditions (`count * size ≤ isize::MAX`)

The byte counts of the copies and of `write_bytes` must fit `isize` (the side conditions `hfits`):
`IScalar.cMax .Isize` is evaluated by `simp` and `scalar_tac`. The sizes of the scalars, the bytes
and the arrays (`Pointee.size_uscalar`, `Pointee.size_u8`, ..., in `CastSpecs.lean`) are in the simp
sets of `scalar_tac` and of `step`'s preconditions, but not `@[simp]`. -/

@[simp, scalar_tac_simps]
theorem IScalar.cMax_Isize : IScalar.cMax .Isize = 2147483647 := rfl

end Aeneas.Std
