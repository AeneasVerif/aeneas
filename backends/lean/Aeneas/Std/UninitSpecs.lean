/- Separation-logic specifications for possibly uninitialized ranges (`p ↦?* values`). -/
module
public import Aeneas.Std.RawPtrSpecs
public import Aeneas.Std.Core.MaybeUninit
public import Aeneas.Std.Core.RawPtrOps
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Core.RawPtrOps
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
@[expose] public section

/-! # Possibly uninitialized ranges: `p ↦?* values`

`p ↦?* values` (for `p : RawPtr T` and `values : List (MaybeUninit T)`) owns, exclusively (depth
`0`, so that they can be written), one encoding-sized chunk of cells per element, one after the
other from `p` on, in a single block:
- for `⟨some v⟩`, the bytes of the chunk *decode* to `v` (`repr.decode bytes = some v`, as in
  `readableRange`): reading the element gives `v`;
- for `⟨none⟩`, the bytes are arbitrary (they may be uninitialized, or any leftover): the element
  can be written but not read.

Consequences of this design:
- `p ↦?* List.replicate n ⟨none⟩` is the weakest assertion of an owned writable buffer of `n`
  elements: every `p ↦?* values` (and so every `p ↦* values`) entails it (`uninitRange_forget`);
- `some` uses the decoding, not the admissible encodings (as `p.readable`, not as `p ↦*`): bytes
  copied out of a read-only exposure (which may keep the pointer bytes of a scalar) still describe
  their value. `p.readable 0 vs` and `p ↦?* vs.map (⟨some ·⟩)` are equivalent
  (`readable_eq_uninitRange`), and `p ↦* vs` entails both (`range_uninitRange`);
- writing an element (`MutRawPtr.write.spec_uninit`) makes it `⟨some v⟩`, whatever its bytes were.

Splitting a range (`uninitRange_split`) is an entailment. Merging two adjacent ranges back
(`uninitRange_merge`) is not, as the two parts could, in an arbitrary fragment, be in two blocks
with different base pointers (the same happens for `p.readable`, see `RawPtr.readable2`): it is a
`RealEntails`, an entailment in the heaps which realize the assertion, which can be used in the
pre- and postconditions of specifications (`ispec_realEntails_pre`, `ispec_realEntails_post`).

The fragment-level predicate is `Bytes.uninitRange`, an instance of `Bytes.rangeWith`: the generic
contiguous range whose element bytes satisfy a predicate (`readableRange` and
`Bytes.pointsToRange` are, definitionally, the instances for the decoding and the encodings). The
lemmas on `Bytes.rangeWith` (append, focus, bounds, pointer arithmetic) serve all three.

Specifications for `step`: the accesses (`MutRawPtr.write.spec_uninit`, `RawPtr.read.spec_uninit`)
and the pointer movements within `↦?*` (`RawPtr.add.spec_uninit`, `RawPtr.offset.spec_uninit`,
`RawPtr.sub.spec_uninit`) are `@[step]`, as is `RawPtr.ptr_cast.spec`. `step` doesn't backtrack
between the specifications whose programs have the same shape (`RawPtr.add (p.elem i) k`, ...): it
uses the first one which unifies with the program, even if its precondition can't be framed. The
pointer movements within readable ranges (`RawPtr.add.spec_readable_elem`, `RawPtr.offset.spec_readable`,
`RawPtr.sub.spec_readable`) are therefore not `@[step]`, and are used with `step with`.

The start of a range. The specifications are stated on the pointers `p.elem i` into a range. The
programs access the start of a range with the pointer of the range itself (`*buffer = c`,
`buffer.add(n)`, `copy(src, buffer, n)`, ...), which is `p.elem 0` only up to `RawPtr.elem_zero`
(a `simp` lemma): the `_head` variants are these specifications at `p`. Their programs
(`MutRawPtr.write ?p ?v`, ...) have the same shape as the specifications on other assertions
(`MutRawPtr.write.spec` on `p ↦ v`, `RawPtr.read.spec`, `RawPtr.add.spec` on `p ↦* vs`, ...), so
`MutRawPtr.write.spec_uninit_head`, `RawPtr.read.spec_uninit_head`, `RawPtr.add.spec_uninit_head`
and `RawPtr.offset.spec_readable_head` are not `@[step]` (use them with `step with`).
`RawPtr.offset.spec_uninit_head` is `@[step]`: no other `@[step]` specification of `RawPtr.offset`
is on the pointer of a range itself (`step` tries the specifications on `p.elem i` first). -/

namespace Aeneas.Std

open Aeneas.SepLogic Aeneas.Std.WP core.mem.maybe_uninit

set_option maxHeartbeats 1000000

/-! ## Possibly uninitialized values -/

/-- The bytes `bytes` describe the possibly uninitialized value `value`: they decode to it if it is
initialized (`⟨some v⟩`), and are arbitrary otherwise. -/
def MaybeUninit.Decodes {T : Type} (repr : Repr T) (value : MaybeUninit T)
    (bytes : Vector Byte repr.size) : Prop :=
  ∀ v, value.value = some v → repr.decode bytes = some v

@[simp] theorem MaybeUninit.decodes_none {T : Type} (repr : Repr T)
    (bytes : Vector Byte repr.size) : MaybeUninit.Decodes repr ⟨none⟩ bytes := by
  intro v h; cases h

@[simp] theorem MaybeUninit.decodes_some {T : Type} (repr : Repr T) (v : T)
    (bytes : Vector Byte repr.size) :
    MaybeUninit.Decodes repr ⟨some v⟩ bytes ↔ repr.decode bytes = some v := by
  constructor
  · intro h; exact h v rfl
  · rintro h w hw; cases hw; exact h

/-- `xs` refines `ys`: they have the same length, and each element initialized in `ys` is
initialized, with the same value, in `xs` (`xs` knows more). A range of `xs` entails a range of
`ys` (`uninitRange_refines`). -/
def MaybeUninit.Refines {T : Type} (xs ys : List (MaybeUninit T)) : Prop :=
  xs.length = ys.length ∧
    ∀ i (hx : i < xs.length) (hy : i < ys.length) v, ys[i].value = some v → xs[i].value = some v

namespace MaybeUninit.Refines

theorem refl {T : Type} (xs : List (MaybeUninit T)) : MaybeUninit.Refines xs xs :=
  ⟨rfl, fun _ _ _ _ h => h⟩

theorem trans {T : Type} {xs ys zs : List (MaybeUninit T)} (h₁ : MaybeUninit.Refines xs ys)
    (h₂ : MaybeUninit.Refines ys zs) : MaybeUninit.Refines xs zs :=
  ⟨h₁.1.trans h₂.1, fun i hx hz v hv => h₁.2 i hx (h₁.1 ▸ hx) v (h₂.2 i (h₁.1 ▸ hx) hz v hv)⟩

/-- Every list refines the fully uninitialized list of its length. -/
theorem replicate_none {T : Type} (xs : List (MaybeUninit T)) :
    MaybeUninit.Refines xs (List.replicate xs.length ⟨none⟩) :=
  ⟨by simp, fun i _ _ v hv => by simp at hv⟩

/-- Refinement is kept by updating both lists at the same index with the same value. -/
theorem set {T : Type} {xs ys : List (MaybeUninit T)} (h : MaybeUninit.Refines xs ys) (i : Nat)
    (a : MaybeUninit T) : MaybeUninit.Refines (xs.set i a) (ys.set i a) := by
  refine ⟨by simp [h.1], fun j hx hy v hv => ?_⟩
  simp only [List.length_set] at hx hy
  by_cases hij : i = j
  · subst hij; simp_all
  · simp only [List.getElem_set_ne hij] at hv ⊢
    exact h.2 j hx hy v hv

/-- Forgetting an element. -/
theorem set_none {T : Type} (xs : List (MaybeUninit T)) (i : Nat) :
    MaybeUninit.Refines xs (xs.set i ⟨none⟩) := by
  refine ⟨by simp, fun j hx hy v hv => ?_⟩
  by_cases hij : i = j
  · subst hij; simp at hv
  · simpa [List.getElem_set_ne hij] using hv

/-- Initializing an uninitialized element refines the list. -/
theorem set_of_none {T : Type} (xs : List (MaybeUninit T)) (i : Nat) (a : MaybeUninit T)
    (hi : ∀ h : i < xs.length, xs[i] = ⟨none⟩) : MaybeUninit.Refines (xs.set i a) xs := by
  refine ⟨by simp, fun j hx hy v hv => ?_⟩
  by_cases hij : i = j
  · subst hij; rw [hi hy] at hv; cases hv
  · simpa [List.getElem_set_ne hij] using hv

theorem append {T : Type} {xs ys xs' ys' : List (MaybeUninit T)} (h : MaybeUninit.Refines xs ys)
    (h' : MaybeUninit.Refines xs' ys') : MaybeUninit.Refines (xs ++ xs') (ys ++ ys') := by
  refine ⟨by simp [h.1, h'.1], fun i hx hy v hv => ?_⟩
  by_cases hi : i < xs.length
  · rw [List.getElem_append_left hi]
    rw [List.getElem_append_left (h.1 ▸ hi)] at hv
    exact h.2 i hi (h.1 ▸ hi) v hv
  · have e₁ := h.1
    have e₂ := h'.1
    simp only [List.length_append] at hx hy
    rw [List.getElem_append_right (by omega)]
    rw [List.getElem_append_right (by omega)] at hv
    have hv' : ys'[i - xs.length].value = some v := by
      have : i - ys.length = i - xs.length := by omega
      simpa [this] using hv
    exact h'.2 _ (by omega) (by omega) v hv'

end MaybeUninit.Refines

/-! ## Contiguous ranges whose element bytes satisfy a predicate -/

namespace Bytes

/-- `count` chunks of cells, one after the other from `p` on, in the block of base pointer `bptr`,
shared `depth` times (`0`: exclusively), whose `i`-th chunk has bytes which satisfy
`valid values[i]`. -/
def rangeWith {T V : Type} (repr : Repr T) (valid : V → Vector Byte repr.size → Prop)
    (p : RawPtr T) (bptr : BasePtr) (values : Vector V count) (depth : Nat) : Fragment → Prop :=
  fun h => ∃ data : Vector (Vector Byte repr.size) count,
    (∀ i : Fin count, valid values[i.val] data[i.val]) ∧
    block repr p bptr (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList h

theorem readableRange_eq_rangeWith {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) :
    readableRange repr p bptr values depth =
      rangeWith repr (fun v bytes => repr.decode bytes = some v) p bptr values depth := rfl

theorem pointsToRange_eq_rangeWith {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) :
    pointsToRange repr p bptr values depth = rangeWith repr repr.encode p bptr values depth := rfl

/-- A possibly uninitialized range, at the level of fragments: exclusive cells, one
encoding-sized chunk per element, whose bytes decode to the element if it is initialized (and are
arbitrary otherwise). -/
def uninitRange {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector (MaybeUninit T) count) : Fragment → Prop :=
  rangeWith repr (MaybeUninit.Decodes repr) p bptr values 0

/-- Weakening the predicate of the elements. -/
theorem rangeWith_imp {T V V' : Type} {repr : Repr T} {valid : V → Vector Byte repr.size → Prop}
    {valid' : V' → Vector Byte repr.size → Prop} {p : RawPtr T} {bptr : BasePtr} {depth n m : Nat}
    (values : Vector V n) (values' : Vector V' m) (hnm : n = m)
    (himp : ∀ i (hn : i < n) (hm : i < m) bytes, valid values[i] bytes → valid' values'[i] bytes)
    {h : Fragment} :
    rangeWith repr valid p bptr values depth h → rangeWith repr valid' p bptr values' depth h := by
  subst hnm
  rintro ⟨data, hv, hb⟩
  exact ⟨data, fun i => himp i.val i.isLt i.isLt _ (hv i), hb⟩

/-- `rangeWith_imp`, on lists. -/
theorem rangeWith_list_imp {T V V' : Type} {repr : Repr T}
    {valid : V → Vector Byte repr.size → Prop} {valid' : V' → Vector Byte repr.size → Prop}
    {p : RawPtr T} {bptr : BasePtr} {depth : Nat} (xs : List V) (ys : List V')
    (hlen : xs.length = ys.length)
    (himp : ∀ i (hx : i < xs.length) (hy : i < ys.length) bytes, valid xs[i] bytes →
      valid' ys[i] bytes) {h : Fragment} :
    rangeWith repr valid p bptr (listVec xs) depth h →
      rangeWith repr valid' p bptr (listVec ys) depth h :=
  rangeWith_imp (listVec xs) (listVec ys) hlen
    (fun i hx hy bytes hv => by simpa [listVec] using himp i hx hy bytes (by simpa [listVec] using hv))

theorem rangeWith_nil {T V : Type} {repr : Repr T} {valid : V → Vector Byte repr.size → Prop}
    {p : RawPtr T} {bptr : BasePtr} {depth : Nat} {h : Fragment} :
    rangeWith repr valid p bptr (listVec ([] : List V)) depth h ↔
      bptr.val ≤ p.address.val ∧ repr.align.val ∣ p.address.val ∧ h = ∅ := by
  constructor
  · rintro ⟨data, _, hlo, ha, rfl⟩
    refine ⟨hlo, ha, ?_⟩
    have : (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList = [] := by
      apply List.eq_nil_of_length_eq_zero; simp
    rw [this, cellsHeap_nil]
  · rintro ⟨hlo, ha, rfl⟩
    refine ⟨#v[], fun i => i.elim0, hlo, ha, ?_⟩
    simp

theorem rangeWith_singleton {T V : Type} {repr : Repr T}
    {valid : V → Vector Byte repr.size → Prop} {p : RawPtr T} {bptr : BasePtr} {depth : Nat}
    {value : V} {h : Fragment} :
    rangeWith repr valid p bptr (listVec [value]) depth h ↔
      ∃ bytes, valid value bytes ∧ block repr p bptr (bytes.map (Cell.shared depth)).toList h := by
  constructor
  · rintro ⟨data, hv, hb⟩
    refine ⟨data[0], hv ⟨0, by simp⟩, ?_⟩
    have : (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList =
        (data[0].map (Cell.shared depth)).toList := by
      obtain ⟨⟨arr⟩, harr⟩ := data
      match arr, harr with
      | [x], _ => simp [Vector.flatMap, Vector.toList]
    rwa [← this]
  · rintro ⟨bytes, hv, hb⟩
    refine ⟨#v[bytes], fun i => ?_, ?_⟩
    · obtain ⟨i, hi⟩ := i
      have : i = 0 := by simp at hi; omega
      subst this
      simpa using hv
    · have : (#v[bytes].flatMap (fun bytes => bytes.map (Cell.shared depth))).toList =
          (bytes.map (Cell.shared depth)).toList := by
        simp [Vector.flatMap, Vector.toList]
      rwa [this]

/-- A range of `xs ++ ys` is a range of `xs` and a range of `ys` after it, in the same block. -/
theorem rangeWith_append {T V : Type} (repr : Repr T) (valid : V → Vector Byte repr.size → Prop)
    (p q : RawPtr T) (bptr : BasePtr) (xs ys : List V) (d : Nat)
    (hprov : q.provenance = p.provenance)
    (hoff : q.address.val = p.address.val + xs.length * repr.size) (h : Fragment) :
    rangeWith repr valid p bptr (listVec (xs ++ ys)) d h ↔
      (rangeWith repr valid p bptr (listVec xs) d ∗ᵇ
        rangeWith repr valid q bptr (listVec ys) d) h := by
  have hcells : ∀ {n} (data : Vector (Vector Byte repr.size) n),
      (data.flatMap (fun b => b.map (Cell.shared d))).toList =
        data.toList.flatMap (fun b => (b.map (Cell.shared d)).toList) :=
    fun data => Vector.toList_flatMap' _ _
  constructor
  · rintro ⟨data, dec, hb⟩
    have hL : data.toList.length = xs.length + ys.length := by simp
    let data₁ : Vector (Vector Byte repr.size) xs.length :=
      ⟨(data.toList.take xs.length).toArray, by simp [hL]⟩
    let data₂ : Vector (Vector Byte repr.size) ys.length :=
      ⟨(data.toList.drop xs.length).toArray, by simp [hL]⟩
    have h₁ : data₁.toList = data.toList.take xs.length := by simp [data₁, Vector.toList]
    have h₂ : data₂.toList = data.toList.drop xs.length := by simp [data₂, Vector.toList]
    have hsplit : (data.flatMap (fun b => b.map (Cell.shared d))).toList =
        (data₁.flatMap (fun b => b.map (Cell.shared d))).toList ++
          (data₂.flatMap (fun b => b.map (Cell.shared d))).toList := by
      rw [hcells, hcells, hcells, h₁, h₂, ← List.flatMap_append, List.take_append_drop]
    rw [hsplit] at hb
    obtain ⟨a, b, hab, rfl, ha, hb'⟩ := (Bytes.block_append repr p q bptr _ _ hprov
      (by rw [hoff, hcells, flatMap_shared_length, h₁]; simp [hL])
      (by rw [hcells, flatMap_shared_length]; exact Repr.aligned_stride repr _) h).mp hb
    refine ⟨a, b, hab, rfl, ⟨data₁, fun i => ?_, ha⟩, ⟨data₂, fun i => ?_, hb'⟩⟩
    · have hv := dec ⟨i.val, by simp; omega⟩
      have e₁ : data₁[i.val] = data[i.val] := by
        simp only [data₁, Vector.getElem_mk, List.getElem_toArray, List.getElem_take]
        rfl
      have ev : (listVec xs)[i.val] = (listVec (xs ++ ys))[i.val]'(by simp; omega) := by
        simp [listVec, List.getElem_append_left]
      rw [e₁, ev]
      exact hv
    · have hv := dec ⟨xs.length + i.val, by simp⟩
      have e₂ : data₂[i.val] = data[xs.length + i.val] := by
        simp only [data₂, Vector.getElem_mk, List.getElem_toArray, List.getElem_drop]
        rfl
      have ev : (listVec ys)[i.val] = (listVec (xs ++ ys))[xs.length + i.val]'(by simp) := by
        simp [listVec]
      rw [e₂, ev]
      exact hv
  · rintro ⟨a, b, hab, rfl, ⟨data₁, dec₁, ha⟩, ⟨data₂, dec₂, hb⟩⟩
    let data : Vector (Vector Byte repr.size) (xs ++ ys).length :=
      ⟨(data₁.toList ++ data₂.toList).toArray, by simp⟩
    have h₀ : data.toList = data₁.toList ++ data₂.toList := by simp [data, Vector.toList]
    refine ⟨data, fun i => ?_, ?_⟩
    · by_cases hi : i.val < xs.length
      · have hv := dec₁ ⟨i.val, hi⟩
        have e : data[i.val] = data₁[i.val] := by
          simp only [data, Vector.getElem_mk, List.getElem_toArray]
          rw [List.getElem_append_left (by simpa using hi)]
          simp
        have ev : (listVec (xs ++ ys))[i.val] = (listVec xs)[i.val]'hi := by
          simp [listVec, List.getElem_append_left hi]
        rw [e, ev]
        exact hv
      · have hi' : i.val - xs.length < ys.length := by have := i.isLt; simp at this; omega
        have hv := dec₂ ⟨i.val - xs.length, hi'⟩
        have e : data[i.val] = data₂[i.val - xs.length] := by
          simp only [data, Vector.getElem_mk, List.getElem_toArray]
          rw [List.getElem_append_right (by simpa using hi)]
          simp
        have ev : (listVec (xs ++ ys))[i.val] = (listVec ys)[i.val - xs.length]'hi' := by
          simp [listVec, List.getElem_append_right (Nat.le_of_not_lt hi)]
        rw [e, ev]
        exact hv
    · have hsplit : (data.flatMap (fun b => b.map (Cell.shared d))).toList =
          (data₁.flatMap (fun b => b.map (Cell.shared d))).toList ++
            (data₂.flatMap (fun b => b.map (Cell.shared d))).toList := by
        rw [hcells, hcells, hcells, h₀, List.flatMap_append]
      rw [hsplit]
      exact (Bytes.block_append repr p q bptr _ _ hprov
        (by rw [hoff, hcells, flatMap_shared_length]; simp)
        (by rw [hcells, flatMap_shared_length]; exact Repr.aligned_stride repr _) _).mpr
        ⟨a, b, hab, rfl, ha, hb⟩

theorem NoOwned_rangeWith {T V : Type} {repr : Repr T} {valid : V → Vector Byte repr.size → Prop}
    {p : RawPtr T} {bptr : BasePtr} {values : Vector V count} {depth : Nat} {a : Fragment}
    (h : rangeWith repr valid p bptr values depth a) : NoOwned a :=
  let ⟨_, _, hb⟩ := h; NoOwned.block hb

/-- A range which holds in a heap ends before the end of the address space. -/
theorem rangeWith_bound {T V : Type} (repr : Repr T) (valid : V → Vector Byte repr.size → Prop)
    (p : RawPtr T) (base : BasePtr) (values : Vector V count) (depth : Nat) (hcount : 0 < count)
    (hsize : 0 < repr.size) (h : Fragment) (s : Heap)
    (hp : rangeWith repr valid p base values depth h) (hm : Fragment.Matches s h) (hi : s.Inv) :
    p.address.val + count * repr.size < 2 ^ UScalarTy.numBits .Usize := by
  obtain ⟨data, _, hlo, _, rfl⟩ := hp
  obtain ⟨blk, hb, hl, _, hbase, _⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
      (data := data.flatMap (fun b => b.map (Cell.shared depth)))
      (Nat.mul_pos hcount hsize) hm
  have bounded := hi.validBlock hl
  simp only [Heap.validBlock, Bool.and_eq_true] at bounded
  have upper : blk.bptr.val + blk.repr.length < 2 ^ UScalarTy.numBits .Usize := by
    have bounds : 0 < blk.bptr.val ∧
        blk.bptr.val + blk.repr.length < 2 ^ UScalarTy.numBits .Usize := by
      simpa [Heap.bounded] using bounded.1.1
    exact bounds.2
  change p.offsetFrom base + count * repr.size ≤ blk.repr.length at hb
  simp only [RawPtr.offsetFrom] at hb
  subst hbase
  omega

/-- Two non-empty blocks of the same view, which hold in the same heap, have the same base
pointer. -/
theorem block_bptr_eq {T U : Type} {repr : Repr T} {repr' : Repr U} {p : RawPtr T} {q : RawPtr U}
    {b₁ b₂ : BasePtr} {c₁ c₂ : List Cell} {h₁ h₂ : Fragment} {s : Heap}
    (hprov : q.provenance = p.provenance) (hb₁ : block repr p b₁ c₁ h₁)
    (hb₂ : block repr' q b₂ c₂ h₂) (n₁ : 0 < c₁.length) (n₂ : 0 < c₂.length)
    (m₁ : Fragment.Matches s h₁) (m₂ : Fragment.Matches s h₂) : b₁ = b₂ := by
  obtain ⟨_, _, rfl⟩ := hb₁
  obtain ⟨_, _, rfl⟩ := hb₂
  obtain ⟨blk, hl, _, hb, _⟩ := m₁ _ ⟨0, n₁, rfl⟩
  obtain ⟨blk', hl', _, hb', _⟩ := m₂ _ ⟨0, n₂, rfl⟩
  change s.allocations q.provenance = some blk' at hl'
  rw [hprov, hl] at hl'
  cases hl'
  rw [← hb, hb']

/-- The cells of the `i`-th element of a range, and the rest of the range, which can be given back
with any element (`focus_range`, for elements which are not values of `T`). -/
theorem rangeWith_focus {T V : Type} (repr : Repr T) (valid : V → Vector Byte repr.size → Prop)
    (p q : RawPtr T) (base : BasePtr) (values : Vector V count)
    (depth : Nat) (i : Fin count) (hsize : 0 < repr.size)
    (hprov : q.provenance = p.provenance)
    (haddr : q.address.val = p.address.val + i.val * repr.size)
    (h : Fragment) (hp : rangeWith repr valid p base values depth h) :
    ∃ rest : (Fragment → Prop),
      sep (fun h => ∃ bytes, valid values[i.val] bytes ∧
        block repr q base (bytes.map (Cell.shared depth)).toList h) rest h ∧
      ∀ value h', sep (fun h => ∃ bytes, valid value bytes ∧
        block repr q base (bytes.map (Cell.shared depth)).toList h) rest h' →
        rangeWith repr valid p base (values.set i.val value i.isLt) depth h' := by
  obtain ⟨data, encoded, hlo, aligned, cells⟩ := hp
  let old := data.map fun bytes => bytes.map (Cell.shared depth)
  let rest := otherCells base p.provenance (p.offsetFrom base) old i
  have hoff : q.offsetFrom base = p.offsetFrom base + i.val * repr.size := by
    simp only [RawPtr.offsetFrom]
    omega
  have halign : repr.align.val ∣ q.address.val := by
    rw [haddr]
    exact Nat.dvd_add aligned (repr.aligned_stride i.val)
  refine ⟨fun h => h = rest, ?_, ?_⟩
  · refine ⟨cellsHeap base p.provenance (p.offsetFrom base + i.val * repr.size)
      old[i.val].toList, rest, disjoint_otherCells _ _ _ old i, ?_, ?_, rfl⟩
    · rw [cells]
      simpa only [old, Vector.flatMap_map, Function.comp_def, id_eq] using
        split_cells base p.provenance (p.offsetFrom base) old hsize i
    · refine ⟨data[i.val], encoded i, by omega, halign, ?_⟩
      simp only [hprov, hoff, old, Vector.getElem_map]
  · rintro value h' ⟨single, other, _, combined, hvalue, hother⟩
    subst other
    obtain ⟨bytes, newEncoded, _, _, singleEq⟩ := hvalue
    refine ⟨data.set i.val bytes i.isLt, ?_, hlo, aligned, ?_⟩
    · intro j
      by_cases he : j = i
      · subst j
        simpa only [Vector.getElem_set_self] using newEncoded
      · have hne : i.val ≠ j.val := fun he' => he (Fin.ext he'.symm)
        simp only [Vector.getElem_set_ne i.isLt j.isLt hne]
        exact encoded j
    · have grouped : (data.set i.val bytes i.isLt).map (fun b => b.map (Cell.shared depth)) =
          old.set i.val (bytes.map (Cell.shared depth)) i.isLt := by
        simp [old]
      have full := split_cells base p.provenance (p.offsetFrom base)
        (old.set i.val (bytes.map (Cell.shared depth)) i.isLt) hsize i
      simp only [Vector.getElem_set_self, otherCells_set] at full
      have joined : h' = cellsHeap base p.provenance (p.offsetFrom base)
          ((old.set i.val (bytes.map (Cell.shared depth)) i.isLt).flatMap id).toList := by
        rw [full, combined, singleEq]
        simp only [hprov, hoff]
        rfl
      simpa only [← grouped, Vector.flatMap_map, Function.comp_def, id_eq] using joined

/-- Reads an element of a range whose bytes decode to `v`. -/
theorem rangeWith_readElem.local {T V : Type} [Pointee T]
    (valid : V → Vector Byte (Pointee.repr (T := T)).size → Prop) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector V count) (depth : Nat) (i : Fin count) (v : T)
    (hdec : ∀ bytes, valid values[i.val] bytes → (Pointee.repr (T := T)).decode bytes = some v)
    (hsize : 0 < (Pointee.repr (T := T)).size) (P : Fragment → Prop)
    (view : ∀ h, P h → rangeWith (Pointee.repr (T := T)) valid p bptr values depth h) :
    LocalOp P (State.read (Pointee.repr (T := T)) (p.elem i.val))
      (fun result h => result = v ∧ P h) := by
  intro h F s hP hd hm hi
  have hp := view h hP
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have bound := rangeWith_bound _ valid p bptr values depth
    (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt) hsize h s hp localMatch hi
  have hfit : p.address.val + i.val * (Pointee.repr (T := T)).size <
      2 ^ UScalarTy.numBits .Usize := by
    have := Nat.mul_le_mul_right (Pointee.repr (T := T)).size (Nat.le_of_lt i.isLt)
    omega
  obtain ⟨rest, ⟨a, b, _, hab, ⟨bytes, hv, hblk⟩, _⟩, _⟩ :=
    rangeWith_focus _ valid p (p.elem i.val) bptr values depth i hsize rfl
      (p.elem_address i.val hfit) h hp
  have hma := ((Fragment.matches_union _ _ _).mp (hab ▸ localMatch)).1
  have hr := read_of_readable hsize ⟨bytes, hdec bytes hv, hblk⟩ hma
  refine ⟨⟨v, s, hr, rfl⟩, ?_⟩
  rintro x s' ⟨hx, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hx.symm.trans hr), hP⟩

/-- Pointer arithmetic, by any (possibly negative) number `c` of elements, from the `j`-th element
of a range to its `t`-th element (`j + c = t`), or one past its end. -/
theorem rangeWith_offset.local {T V : Type} [Pointee T]
    (valid : V → Vector Byte (Pointee.repr (T := T)).size → Prop) (p : RawPtr T) (base : BasePtr)
    (values : Vector V count) (depth : Nat) (j : Nat) (c : Int) (t : Nat) (hcount : 0 < count)
    (hsize : 0 < (Pointee.repr (T := T)).size) (hj : j ≤ count) (htc : (j : Int) + c = t)
    (htle : t ≤ count) (P : Fragment → Prop)
    (view : ∀ h, P h → rangeWith (Pointee.repr (T := T)) valid p base values depth h) :
    LocalOp P (State.offset (Pointee.repr (T := T)) (p.elem j) c)
      (fun result h => result = p.elem t ∧ P h) := by
  intro h F s hP hd hm hi
  have keep := hP
  have hp := view h hP
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have bound := rangeWith_bound _ valid p base values depth hcount hsize h s hp localMatch hi
  have hmulj := Nat.mul_le_mul_right (Pointee.repr (T := T)).size hj
  have hmult := Nat.mul_le_mul_right (Pointee.repr (T := T)).size htle
  have hqaddr : (p.elem j).address.val = p.address.val + j * (Pointee.repr (T := T)).size :=
    RawPtr.elem_address p j (by omega)
  have hfit : p.address.val + t * (Pointee.repr (T := T)).size < 2 ^ UScalarTy.numBits .Usize := by
    omega
  have target : ((p.elem j).address.val : Int) + c * ((Pointee.repr (T := T)).size : Int) =
      ((p.address.val + t * (Pointee.repr (T := T)).size : Nat) : Int) := by
    rw [hqaddr]
    push_cast
    have : (c : Int) = (t : Int) - j := by omega
    rw [this]
    ring
  obtain ⟨data, _, hlo', _, cells⟩ := hp
  rw [cells] at localMatch
  obtain ⟨blk, hb, hl, hlive, hbase, _⟩ :=
    Bytes.bytes_of_matches (repr := (Pointee.repr (T := T)).region count) (p := p.cast Unit)
      (data := data.flatMap (fun bytes => bytes.map (Cell.shared depth)))
      (Nat.mul_pos hcount hsize) localMatch
  change p.offsetFrom base + count * (Pointee.repr (T := T)).size ≤ blk.repr.length at hb
  change s.allocations (p.elem j).provenance = some blk at hl
  simp only [RawPtr.offsetFrom] at hb
  have hqlo : base.val ≤ (p.elem j).address.val := by omega
  have hstart : (p.elem j).address.val ≤ base.val + blk.repr.length := by omega
  have hlo'' : (base.val : Int) ≤ ((p.elem j).address.val : Int) +
      c * ((Pointee.repr (T := T)).size : Int) := by rw [target]; omega
  have hhi' : ((p.elem j).address.val : Int) + c * ((Pointee.repr (T := T)).size : Int) ≤
      base.val + blk.repr.length := by rw [target]; omega
  have hf : ((p.elem j).address.val : Int) + c * ((Pointee.repr (T := T)).size : Int) <
      (2 : Int) ^ System.Platform.numBits := by
    rw [target]
    have : ((p.address.val + t * (Pointee.repr (T := T)).size : Nat) : Int) <
        ((2 ^ UScalarTy.numBits .Usize : Nat) : Int) := by exact_mod_cast hfit
    simpa only [Nat.cast_pow, Nat.cast_ofNat, UScalarTy.Usize_numBits_eq] using this
  have target_nat : (((p.elem j).address.val : Int) +
      c * ((Pointee.repr (T := T)).size : Int)).toNat =
      p.address.val + t * (Pointee.repr (T := T)).size := by
    rw [target]; exact Int.toNat_natCast _
  let result : RawPtr T := ⟨(p.elem j).provenance,
    ⟨BitVec.ofNat _ (p.address.val + t * (Pointee.repr (T := T)).size)⟩⟩
  have hrun : Heap.offset (Pointee.repr (T := T)) (p.elem j) c s = some result := by
    simp [Heap.offset, hl, hlive, hbase, hqlo, hstart, hlo'', hhi', hf, target_nat, result]
  refine ⟨⟨result, s, hrun, rfl⟩, ?_⟩
  rintro answer s' ⟨he, rfl⟩
  have he := Option.some.inj (he.symm.trans hrun)
  subst answer
  exact ⟨h, hd, hm, hi, rfl, keep⟩

/-- Writes an element of an exclusive range, whatever its bytes were. -/
theorem rangeWith_writeElem.local {T V : Type} [Pointee T]
    (valid : V → Vector Byte (Pointee.repr (T := T)).size → Prop) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector V count) (i : Fin count) (value : T) (new : V)
    (hnew : ∀ bytes, (Pointee.repr (T := T)).encode value bytes → valid new bytes)
    (noPointers : ∀ q, ¬ (Pointee.repr (T := T)).Carries value q)
    (hsize : 0 < (Pointee.repr (T := T)).size) :
    LocalOp (rangeWith (Pointee.repr (T := T)) valid p bptr values 0)
      (State.write (Pointee.repr (T := T)) (p.elem i.val) value)
      (fun _ => rangeWith (Pointee.repr (T := T)) valid p bptr (values.set i.val new i.isLt) 0) := by
  intro h F s hp hd hm hi
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have bound := rangeWith_bound _ valid p bptr values 0
    (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt) hsize h s hp localMatch hi
  have hfit : p.address.val + i.val * (Pointee.repr (T := T)).size <
      2 ^ UScalarTy.numBits .Usize := by
    have := Nat.mul_le_mul_right (Pointee.repr (T := T)).size (Nat.le_of_lt i.isLt)
    omega
  obtain ⟨rest, hsep, rebuild⟩ := rangeWith_focus _ valid p (p.elem i.val) bptr values 0 i hsize
    rfl (p.elem_address i.val hfit) h hp
  have hw : LocalOp (fun h => ∃ bytes, valid values[i.val] bytes ∧
      block (Pointee.repr (T := T)) (p.elem i.val) bptr (bytes.map (Cell.shared 0)).toList h)
      (State.write (Pointee.repr (T := T)) (p.elem i.val) value)
      (fun _ => pointsTo (Pointee.repr (T := T)) (p.elem i.val) bptr value) := by
    rintro h F s ⟨bytes, _, hb⟩ hd hm hinv
    exact write.spec _ (p.elem i.val) bptr bytes value noPointers hsize h F s hb hd hm hinv
  obtain ⟨hE, hPost⟩ := LocalOp.frame (R := rest) hw h F s hsep hd hm hi
  refine ⟨hE, fun x s' hx => ?_⟩
  obtain ⟨h', hd', hm', hi', hq⟩ := hPost x s' hx
  refine ⟨h', hd', hm', hi', rebuild new h' ?_⟩
  obtain ⟨a, b, hab, he, ⟨bytes, henc, hb⟩, hr⟩ := hq
  exact ⟨a, b, hab, he, ⟨bytes, hnew bytes henc, hb⟩, hr⟩

theorem rangeWith_writeElem.auth {T V : Type} [Pointee T]
    (valid : V → Vector Byte (Pointee.repr (T := T)).size → Prop) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector V count) (i : Fin count) (value : T) (new : V)
    (hsize : 0 < (Pointee.repr (T := T)).size) :
    WP.Bytes.AuthPres (rangeWith (Pointee.repr (T := T)) valid p bptr values 0)
      (State.write (Pointee.repr (T := T)) (p.elem i.val) value)
      (fun _ => rangeWith (Pointee.repr (T := T)) valid p bptr (values.set i.val new i.isLt) 0) := by
  refine AuthPres.of_step (fun _ _ h => NoOwned_rangeWith h) ?_
  rintro h F s hp hd hm hi x s' hx a' _ _ _ _ base hEx _
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have bound := rangeWith_bound _ valid p bptr values 0
    (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt) hsize h s hp localMatch hi
  have hfit : p.address.val + i.val * (Pointee.repr (T := T)).size <
      2 ^ UScalarTy.numBits .Usize := by
    have := Nat.mul_le_mul_right (Pointee.repr (T := T)).size (Nat.le_of_lt i.isLt)
    omega
  obtain ⟨rest, ⟨c, r, _, rfl, ⟨bytes, _, hblock⟩, _⟩, _⟩ := rangeWith_focus _ valid p
    (p.elem i.val) bptr values 0 i hsize rfl (p.elem_address i.val hfit) h hp
  obtain ⟨_, _, rfl⟩ := hblock
  exact write_step hsize ((Fragment.matches_union _ _ _).mp localMatch).1 hx base hEx

end Bytes

/-! ## `p ↦?* values` -/

namespace RawPtr

/-- `p ↦?* values`: `p` owns, exclusively, one encoding-sized chunk of cells per element of
`values`, one after the other in some block, whose bytes decode to the element if it is initialized
(`⟨some v⟩`) and are arbitrary otherwise (`⟨none⟩`). See the module documentation. -/
def uninitRange {T : Type} [Pointee T] (p : RawPtr T) (values : List (MaybeUninit T)) : IProp :=
  iexists fun bptr : BasePtr =>
    upClose (Bytes.uninitRange (Pointee.repr (T := T)) p bptr (listVec values))

end RawPtr

end Aeneas.Std

namespace Aeneas

/-- `p ↦?* values` (`p : RawPtr T`, `values : List (MaybeUninit T)`): see `RawPtr.uninitRange`. -/
scoped notation:50 q:50 " ↦?* " values:50 => Std.RawPtr.uninitRange q values

end Aeneas

namespace Aeneas.Std

open Aeneas.SepLogic Aeneas.Std.WP core.mem.maybe_uninit

/-! ## Entailment in the realizing heaps

`RealEntails P Q`: every heap which realizes `P` (with any frame) realizes `Q` (with the same
frame). It is weaker than `P ⊢ Q`, and can use the facts that hold in every heap (for instance, that
two non-empty blocks of the same view have the same base pointer, or that a block doesn't wrap
around the address space). It is used through `ispec_realEntails_pre` and
`ispec_realEntails_post`. -/

/-- `P` entails `Q` in the heaps which realize it, with any frame. -/
def RealEntails (P Q : IProp) : Prop :=
  ∀ F s, Realizes (P ∗ F) s → Realizes (Q ∗ F) s

namespace RealEntails

theorem of_entails {P Q : IProp} (h : P ⊢ Q) : RealEntails P Q :=
  fun F _ hR => Realizes.mono (sep_mono h (entails_refl F)) hR

theorem refl (P : IProp) : RealEntails P P := fun _ _ h => h

theorem trans {P Q R : IProp} (h₁ : RealEntails P Q) (h₂ : RealEntails Q R) : RealEntails P R :=
  fun F s h => h₂ F s (h₁ F s h)

theorem frame {P Q : IProp} (h : RealEntails P Q) (R : IProp) : RealEntails (P ∗ R) (Q ∗ R) := by
  intro F s hR
  exact Realizes.mono (entails_of_eq (sep_assoc_eq Q R F).symm)
    (h (R ∗ F) s (Realizes.mono (entails_of_eq (sep_assoc_eq P R F)) hR))

theorem frame_left {P Q : IProp} (h : RealEntails P Q) (R : IProp) :
    RealEntails (R ∗ P) (R ∗ Q) := by
  rw [sep_comm_eq R P, sep_comm_eq R Q]
  exact h.frame R

/-- Fragment-level reasoning in a heap which matches the fragment. -/
theorem of_matches {P Q : IProp}
    (hPQ : ∀ s h, s.Inv → Fragment.Matches s h → P h → Q h) : RealEntails P Q := by
  rintro F s ⟨hInv, _, ⟨h₁, h₂, hd, rfl, hP, hF⟩, hm, hAuth⟩
  exact ⟨hInv, _, ⟨h₁, h₂, hd, rfl,
    hPQ s h₁ hInv ((Fragment.matches_union _ _ _).mp hm).1 hP, hF⟩, hm, hAuth⟩

/-! The postconditions of `step` start with pure facts and end with existentials: the rules below
let a `RealEntails` proof (for instance through `ispec_realEntails_post`, to merge ranges back)
use the facts and choose the witnesses, as `entails_pure_l` and `entails_exists_l`/`_r` do for
`⊢`. -/

/-- Uses a pure fact of the source. -/
theorem pure_l {P : Prop} {H Q : IProp} (h : P → RealEntails H Q) :
    RealEntails iprop(⌜P⌝ ∗ H) Q := by
  intro F s hR
  obtain ⟨hInv, x, hx, hm, ha⟩ := Realizes.mono (entails_of_eq (sep_assoc_eq _ _ _)) hR
  obtain ⟨hP, hx'⟩ := (sep_pure_l _ _ x).mp hx
  exact h hP F s ⟨hInv, x, hx', hm, ha⟩

/-- Opens an existential of the source. -/
theorem exists_l {ι : Sort _} {J : ι → IProp} {Q : IProp} (h : ∀ x, RealEntails (J x) Q) :
    RealEntails (iexists J) Q := by
  intro F s hR
  rw [sep_exists_l_eq] at hR
  obtain ⟨hInv, fr, hJ, hm, ha⟩ := hR
  obtain ⟨x, hx⟩ := (exists_holds _ _).mp hJ
  exact h x F s ⟨hInv, fr, hx, hm, ha⟩

/-- Chooses the witness of an existential of the target. -/
theorem exists_r {ι : Sort _} {H : IProp} {J : ι → IProp} (x : ι) (h : RealEntails H (J x)) :
    RealEntails H (iexists J) :=
  h.trans (of_entails (entails_exists_r x (entails_refl _)))

/-- Weakens the target by an entailment. -/
theorem trans_entails {H Q R : IProp} (h : RealEntails H Q) (h' : Q ⊢ R) : RealEntails H R :=
  h.trans (of_entails h')

end RealEntails

theorem ispec_realEntails_pre {α : Type} {P P' : IPre} {m : Result α} {Q : IPost α}
    (hP : RealEntails P P') (hs : ispec P' m Q) : ispec P m Q := by
  rw [ispec_iff] at hs ⊢
  intro F s hR
  exact hs F s (hP F s hR)

unseal Result in
theorem ispec_realEntails_post {α : Type} {P : IPre} {m : Result α} {Q Q' : IPost α}
    (hs : ispec P m Q') (hQ : ∀ x, RealEntails (Q' x) (Q x)) : ispec P m Q := by
  rw [ispec_iff] at hs ⊢
  intro F s hR
  refine (hs F s hR).mono ?_
  intro x s' h
  exact hQ x F s' h

theorem Fragment.matches_of_subheap {s : Heap} {a h : Fragment}
    (hsub : PartialCommMonoid.Subheap a h) (hm : Fragment.Matches s h) : Fragment.Matches s a := by
  obtain ⟨r, _, rfl⟩ := PartialCommMonoid.subheap_iff.mp hsub
  exact ((Fragment.matches_union _ _ _).mp hm).1

/-! ## Pointers to elements -/

theorem RawPtr.elem_elem {T : Type} [Pointee T] (p : RawPtr T) (i j : Nat) :
    (p.elem i).elem j = p.elem (i + j) := by
  simp only [RawPtr.elem, RawPtr.mk.injEq, true_and]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, UScalar.val]
  rw [Nat.mod_add_mod, Nat.add_mul, Nat.add_assoc]

theorem RawPtr.elem_add {T : Type} [Pointee T] (p : RawPtr T) (i j : Nat) :
    p.elem (i + j) = (p.elem i).elem j := (p.elem_elem i j).symm

@[simp] theorem RawPtr.cast_cast {T U V : Type} (p : RawPtr T) :
    (p.cast U).cast V = p.cast V := rfl

@[simp] theorem RawPtr.cast_self {T : Type} (p : RawPtr T) : p.cast T = p := by
  cases p; rfl

@[simp] theorem RawPtr.cast_address {T U : Type} (p : RawPtr T) : (p.cast U).address = p.address :=
  rfl

/-- `ptr.cast::<U>()`. -/
@[step]
theorem RawPtr.ptr_cast.spec {T : Type} (U : Type) (q : RawPtr T) :
    RawPtr.ptr_cast U q ⦃ r => r = q.cast U ⦄ := by
  simp [RawPtr.ptr_cast, spec_ok]

/-! ## Algebra of `↦?*` -/

theorem uninitRange_nil_emp {T : Type} [Pointee T] (p : RawPtr T) : p ↦?* [] ⊢ emp :=
  entails_emp_r _

/-- An empty range, at an aligned address. -/
theorem emp_uninitRange_nil {T : Type} [Pointee T] (p : RawPtr T)
    (ha : (Pointee.repr (T := T)).align.val ∣ p.address.val) : emp ⊢ p ↦?* [] :=
  fun h _ => ⟨0#usize, ∅, Bytes.rangeWith_nil.mpr ⟨by simp, ha, rfl⟩,
    PartialCommMonoid.Subheap.of_empty h⟩

/-- A range starts at an aligned address. -/
theorem uninitRange_aligned {T : Type} [Pointee T] (p : RawPtr T) (vs : List (MaybeUninit T)) :
    p ↦?* vs ⊢ ⌜(Pointee.repr (T := T)).align.val ∣ p.address.val⌝ ∗ p ↦?* vs := by
  rintro h ⟨bptr, a, ⟨data, hv, hlo, ha, hc⟩, hsub⟩
  exact (sep_pure_l _ _ h).mpr ⟨ha, bptr, a, ⟨data, hv, hlo, ha, hc⟩, hsub⟩

/-- A readable range starts at an aligned address. -/
theorem RawPtr.readable_aligned {T : Type} [Pointee T] (p : RawPtr T) (d : Nat) (vs : List T) :
    p.readable d vs ⊢ ⌜(Pointee.repr (T := T)).align.val ∣ p.address.val⌝ ∗ p.readable d vs := by
  rintro h ⟨bptr, a, ha, hsub⟩
  have ha' := ha
  rw [Bytes.readableRange_eq_rangeWith] at ha'
  obtain ⟨data, hv, hlo, hal, hc⟩ := ha'
  exact (sep_pure_l _ _ h).mpr ⟨hal, bptr, a, ha, hsub⟩

/-- Splits a range at any index (the address of the split must not wrap around, which holds in
every heap: see `uninitRange_split_real`). -/
theorem uninitRange_split {T : Type} [Pointee T] (p : RawPtr T) (xs ys : List (MaybeUninit T))
    (hfit : p.address.val + xs.length * (Pointee.repr (T := T)).size <
      2 ^ UScalarTy.numBits .Usize) :
    p ↦?* (xs ++ ys) ⊢ p ↦?* xs ∗ (p.elem xs.length) ↦?* ys := by
  rintro h ⟨bptr, a, ha, hsub⟩
  have hs := (Bytes.rangeWith_append _ _ p (p.elem xs.length) bptr xs ys 0
    (RawPtr.elem_provenance p _) (RawPtr.elem_address p _ hfit) a).mp ha
  obtain ⟨h₁, h₂, hd, he, hA, hB⟩ := upClose_sep _ ⟨a, hs, hsub⟩
  exact ⟨h₁, h₂, hd, he, ⟨bptr, hA⟩, ⟨bptr, hB⟩⟩

/-- Splits a range at any index. -/
theorem uninitRange_split_real {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (xs ys : List (MaybeUninit T)) :
    RealEntails (p ↦?* (xs ++ ys)) (p ↦?* xs ∗ (p.elem xs.length) ↦?* ys) := by
  refine RealEntails.of_matches fun s h hi hm hP => ?_
  apply uninitRange_split p xs ys _ h hP
  obtain ⟨bptr, a, ha, hsub⟩ := hP
  by_cases hx : xs.length = 0
  · rw [hx, Nat.zero_mul, Nat.add_zero]
    exact p.address.bv.isLt
  · have hb := Bytes.rangeWith_bound _ _ p bptr _ 0 (by simp; omega) Pointee.Sized.pos a s ha
      (Fragment.matches_of_subheap hsub hm) hi
    have := Nat.mul_le_mul_right (Pointee.repr (T := T)).size
      (show xs.length ≤ (xs ++ ys).length by simp)
    omega

/-- Merges two adjacent ranges. -/
theorem uninitRange_merge {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (xs ys : List (MaybeUninit T)) :
    RealEntails (p ↦?* xs ∗ (p.elem xs.length) ↦?* ys) (p ↦?* (xs ++ ys)) := by
  refine RealEntails.of_matches fun s h hi hm hP => ?_
  obtain ⟨h₁, h₂, hd, rfl, ⟨b₁, hU₁⟩, ⟨b₂, hU₂⟩⟩ := hP
  obtain ⟨c, ⟨a, b, hab, rfl, ha, hb⟩, hsub⟩ := sep_upClose _ ⟨h₁, h₂, hd, rfl, hU₁, hU₂⟩
  have hmc := Fragment.matches_of_subheap hsub hm
  have hma := ((Fragment.matches_union _ _ _).mp hmc).1
  have hmb := ((Fragment.matches_union _ _ _).mp hmc).2
  by_cases hx : xs = []
  · subst hx
    simp only [List.length_nil, RawPtr.elem_zero] at hb
    rw [List.nil_append]
    exact ⟨b₂, b, hb,
      (PartialCommMonoid.Subheap.union_right hab).trans hsub⟩
  by_cases hy : ys = []
  · subst hy
    rw [List.append_nil]
    exact ⟨b₁, a, ha, (PartialCommMonoid.Subheap.union_left hab).trans hsub⟩
  have hxl : 0 < xs.length := List.length_pos_iff.mpr hx
  have hyl : 0 < ys.length := List.length_pos_iff.mpr hy
  have hsize := (Pointee.Sized.pos (T := T))
  obtain ⟨da, hva, hbla⟩ := ha
  obtain ⟨db, hvb, hblb⟩ := hb
  have heq : b₁ = b₂ := Bytes.block_bptr_eq (RawPtr.elem_provenance p _) hbla hblb
    (by simp; exact ⟨hxl, hsize⟩) (by simp; exact ⟨hyl, hsize⟩) hma hmb
  subst heq
  have hfit := Bytes.rangeWith_bound _ _ p b₁ _ 0 hxl hsize a s ⟨da, hva, hbla⟩ hma hi
  refine ⟨b₁, a ∪ b, ?_, hsub⟩
  exact (Bytes.rangeWith_append _ _ p (p.elem xs.length) b₁ xs ys 0
    (RawPtr.elem_provenance p _) (RawPtr.elem_address p _ (by simpa using hfit)) _).mpr
    ⟨a, b, hab, rfl, ⟨da, hva, hbla⟩, ⟨db, hvb, hblb⟩⟩

/-- Splits off the first element. -/
theorem uninitRange_cons {T : Type} [Pointee T] (p : RawPtr T) (v : MaybeUninit T)
    (vs : List (MaybeUninit T))
    (hfit : p.address.val + (Pointee.repr (T := T)).size < 2 ^ UScalarTy.numBits .Usize) :
    p ↦?* (v :: vs) ⊢ p ↦?* [v] ∗ (p.elem 1) ↦?* vs :=
  uninitRange_split p [v] vs (by simpa using hfit)

theorem uninitRange_cons_real {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (v : MaybeUninit T) (vs : List (MaybeUninit T)) :
    RealEntails (p ↦?* (v :: vs)) (p ↦?* [v] ∗ (p.elem 1) ↦?* vs) :=
  uninitRange_split_real p [v] vs

theorem uninitRange_cons_merge {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (v : MaybeUninit T) (vs : List (MaybeUninit T)) :
    RealEntails (p ↦?* [v] ∗ (p.elem 1) ↦?* vs) (p ↦?* (v :: vs)) :=
  uninitRange_merge p [v] vs

/-- Splits off the last element. -/
theorem uninitRange_concat_real {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (v : MaybeUninit T) :
    RealEntails (p ↦?* (vs ++ [v])) (p ↦?* vs ∗ (p.elem vs.length) ↦?* [v]) :=
  uninitRange_split_real p vs [v]

/-- Forgets what is known about the elements (`MaybeUninit.Refines`). -/
theorem uninitRange_refines {T : Type} [Pointee T] (p : RawPtr T)
    {xs ys : List (MaybeUninit T)} (href : MaybeUninit.Refines xs ys) : p ↦?* xs ⊢ p ↦?* ys := by
  rintro h ⟨bptr, a, ha, hsub⟩
  exact ⟨bptr, a, Bytes.rangeWith_list_imp xs ys href.1
    (fun i hx hy _ hv w hw => hv w (href.2 i hx hy w hw)) ha, hsub⟩

/-- Every range is an owned writable buffer. -/
theorem uninitRange_forget {T : Type} [Pointee T] (p : RawPtr T) (xs : List (MaybeUninit T)) :
    p ↦?* xs ⊢ p ↦?* List.replicate xs.length ⟨none⟩ :=
  uninitRange_refines p (MaybeUninit.Refines.replicate_none xs)

/-- Forgets the `i`-th element. -/
theorem uninitRange_set_none {T : Type} [Pointee T] (p : RawPtr T) (xs : List (MaybeUninit T))
    (i : Nat) : p ↦?* xs ⊢ p ↦?* xs.set i ⟨none⟩ :=
  uninitRange_refines p (MaybeUninit.Refines.set_none xs i)

/-- A range of values is a range of initialized values. -/
theorem range_uninitRange {T : Type} [Pointee T] (p : RawPtr T) (vs : List T) :
    p ↦* vs ⊢ p ↦?* vs.map (fun v => ⟨some v⟩) := by
  rintro h ⟨bptr, a, ha, hsub⟩
  exact ⟨bptr, a, Bytes.rangeWith_list_imp vs _ (by simp)
    (fun i _ _ bytes he => by simpa using (Pointee.repr (T := T)).encode_decode _ _ he) ha, hsub⟩

theorem readable_uninitRange {T : Type} [Pointee T] (p : RawPtr T) (vs : List T) :
    p.readable 0 vs ⊢ p ↦?* vs.map (fun v => ⟨some v⟩) := by
  rintro h ⟨bptr, a, ha, hsub⟩
  exact ⟨bptr, a, Bytes.rangeWith_list_imp
    (valid := fun v bytes => (Pointee.repr (T := T)).decode bytes = some v) vs _ (by simp)
    (fun i _ _ bytes he => by simpa using he) ha, hsub⟩

theorem uninitRange_readable {T : Type} [Pointee T] (p : RawPtr T) (vs : List T) :
    p ↦?* vs.map (fun v => ⟨some v⟩) ⊢ p.readable 0 vs := by
  rintro h ⟨bptr, a, ha, hsub⟩
  exact ⟨bptr, a, Bytes.rangeWith_list_imp
    (valid' := fun v bytes => (Pointee.repr (T := T)).decode bytes = some v) _ vs (by simp)
    (fun i _ _ bytes he => by simpa using he) ha, hsub⟩

/-- `p.readable 0 vs` and `p ↦?* vs.map (⟨some ·⟩)` are the same assertion. -/
theorem readable_eq_uninitRange {T : Type} [Pointee T] (p : RawPtr T) (vs : List T) :
    p.readable 0 vs = (p ↦?* vs.map (fun v => ⟨some v⟩)) :=
  entails_antisymm (readable_uninitRange p vs) (uninitRange_readable p vs)

theorem pointsTo_uninitRange {T : Type} [Pointee T] (p : RawPtr T) (v : T) :
    p ↦ v ⊢ p ↦?* [⟨some v⟩] := by
  rw [← RawPtr.range_singleton]
  simpa using range_uninitRange p [v]

/-! ## Accesses to the elements of `↦?*` -/

/-- Writes the `i`-th element of a range, whatever its bytes were. `noPointers`: the encodings of
`v` carry no pointer (it holds for every value of a `Pointee.NoPointers` type). -/
theorem MutRawPtr.write.spec_uninit' {T : Type} [Pointee T] [Pointee.Sized T] (p : MutRawPtr T)
    (vs : List (MaybeUninit T)) (i : Nat) (v : T) (hi : i < vs.length)
    (noPointers : ∀ q, ¬ (Pointee.repr (T := T)).Carries v q) :
    ⦃ p ↦?* vs ⦄ MutRawPtr.write (p.elem i) v ⦃ p ↦?* vs.set i ⟨some v⟩ ⦄ := by
  refine ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.rangeWith_writeElem.local (MaybeUninit.Decodes _) p bptr (listVec vs)
        ⟨i, hi⟩ v ⟨some v⟩
        (fun bytes he => (MaybeUninit.decodes_some _ _ _).mpr
          ((Pointee.repr (T := T)).encode_decode _ _ he)) noPointers Pointee.Sized.pos)
      (fun bptr => Bytes.rangeWith_writeElem.auth _ p bptr (listVec vs) ⟨i, hi⟩ v ⟨some v⟩
        Pointee.Sized.pos))
    (entails_refl _) (fun _ => ?_)
  rintro h ⟨bptr, a, ha, hsa⟩
  refine ⟨bptr, a, ?_, hsa⟩
  exact Bytes.rangeWith_imp _ _ (by simp)
    (fun j _ _ bytes hv => by
      by_cases hij : i = j
      · subst hij; simpa [listVec] using hv
      · simpa [listVec, List.getElem_set_ne hij, Vector.getElem_set_ne _ _ hij] using hv) ha

/-- Writes the `i`-th element of a range of a type without pointers, whatever its bytes were. -/
@[step]
theorem MutRawPtr.write.spec_uninit {T : Type} [Pointee T] [Pointee.Sized T]
    [Pointee.NoPointers T] (p : MutRawPtr T) (vs : List (MaybeUninit T)) (i : Nat) (v : T)
    (hi : i < vs.length) :
    ⦃ p ↦?* vs ⦄ MutRawPtr.write (p.elem i) v ⦃ p ↦?* vs.set i ⟨some v⟩ ⦄ :=
  MutRawPtr.write.spec_uninit' p vs i v hi (Pointee.NoPointers.no_pointers v)

/-- Reads the `i`-th element of a range, which is initialized. -/
@[step]
theorem RawPtr.read.spec_uninit {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (i : Nat) (v : T) (hi : i < vs.length) (hv : vs[i] = ⟨some v⟩) :
    ⦃ p ↦?* vs ⦄ RawPtr.read (p.elem i) ⦃ r => ⌜r = v⌝ ∗ p ↦?* vs ⦄ :=
  ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.rangeWith_readElem.local (MaybeUninit.Decodes _) p bptr (listVec vs) 0
        ⟨i, hi⟩ v (fun bytes hd => hd v (by simp [listVec, hv])) Pointee.Sized.pos _
        (fun _ h => h))
      (fun _ => Bytes.AuthPres.of_eq (fun _ _ h => Bytes.NoOwned_rangeWith h.2)
        (fun _ _ _ h => h.2)))
    (entails_refl _) (fun _ => iexists_upClose_pure_and)

/-- Writes the first element of a range (`*p = v`, at the pointer of the range itself). -/
theorem MutRawPtr.write.spec_uninit_head {T : Type} [Pointee T] [Pointee.Sized T]
    [Pointee.NoPointers T] (p : MutRawPtr T) (vs : List (MaybeUninit T)) (v : T)
    (hne : 0 < vs.length) :
    ⦃ p ↦?* vs ⦄ MutRawPtr.write p v ⦃ p ↦?* vs.set 0 ⟨some v⟩ ⦄ := by
  simpa only [RawPtr.elem_zero] using MutRawPtr.write.spec_uninit p vs 0 v hne

/-- Reads the first element of a range, which is initialized. -/
theorem RawPtr.read.spec_uninit_head {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (v : T) (hne : 0 < vs.length) (hv : vs[0] = ⟨some v⟩) :
    ⦃ p ↦?* vs ⦄ RawPtr.read p ⦃ r => ⌜r = v⌝ ∗ p ↦?* vs ⦄ := by
  simpa only [RawPtr.elem_zero] using RawPtr.read.spec_uninit p vs 0 v hne hv

/-! ## Pointer arithmetic within `↦?*` and `readable` ranges -/

/-- Pointer arithmetic within a range: the generic form of the specifications below. -/
theorem RawPtr.offset_elem.spec_rangeWith {T V : Type} [Pointee T] [Pointee.Sized T]
    (valid : V → Vector Byte (Pointee.repr (T := T)).size → Prop) (depth : Nat)
    (p : RawPtr T) (values : List V) (j : Nat) (c : Int) (t : Nat) (hne : 0 < values.length)
    (hj : j ≤ values.length) (htc : (j : Int) + c = t) (ht : t ≤ values.length) :
    ispec (iexists fun bptr : BasePtr => upClose
        (Bytes.rangeWith (Pointee.repr (T := T)) valid p bptr (listVec values) depth))
      (Result.checkedModify (State.offset (Pointee.repr (T := T)) (p.elem j) c))
      (fun result => ⌜result = p.elem t⌝ ∗ iexists fun bptr : BasePtr => upClose
        (Bytes.rangeWith (Pointee.repr (T := T)) valid p bptr (listVec values) depth)) :=
  ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.rangeWith_offset.local valid p bptr (listVec values) depth j c t hne
        Pointee.Sized.pos hj htc ht _ (fun _ h => h))
      (fun _ => Bytes.AuthPres.of_eq (fun _ _ h => Bytes.NoOwned_rangeWith h.2)
        (fun _ _ _ h => h.2)))
    (entails_refl _) (fun _ => iexists_upClose_pure_and)

/-- `add` from the `i`-th element of a range, to an element or one past the end. -/
@[step]
theorem RawPtr.add.spec_uninit {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (i : Nat) (k : Usize) (hne : 0 < vs.length)
    (hle : i + k.val ≤ vs.length) :
    ⦃ p ↦?* vs ⦄ RawPtr.add (p.elem i) k ⦃ r => ⌜r = p.elem (i + k.val)⌝ ∗ p ↦?* vs ⦄ :=
  RawPtr.offset_elem.spec_rangeWith _ 0 p vs i k.val (i + k.val) hne (by omega) (by omega) hle

/-- `offset` (by a possibly negative count) from the `i`-th element of a range, to an element or
one past the end. -/
@[step]
theorem RawPtr.offset.spec_uninit {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (i : Nat) (k : Isize) (hne : 0 < vs.length)
    (hi : i ≤ vs.length) (hlo : 0 ≤ (i : Int) + k.val) (hle : (i : Int) + k.val ≤ vs.length) :
    ⦃ p ↦?* vs ⦄ RawPtr.offset (p.elem i) k
      ⦃ r => ⌜r = p.elem ((i : Int) + k.val).toNat⌝ ∗ p ↦?* vs ⦄ :=
  RawPtr.offset_elem.spec_rangeWith _ 0 p vs i k.val ((i : Int) + k.val).toNat hne hi (by omega) (by omega)

/-- `add` from the start of a range. -/
theorem RawPtr.add.spec_uninit_head {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (k : Usize) (hne : 0 < vs.length) (hle : k.val ≤ vs.length) :
    ⦃ p ↦?* vs ⦄ RawPtr.add p k ⦃ r => ⌜r = p.elem k.val⌝ ∗ p ↦?* vs ⦄ := by
  simpa only [RawPtr.elem_zero, Nat.zero_add] using
    RawPtr.add.spec_uninit p vs 0 k hne (by omega)

/-- `offset` (by a nonnegative count) from the start of a range. -/
@[step]
theorem RawPtr.offset.spec_uninit_head {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (k : Isize) (hne : 0 < vs.length) (hlo : 0 ≤ k.val)
    (hle : k.val ≤ vs.length) :
    ⦃ p ↦?* vs ⦄ RawPtr.offset p k ⦃ r => ⌜r = p.elem k.val.toNat⌝ ∗ p ↦?* vs ⦄ := by
  simpa only [RawPtr.elem_zero, Nat.cast_zero, Int.zero_add] using
    RawPtr.offset.spec_uninit p vs 0 k hne (by omega) (by omega) (by omega)

/-- `sub` from the `i`-th element of a range (or one past its end). -/
@[step]
theorem RawPtr.sub.spec_uninit {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (i : Nat) (k : Usize) (hne : 0 < vs.length)
    (hi : i ≤ vs.length) (hk : k.val ≤ i) :
    ⦃ p ↦?* vs ⦄ RawPtr.sub (p.elem i) k ⦃ r => ⌜r = p.elem (i - k.val)⌝ ∗ p ↦?* vs ⦄ :=
  RawPtr.offset_elem.spec_rangeWith _ 0 p vs i (-(k.val : Int)) (i - k.val) hne hi (by omega)
    (by omega)

/-- `add` from the `i`-th element of a readable range, to an element or one past the end. -/
theorem RawPtr.add.spec_readable_elem {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (depth : Nat) (vs : List T) (i : Nat) (k : Usize) (hne : 0 < vs.length)
    (hle : i + k.val ≤ vs.length) :
    ⦃ p.readable depth vs ⦄ RawPtr.add (p.elem i) k
      ⦃ r => ⌜r = p.elem (i + k.val)⌝ ∗ p.readable depth vs ⦄ :=
  RawPtr.offset_elem.spec_rangeWith (fun v bytes => (Pointee.repr (T := T)).decode bytes = some v) depth p vs i k.val (i + k.val) hne (by omega) (by omega) hle

/-- `offset` (by a possibly negative count) from the `i`-th element of a readable range. -/
theorem RawPtr.offset.spec_readable {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (depth : Nat) (vs : List T) (i : Nat) (k : Isize) (hne : 0 < vs.length)
    (hi : i ≤ vs.length) (hlo : 0 ≤ (i : Int) + k.val) (hle : (i : Int) + k.val ≤ vs.length) :
    ⦃ p.readable depth vs ⦄ RawPtr.offset (p.elem i) k
      ⦃ r => ⌜r = p.elem ((i : Int) + k.val).toNat⌝ ∗ p.readable depth vs ⦄ :=
  RawPtr.offset_elem.spec_rangeWith (fun v bytes => (Pointee.repr (T := T)).decode bytes = some v) depth p vs i k.val
    ((i : Int) + k.val).toNat hne hi (by omega) (by omega)

/-- `sub` from the `i`-th element of a readable range (or one past its end). -/
theorem RawPtr.sub.spec_readable {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (depth : Nat) (vs : List T) (i : Nat) (k : Usize) (hne : 0 < vs.length)
    (hi : i ≤ vs.length) (hk : k.val ≤ i) :
    ⦃ p.readable depth vs ⦄ RawPtr.sub (p.elem i) k
      ⦃ r => ⌜r = p.elem (i - k.val)⌝ ∗ p.readable depth vs ⦄ :=
  RawPtr.offset_elem.spec_rangeWith (fun v bytes => (Pointee.repr (T := T)).decode bytes = some v) depth p vs i
    (-(k.val : Int)) (i - k.val) hne hi (by omega)
    (by omega)

/-- `offset` (by a nonnegative count) from the start of a readable range (for instance the result
of `as_ptr`). -/
theorem RawPtr.offset.spec_readable_head {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (depth : Nat) (vs : List T) (k : Isize) (hne : 0 < vs.length) (hlo : 0 ≤ k.val)
    (hle : k.val ≤ vs.length) :
    ⦃ p.readable depth vs ⦄ RawPtr.offset p k
      ⦃ r => ⌜r = p.elem k.val.toNat⌝ ∗ p.readable depth vs ⦄ := by
  simpa only [RawPtr.elem_zero, Nat.cast_zero, Int.zero_add] using
    RawPtr.offset.spec_readable p depth vs 0 k hne (by omega) (by omega) (by omega)

end Aeneas.Std
