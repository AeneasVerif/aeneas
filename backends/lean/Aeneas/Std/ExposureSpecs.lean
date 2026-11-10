/- Separation-logic specifications of the exposures of `MaybeUninit` values and slices, of
`ptr::from_ref`, and of the reborrows `&*p` and `&mut *p`. -/
module
public import Aeneas.Std.UninitSpecs
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Core.RawPtrOps
import all Aeneas.Std.Core.MaybeUninit
import all Aeneas.Std.Slice
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import Aeneas.Tactic.Solver.ScalarTac
@[expose] public section

/-! # Exposures of `MaybeUninit` values and slices, `from_ref`, `&*p` and `&mut *p`

Specifications of the models of `Std/Core/MaybeUninit.lean` and of `ptr::from_ref`,
`as_ref_unchecked` (`&*p`) and `as_mut_unchecked` (`&mut *p`) of `Std/Core/RawPtrOps.lean`, in the
style of `RawPtrSpecs.lean` (see `UninitSpecs.lean` for `p ↦?* values`).

- Pure functions (`@[step]`): `MaybeUninit::{uninit, new, assume_init, clone}`. `assume_init`
  of `⟨none⟩` fails (`assume_init_none`).
- Mutable exposures (`MaybeUninit::as_mut_ptr`, and `as_mut_ptr` on slices of `MaybeUninit U`):
  the exposed pointer, cast to `U`, owns `↦?* values` (uninitialized values are exposed as
  uninitialized bytes) and the exposure. The backward computation reads the values back: they
  refine the final cells (`MaybeUninit.Refines result cells`: every element known to be
  `⟨some v⟩` is read back as `⟨some v⟩`; the other ones are `⟨some _⟩` exactly when their bytes
  decode).
- Shared exposures (`MaybeUninit::as_ptr`, and `as_ptr` on slices of `MaybeUninit U`): the cast
  pointer has `p.uninitShared 1 values`: cells shared once, whose bytes decode to `v` for
  `⟨some v⟩`, and are exactly uninitialized for `⟨none⟩` (they can be neither read nor written). It
  is `p.readable 1 xs` for initialized values (`uninitShared_some`). Its end checks that the cells
  are unchanged, which needs the uninitialized bytes not to decode if some value is uninitialized
  (`Repr.uscalar_decode_uninit` for the integers).
- `from_raw_parts` on the initialized prefix of a buffer, exclusive (`spec_uninit_prefix`) or
  shared (`spec_uninitShared_prefix`), and on readable ranges (`spec_readable`).
- `ptr::from_ref` (and `&raw const place`): a shared exposure, `p.readable 1 [v] ∗ p.exposure 1`.
- `&*p` (`as_ref_unchecked`) shares the cell once more (`q.range d`, `q.readable d`, and an
  initialized element of `↦?*`), until its backward computation ends the share.
- `&mut *p` (`as_mut_unchecked`) borrows the cell (`q ↦† 1`).

Not specified, as the separation logic can't justify them: the ends of shares and borrows which
make cells exclusive again (`endShareRange` from depth `1` to `0`, which ends `&*p` on exclusive
cells and `from_raw_parts` on a `↦?*` prefix; and `endBorrow`, the backward computation of
`&mut *p`). While cells are shared or borrowed, a new exposure (whose address is chosen by the
caller) may overlap them, which is compatible with shared or borrowed cells but not with exclusive
ones: the end can then fail. (The other specifications of `RawPtrSpecs.lean`, such as
`RawPtr.endShareRange.spec`, also require the cells to stay shared.) -/

namespace Aeneas.Std

open Aeneas.SepLogic Aeneas.Std.WP core.mem.maybe_uninit

set_option maxHeartbeats 1000000

/-! ## Pure specifications -/

namespace core.mem.maybe_uninit.MaybeUninit

@[step]
theorem uninit.spec (T : Type) : MaybeUninit.uninit T ⦃ r => r = ⟨none⟩ ⦄ := by
  simp [MaybeUninit.uninit, spec_ok]

@[step]
theorem new.spec {T : Type} (v : T) : MaybeUninit.new v ⦃ r => r = ⟨some v⟩ ⦄ := by
  simp [MaybeUninit.new, spec_ok]

@[step]
theorem assume_init.spec {T : Type} (v : T) :
    MaybeUninit.assume_init ⟨some v⟩ ⦃ r => r = v ⦄ := by
  simp [MaybeUninit.assume_init, spec_ok]

theorem assume_init.spec_of_eq {T : Type} (x : MaybeUninit T) (v : T) (hx : x.value = some v) :
    MaybeUninit.assume_init x ⦃ r => r = v ⦄ := by
  simp [MaybeUninit.assume_init, hx, spec_ok]

/-- Reading an uninitialized value is undefined behavior. -/
theorem assume_init_none {T : Type} : MaybeUninit.assume_init (⟨none⟩ : MaybeUninit T) = .fail .undef :=
  rfl

@[step]
theorem Insts.CoreCloneClone.clone.spec {T : Type} (c : core.marker.Copy T)
    (x : SharedBorrow (MaybeUninit T)) :
    MaybeUninit.Insts.CoreCloneClone.clone c x ⦃ r => r = x.val ⦄ := by
  simp [MaybeUninit.Insts.CoreCloneClone.clone, spec_ok]

end core.mem.maybe_uninit.MaybeUninit

/-! ## The bytes of an exposure of possibly uninitialized values -/

/-- The bytes `bytes` are those of an exposure of `m`: exactly uninitialized bytes for `⟨none⟩`
(see `State.exposesUninit`), and bytes which decode to `v` for `⟨some v⟩`. -/
def MaybeUninit.Exposes {T : Type} (repr : Repr T) (m : MaybeUninit T)
    (bytes : Vector Byte repr.size) : Prop :=
  match m.value with
  | none => bytes = Vector.replicate repr.size .uninit
  | some v => repr.decode bytes = some v

theorem MaybeUninit.Exposes.decodes {T : Type} {repr : Repr T} {m : MaybeUninit T}
    {bytes : Vector Byte repr.size} (h : MaybeUninit.Exposes repr m bytes) :
    MaybeUninit.Decodes repr m bytes := by
  intro v hv
  rcases m with ⟨_ | w⟩
  · cases hv
  · cases hv; exact h

@[simp] theorem MaybeUninit.exposes_some {T : Type} (repr : Repr T) (v : T)
    (bytes : Vector Byte repr.size) :
    MaybeUninit.Exposes repr ⟨some v⟩ bytes ↔ repr.decode bytes = some v := Iff.rfl

theorem State.exposesUninit_index {T : Type} (repr : Repr T) (s : State) (address : Nat)
    (values : List (MaybeUninit T)) (data : List (Vector Byte repr.size))
    (h : State.exposesUninit repr s address values data) :
    ∃ (len : data.length = values.length), ∀ i (hi : i < values.length),
      MaybeUninit.Exposes repr values[i] (data[i]'(len ▸ hi)) := by
  induction values generalizing data address with
  | nil =>
    cases data with
    | nil => exact ⟨rfl, fun i hi => by simp at hi⟩
    | cons _ _ => simp [State.exposesUninit] at h
  | cons value values ih =>
    cases data with
    | nil => rcases value with ⟨_ | _⟩ <;> simp [State.exposesUninit] at h
    | cons bytes data =>
      have hhead : MaybeUninit.Exposes repr value bytes ∧
          State.exposesUninit repr s (address + repr.size) values data := by
        rcases value with ⟨_ | v⟩
        · simpa [State.exposesUninit, MaybeUninit.Exposes] using h
        · simp only [State.exposesUninit] at h
          exact ⟨h.1.1, h.2⟩
      obtain ⟨len, rest⟩ := ih _ data hhead.2
      refine ⟨by simp [len], fun i hi => ?_⟩
      cases i with
      | zero => simpa using hhead.1
      | succ i => simpa using rest i (by simpa using hi)

/-- The resources of a fresh exposure of possibly uninitialized values. -/
theorem Bytes.createUninit.post {T : Type} (repr : Repr T) (values : List (MaybeUninit T))
    (depth : Nat) (data : List (Vector Byte repr.size)) (bptr : BasePtr) (root : Option Nat)
    (s₀ s₁ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) (id : Nat)
    (aligned : repr.align.val ∣ bptr.val)
    (exposed : State.exposesUninit repr s₀ bptr.val values data)
    (created : s₀.createRepr
      ⟨bptr, root.getD s₀.next, repr.create data depth, false, true, true⟩ = some (id, s₁)) :
    ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧
      (Bytes.alloc repr ⟨id, bptr⟩ bptr values.length false ∗ᵇ
        Bytes.rangeWith repr (MaybeUninit.Exposes repr) ⟨id, bptr⟩ bptr (listVec values)
          depth) h := by
  obtain ⟨len, each⟩ := State.exposesUninit_index repr s₀ bptr.val values data exposed
  let bytes : Vector (Vector Byte repr.size) values.length := ⟨data.toArray, by simp [len]⟩
  have bytesList : bytes.toList = data := by simp [bytes]
  obtain ⟨h, hd, hm, hi, a, b, hab, hh, ha, hb⟩ :=
    create_range_resources repr bytes depth bptr root s₀ s₁ id aligned hi F hm
      (by simpa only [bytesList] using created)
  exact ⟨h, hd, hm, hi, a, b, hab, hh, ha, bytes,
    fun i => by simpa [bytes] using each i.val i.isLt, hb⟩

theorem Bytes.newBlockUninit.post {T : Type} (repr : Repr T) (values : List (MaybeUninit T))
    (data : List (Vector Byte repr.size)) (bptr : BasePtr) (root : Option Nat)
    (s₀ s₁ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) (q : RawPtr T)
    (exposed : State.exposesUninit repr s₀ bptr.val values data)
    (created : Heap.newBlock repr data false bptr root s₀ = some (q, s₁)) :
    ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧ q.address = bptr ∧
      (Bytes.alloc repr q q.address values.length false ∗ᵇ
        Bytes.rangeWith repr (MaybeUninit.Exposes repr) q q.address (listVec values) 0) h := by
  unfold Heap.newBlock at created
  simp only [Bool.not_false, Bool.true_or, Bool.and_true] at created
  split at created
  · rename_i aligned
    obtain ⟨⟨id, result⟩, run, he⟩ := Option.map_eq_some_iff.mp created
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨h, hd, hm, hi, hA⟩ := Bytes.createUninit.post repr values 0 data bptr root s₀ _ F
      hi hm id (of_decide_eq_true aligned) exposed run
    exact ⟨h, hd, hm, hi, rfl, hA⟩
  · contradiction

theorem Bytes.newSharedUninit.post {T : Type} (repr : Repr T) (values : List (MaybeUninit T))
    (data : List (Vector Byte repr.size)) (bptr : BasePtr) (root : Option Nat)
    (s₀ s₁ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) (q : RawPtr T)
    (exposed : State.exposesUninit repr s₀ bptr.val values data)
    (created : Heap.newSharedExposure repr data bptr root s₀ = some (q, s₁)) :
    ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧ q.address = bptr ∧
      (Bytes.alloc repr q q.address values.length false ∗ᵇ
        Bytes.rangeWith repr (MaybeUninit.Exposes repr) q q.address (listVec values) 1) h := by
  unfold Heap.newSharedExposure at created
  split at created
  · rename_i aligned
    obtain ⟨⟨id, result⟩, run, he⟩ := Option.map_eq_some_iff.mp created
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨h, hd, hm, hi, hA⟩ := Bytes.createUninit.post repr values 1 data bptr root s₀ _ F
      hi hm id aligned exposed run
    exact ⟨h, hd, hm, hi, rfl, hA⟩
  · contradiction

/-! ## Reading back and retiring exposures -/

section
open Bytes

theorem whole_rangeWith {T V : Type} (repr : Repr T) (valid : V → Vector Byte repr.size → Prop)
    (p : RawPtr T) (values : Vector V count) (depth : Nat) (h : Fragment) (s : Heap)
    (hp : (alloc repr p p.address count false ∗ᵇ
      rangeWith repr valid p p.address values depth) h)
    (hm : Fragment.Matches s h) :
    ∃ blk, s.allocations p.provenance = some blk ∧ s.live blk = true ∧
      p.address = blk.bptr ∧ repr.align.val ∣ blk.bptr.val ∧ blk.owned = false ∧
      blk.repr.length = count * repr.size ∧
      blk.repr.all (fun cell => cell.depth == some depth) = true ∧
      h = Fragment.single (.cleanup p.provenance blk.repr.length blk.bptr blk.owned) ∪
        cellsHeap blk.bptr p.provenance 0 blk.repr := by
  obtain ⟨a, b, _, rfl, ⟨_, rfl⟩, data, _, _, ha, rfl⟩ := hp
  obtain ⟨hma, hmb⟩ := (Fragment.matches_union _ _ _).mp hm
  obtain ⟨blk, hl, hlen, hlive, hbptr, hown⟩ := hma _ rfl
  have hrepr : blk.repr =
      (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList := by
    by_cases hz : count * repr.size = 0
    · have empty : blk.repr = [] := List.eq_nil_of_length_eq_zero (hlen.trans hz)
      simp [empty, Vector.toList_eq_nil_iff, hz]
    · obtain ⟨actual, hb, hl', _, _, selected⟩ :=
        bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
          (data := data.flatMap (fun b => b.map (Cell.shared depth)))
          (by simp only [Repr.region]; omega) hmb
      have he : actual = blk := Option.some.inj (hl'.symm.trans hl)
      subst actual
      have hs := congrArg Vector.toList selected
      have ht : blk.repr.take (count * repr.size) = blk.repr := by
        rw [← hlen, List.take_length]
      simpa [Repr.select_toList, Block.bytes, hbptr, RawPtr.offsetFrom, RawPtr.cast,
        Repr.region, ht] using hs
  refine ⟨blk, hl, hlive, hbptr.symm, hbptr ▸ ha, hown, hlen, ?_, ?_⟩
  · have hrepr' : blk.repr =
        data.toList.flatMap (fun b => b.toList.map (Cell.shared depth)) := by
      simpa [Vector.flatMap, Vector.toList] using hrepr
    simp [hrepr', Cell.depth]
  · simp [allocHeap, hbptr, hown, hrepr, RawPtr.offsetFrom]

theorem end_rangeWith_exposure.spec {T V : Type} (repr : Repr T)
    (valid : V → Vector Byte repr.size → Prop) (p : RawPtr T) (values : Vector V count)
    (depth : Nat) :
    LocalOp
      (alloc repr p p.address count false ∗ᵇ rangeWith repr valid p p.address values depth)
      (fun s (_ : Unit) s' => Heap.endExposureAt repr p count depth s = some s')
      (fun _ => empty) := by
  intro h F s hp hd hm hi
  obtain ⟨blk, hl, live, addr, aligned, own, len, depths, whole⟩ :=
    whole_rangeWith repr valid p values depth h s hp ((Fragment.matches_union _ _ _).mp hm).1
  have preserved := Heap.retire_Inv hi p.provenance
  have commit : Heap.commit (s.retire p.provenance) = some (s.retire p.provenance) := by
    simp [Heap.commit, preserved.2]
  have run : Heap.endExposureAt repr p count depth s = some (s.retire p.provenance) := by
    have hd : ∀ cell ∈ blk.repr, cell.depth = some depth := by
      simpa [-Cell.depth] using depths
    simp [-Cell.depth, Heap.endExposureAt, hl, live, addr, aligned, own, len, commit]
    exact hd
  obtain ⟨_, post⟩ := retire.spec s p.provenance blk hl h F whole hd hm hi
  refine ⟨⟨(), _, run⟩, ?_⟩
  intro _ s' he
  have hs : s' = s.retire p.provenance := Option.some.inj (he.symm.trans run)
  subst s'
  exact post () _ commit

end

/-- Retiring an exposure whose element bytes satisfy any predicate. -/
theorem Bytes.endExposure.local_rangeWith {T V : Type} (repr : Repr T)
    (valid : V → Vector Byte repr.size → Prop) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector V count) (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Bytes.LocalOp
      (Bytes.alloc repr p p.address count false ∗ᵇ Bytes.rangeWith repr valid p bptr values depth)
      (fun s (_ : Unit) s' => Heap.endExposureAt repr p count depth s = some s')
      (fun _ => Bytes.empty) := by
  intro h F s hp hd hm hi
  obtain ⟨a, b, hab, rfl, ha, hb⟩ := id hp
  have hmab := (Fragment.matches_union _ _ _).mp ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨data, _, hblock⟩ := id hb
  have hlen : 0 < (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList.length := by
    simp; exact ⟨hcount, hsize⟩
  have hbptr := Bytes.bptr_eq_of_matches hlen ha hblock hmab.1 hmab.2
  subst hbptr
  exact end_rangeWith_exposure.spec repr valid p values depth _ F s hp hd hm hi

/-- Retiring an exposure keeps the authority, whatever the precondition. -/
theorem Bytes.endExposure.auth_any {T : Type} (repr : Repr T) (p : RawPtr T) (count depth : Nat)
    (A : Fragment → Prop) {op : Heap → Unit → Heap → Prop}
    (hop : ∀ s x s', op s x s' → Heap.endExposureAt repr p count depth s = some s') :
    Bytes.AuthPres A op (fun _ => Bytes.empty) := by
  refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.empty h) ?_
  rintro a F s _ _ _ _ x s' hx _ _ _ _ _ base hEx _
  obtain rfl := Heap.endExposureAt_run (hop s x s' hx)
  exact retire_step base hEx

/-- The values read back from a range: the decodings of its element bytes. -/
theorem Heap.readUninitRange_of_rangeWith {T V : Type} {s : Heap} {repr : Repr T}
    {valid : V → Vector Byte repr.size → Prop} {p : RawPtr T} {bptr : BasePtr}
    {values : Vector V count} {depth : Nat} {h : Fragment}
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (hp : Bytes.rangeWith repr valid p bptr values depth h) (hm : Fragment.Matches s h) :
    ∃ data : Vector (Vector Byte repr.size) count,
      (∀ i : Fin count, valid values[i.val] data[i.val]) ∧
      Heap.readUninitRange repr p count s =
        some (data.toList.map fun bytes => (⟨repr.decode bytes⟩ : MaybeUninit T)) := by
  obtain ⟨data, hvalid, hlo, hpa, rfl⟩ := hp
  refine ⟨data, hvalid, ?_⟩
  obtain ⟨blk, hb, hl, hlive, ha, hs⟩ := Bytes.bytes_of_matches (repr := repr.region count)
    (p := p.cast Unit) (data := data.flatMap (fun bytes => bytes.map (Cell.shared depth)))
    (Nat.mul_pos hcount hsize) hm
  change p.offsetFrom bptr + count * repr.size ≤ blk.repr.length at hb
  change s.allocations p.provenance = some blk at hl
  subst ha
  have hr (i : Nat) (hi : i < count) :
      (if h : p.offsetFrom blk.bptr + i * repr.size + repr.size ≤ blk.repr.length then
        (Repr.readBytes repr.size
          (repr.select blk.bytes (p.offsetFrom blk.bptr + i * repr.size) h)).map
            fun bytes => (⟨repr.decode bytes⟩ : MaybeUninit T)
      else none) = some ⟨repr.decode data[i]⟩ := by
    have hsel := repr.select_region blk.bytes (p.offsetFrom blk.bptr) count
      (data.map fun bytes => bytes.map (Cell.shared depth)) hb
      (by simpa [Vector.flatMap_map, Repr.region, RawPtr.cast, RawPtr.offsetFrom] using hs) i hi
    simp only [Vector.getElem_map] at hsel
    simp [range_element_bound hi hb, hsel, Repr.readBytes_shared]
  have hmap := mapM_range'_some (data.toList.map fun bytes => (⟨repr.decode bytes⟩ : MaybeUninit T))
    0 (f := fun i => if h : p.offsetFrom blk.bptr + i * repr.size + repr.size ≤ blk.repr.length then
        (Repr.readBytes repr.size
          (repr.select blk.bytes (p.offsetFrom blk.bptr + i * repr.size) h)).map
            fun bytes => (⟨repr.decode bytes⟩ : MaybeUninit T)
      else none)
    (fun i hi => by simpa using hr i (by simpa using hi))
  have bound : p.address.val + count * repr.size ≤ blk.bptr.val + blk.repr.length := by
    simp only [RawPtr.offsetFrom] at hb
    omega
  simp only [List.length_map, Vector.length_toList] at hmap
  simpa [Heap.readUninitRange, hl, hlive, hpa, bound, hlo, List.range_eq_range'] using hmap

/-! ## Shared possibly uninitialized ranges -/

namespace RawPtr

/-- `p.uninitShared depth values`: one chunk of cells per element of `values`, shared `depth`
times, one after the other from `p` on in some block, which are the bytes of an exposure of the
element (`MaybeUninit.Exposes`): bytes which decode to `v` for `⟨some v⟩`, and exactly
uninitialized bytes for `⟨none⟩`. It is the view given by the shared exposures of `MaybeUninit`
values (`as_ptr`); `p.uninitShared d (xs.map (⟨some ·⟩)) = p.readable d xs`
(`uninitShared_some`). -/
def uninitShared {T : Type} [Pointee T] (p : RawPtr T) (depth : Nat)
    (values : List (MaybeUninit T)) : IProp :=
  iexists fun bptr : BasePtr => upClose (Bytes.rangeWith (Pointee.repr (T := T))
    (MaybeUninit.Exposes (Pointee.repr (T := T))) p bptr (listVec values) depth)

end RawPtr

theorem uninitShared_some {T : Type} [Pointee T] (p : RawPtr T) (d : Nat) (xs : List T) :
    p.uninitShared d (xs.map fun v => ⟨some v⟩) = p.readable d xs := by
  apply entails_antisymm
  · rintro h ⟨bptr, a, ha, hsub⟩
    exact ⟨bptr, a, Bytes.rangeWith_list_imp
      (valid' := fun v bytes => (Pointee.repr (T := T)).decode bytes = some v) _ xs (by simp)
      (fun i _ _ bytes he => by simpa using he) ha, hsub⟩
  · rintro h ⟨bptr, a, ha, hsub⟩
    exact ⟨bptr, a, Bytes.rangeWith_list_imp
      (valid := fun v bytes => (Pointee.repr (T := T)).decode bytes = some v) xs _ (by simp)
      (fun i _ _ bytes he => by simpa using he) ha, hsub⟩

theorem uninitShared_singleton_some {T : Type} [Pointee T] (p : RawPtr T) (d : Nat) (v : T) :
    p.uninitShared d [⟨some v⟩] = p.readable d [v] := by
  simpa using uninitShared_some p d [v]

/-- Splits a shared possibly uninitialized range at any index. -/
theorem uninitShared_split_real {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (d : Nat) (xs ys : List (MaybeUninit T)) :
    RealEntails (p.uninitShared d (xs ++ ys))
      (p.uninitShared d xs ∗ (p.elem xs.length).uninitShared d ys) := by
  refine RealEntails.of_matches fun s h hi hm hP => ?_
  obtain ⟨bptr, a, ha, hsub⟩ := hP
  have hfit : p.address.val + xs.length * (Pointee.repr (T := T)).size <
      2 ^ UScalarTy.numBits .Usize := by
    by_cases hx : xs.length = 0
    · rw [hx, Nat.zero_mul, Nat.add_zero]
      exact p.address.bv.isLt
    · have hb := Bytes.rangeWith_bound _ _ p bptr _ d (by simp; omega) Pointee.Sized.pos a s ha
        (Fragment.matches_of_subheap hsub hm) hi
      have := Nat.mul_le_mul_right (Pointee.repr (T := T)).size
        (show xs.length ≤ (xs ++ ys).length by simp)
      omega
  have hs := (Bytes.rangeWith_append _ _ p (p.elem xs.length) bptr xs ys d
    (RawPtr.elem_provenance p _) (RawPtr.elem_address p _ hfit) a).mp ha
  obtain ⟨h₁, h₂, hd, he, hA, hB⟩ := upClose_sep _ ⟨a, hs, hsub⟩
  exact ⟨h₁, h₂, hd, he, ⟨bptr, hA⟩, ⟨bptr, hB⟩⟩

/-- Merges two adjacent shared possibly uninitialized ranges. -/
theorem uninitShared_merge {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T) (d : Nat)
    (xs ys : List (MaybeUninit T)) :
    RealEntails (p.uninitShared d xs ∗ (p.elem xs.length).uninitShared d ys)
      (p.uninitShared d (xs ++ ys)) := by
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
    exact ⟨b₂, b, hb, (PartialCommMonoid.Subheap.union_right hab).trans hsub⟩
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
  have hfit := Bytes.rangeWith_bound _ _ p b₁ _ d hxl hsize a s ⟨da, hva, hbla⟩ hma hi
  refine ⟨b₁, a ∪ b, ?_, hsub⟩
  exact (Bytes.rangeWith_append _ _ p (p.elem xs.length) b₁ xs ys d
    (RawPtr.elem_provenance p _) (RawPtr.elem_address p _ (by simpa using hfit)) _).mpr
    ⟨a, b, hab, rfl, ⟨da, hva, hbla⟩, ⟨db, hvb, hblb⟩⟩

/-! ## Allocating and retiring the exposures of possibly uninitialized values -/

/-- Exposes possibly uninitialized values, mutably, at `address`: the pointer (cast to `T`) owns
`↦?* values`, uninitialized values being exposed as uninitialized bytes. -/
@[step]
theorem MaybeUninit.allocExposure.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (values : List (MaybeUninit T)) (address : BasePtr) (hne : 0 < values.length) :
    ⦃ emp ⦄ MaybeUninit.allocExposure (Pointee.repr (T := T)) values address
      ⦃ p => ⌜(p.cast T).address = address⌝ ∗
        ((p.cast T) ↦?* values ∗ (p.cast T).exposure values.length) ⦄ := by
  have h := ispec_allocating_emp (A := fun p h => (p.cast T).address = address ∧
      (Bytes.alloc (Pointee.repr (T := T)) (p.cast T) (p.cast T).address values.length false ∗ᵇ
        Bytes.rangeWith (Pointee.repr (T := T)) (MaybeUninit.Exposes (Pointee.repr (T := T)))
          (p.cast T) (p.cast T).address (listVec values) 0) h)
    (modify := State.exposeUninitAt (Pointee.repr (T := T)) values address)
    (fun s F hi hm hAuth p s₁ hx => by
      obtain ⟨data, root, exposed, created⟩ := hx
      obtain ⟨len, _⟩ := State.exposesUninit_index _ s address.val values data exposed
      obtain ⟨h, hd, hm', hi', haddr, hA⟩ := Bytes.newBlockUninit.post _ values data address root
        s s₁ F hi hm (p.cast T) exposed created
      have hs := Heap.newBlock_fresh created
      subst hs
      exact ⟨h, hd, hm', hi', exposure_authOK hi hm hAuth
        (NoOwned.sep (fun _ ha => NoOwned.alloc_false ha)
          (fun _ hb => Bytes.NoOwned_rangeWith hb) hA)
        (by omega) Pointee.Sized.pos hi', haddr, hA⟩)
  refine ispec_conseq h (entails_refl _) (fun p => ?_)
  refine entails_trans upClose_pure_and (sep_mono (entails_refl _) ?_)
  refine entails_trans upClose_sep ?_
  refine entails_trans (entails_of_eq (sep_comm_eq _ _)) ?_
  refine sep_mono ?_ (entails_refl _)
  rintro h ⟨a, ha, hsub⟩
  exact ⟨(p.cast T).address, a, Bytes.rangeWith_imp _ _ rfl
    (fun _ _ _ _ hb => MaybeUninit.Exposes.decodes hb) ha, hsub⟩

/-- Exposes possibly uninitialized values, read-only, at `address`. -/
@[step]
theorem MaybeUninit.allocSharedExposure.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (values : List (MaybeUninit T)) (address : BasePtr) (hne : 0 < values.length) :
    ⦃ emp ⦄ MaybeUninit.allocSharedExposure (Pointee.repr (T := T)) values address
      ⦃ p => ⌜(p.cast T).address = address⌝ ∗
        ((p.cast T).uninitShared 1 values ∗ (p.cast T).exposure values.length) ⦄ := by
  have h := ispec_allocating_emp (A := fun p h => (p.cast T).address = address ∧
      (Bytes.alloc (Pointee.repr (T := T)) (p.cast T) (p.cast T).address values.length false ∗ᵇ
        Bytes.rangeWith (Pointee.repr (T := T)) (MaybeUninit.Exposes (Pointee.repr (T := T)))
          (p.cast T) (p.cast T).address (listVec values) 1) h)
    (modify := State.sharedExposeUninitAt (Pointee.repr (T := T)) values address)
    (fun s F hi hm hAuth p s₁ hx => by
      obtain ⟨data, root, exposed, created⟩ := hx
      obtain ⟨len, _⟩ := State.exposesUninit_index _ s address.val values data exposed
      obtain ⟨h, hd, hm', hi', haddr, hA⟩ := Bytes.newSharedUninit.post _ values data address root
        s s₁ F hi hm (p.cast T) exposed created
      have hs := Heap.newSharedExposure_fresh created
      subst hs
      exact ⟨h, hd, hm', hi', exposure_authOK hi hm hAuth
        (NoOwned.sep (fun _ ha => NoOwned.alloc_false ha)
          (fun _ hb => Bytes.NoOwned_rangeWith hb) hA)
        (by omega) Pointee.Sized.pos hi', haddr, hA⟩)
  refine ispec_conseq h (entails_refl _) (fun p => ?_)
  refine entails_trans upClose_pure_and (sep_mono (entails_refl _) ?_)
  refine entails_trans upClose_sep ?_
  refine entails_trans (entails_of_eq (sep_comm_eq _ _)) ?_
  exact sep_mono (fun h hU => ⟨(p.cast T).address, hU⟩) (entails_refl _)

/-- Reads back the values of a possibly uninitialized range: they refine it (an element known to be
`⟨some v⟩` is read back as `⟨some v⟩`; the other ones are `⟨some _⟩` if their bytes decode). -/
theorem readUninitRange.spec {T : Type} [Pointee T] [Pointee.Sized T] (q : RawPtr T)
    (vs : List (MaybeUninit T)) (hne : 0 < vs.length) :
    ⦃ q ↦?* vs ⦄ Result.checkedModify (fun s values s' =>
        Heap.readUninitRange (Pointee.repr (T := T)) q vs.length s = some values ∧ s' = s)
      ⦃ r => ⌜MaybeUninit.Refines r vs⌝ ∗ q ↦?* vs ⦄ := by
  refine ispec_conseq (ispec_checked_local
    (B := fun bptr r h => MaybeUninit.Refines r vs ∧
      Bytes.uninitRange (Pointee.repr (T := T)) q bptr (listVec vs) h)
    (fun bptr => ?_)
    (fun _ => Bytes.AuthPres.of_eq (fun _ _ h => Bytes.NoOwned_rangeWith h.2)
      (fun _ _ _ h => h.2)))
    (entails_refl _) (fun _ => iexists_upClose_pure_and)
  intro h F s hp hd hm hi
  obtain ⟨data, hvalid, hrd⟩ := Heap.readUninitRange_of_rangeWith hne Pointee.Sized.pos hp
    ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨_, s, hrd, rfl⟩, ?_⟩
  rintro x s' ⟨hx, rfl⟩
  have := Option.some.inj (hx.symm.trans hrd)
  subst this
  refine ⟨h, hd, hm, hi, ⟨by simp, fun i hx hy v hv => ?_⟩, hp⟩
  have := hvalid ⟨i, hy⟩ v (by simpa [listVec] using hv)
  simp [this]

/-- Retires a mutable exposure whose cells are a possibly uninitialized range. -/
theorem RawPtr.endExposure.spec_uninit {T : Type} [Pointee T] [Pointee.Sized T] (q : RawPtr T)
    (vs : List (MaybeUninit T)) (hne : 0 < vs.length) :
    ⦃ q ↦?* vs ∗ q.exposure vs.length ⦄ RawPtr.endExposure (Pointee.repr (T := T)) q vs.length
      ⦃ emp ⦄ := by
  have hEq : q ↦?* vs ∗ q.exposure vs.length ⊢
      iexists fun bptr => upClose (Bytes.alloc (Pointee.repr (T := T)) q q.address
        vs.length false ∗ᵇ Bytes.uninitRange (Pointee.repr (T := T)) q bptr (listVec vs)) := by
    rintro h ⟨h₁, h₂, hd, rfl, ⟨bptr, hR⟩, hE⟩
    obtain ⟨c, ⟨a, b, hab, rfl, ha, hb⟩, hsc⟩ := sep_upClose _
      ⟨h₂, h₁, hd.symm, Fragment.union_comm _ _, hE, hR⟩
    exact ⟨bptr, a ∪ b, ⟨a, b, hab, rfl, ha, hb⟩, hsc⟩
  exact ispec_conseq (ispec_checked_local (modify := State.removeExposure
    (Pointee.repr (T := T)) q vs.length) (B := fun _ _ => Bytes.empty)
    (fun bptr => Bytes.endExposure.local_rangeWith _ _ q bptr (listVec vs) 0 hne
      Pointee.Sized.pos)
    (fun bptr => Bytes.endExposure.auth_any _ q vs.length 0 _ (fun _ _ _ h => h))) hEq
    (fun _ _ _ => trivial)

/-- Ends a mutable exposure of possibly uninitialized values: the values read back refine the
final cells. -/
@[step]
theorem RawPtr.endUninitExposure.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (p : RawPtr (MaybeUninit T)) (vs : List (MaybeUninit T)) (hne : 0 < vs.length) :
    ⦃ (p.cast T) ↦?* vs ∗ (p.cast T).exposure vs.length ⦄
      p.endUninitExposure (Pointee.repr (T := T)) vs.length
      ⦃ r => ⌜MaybeUninit.Refines r vs⌝ ⦄ := by
  unfold RawPtr.endUninitExposure
  apply ispec_bind (readUninitRange.spec (p.cast T) vs hne) (entails_refl _)
  intro values
  rw [sep_assoc_eq, ispec_ipure]
  intro href
  apply ispec_bind (RawPtr.endExposure.spec_uninit (p.cast T) vs hne)
    (entails_of_eq (sep_emp_r_eq _).symm)
  intro _
  apply ispec_ok
  exact entails_trans (entails_of_eq (sep_emp_r_eq _))
    (entails_trans (pure_sep_intro emp href) (entails_of_eq (sep_emp_r_eq _)))

/-- The values read back from the exact bytes of an exposure: the original ones, if the
uninitialized bytes don't decode. -/
theorem MaybeUninit.Exposes.map_decode {T : Type} (repr : Repr T) (vs : List (MaybeUninit T))
    (data : Vector (Vector Byte repr.size) vs.length)
    (h : ∀ i : Fin vs.length, MaybeUninit.Exposes repr (listVec vs)[i.val] data[i.val])
    (huninit : ⟨none⟩ ∈ vs → repr.decode (Vector.replicate repr.size .uninit) = none) :
    data.toList.map (fun bytes => (⟨repr.decode bytes⟩ : MaybeUninit T)) = vs := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  have hi := h ⟨i, h₂⟩
  simp only [listVec, Vector.getElem_mk, List.getElem_toArray] at hi
  simp only [List.getElem_map, Vector.getElem_toList]
  have hmem : vs[i] ∈ vs := List.getElem_mem h₂
  generalize vs[i] = m at hi hmem ⊢
  rcases m with ⟨_ | v⟩
  · simp only [MaybeUninit.Exposes] at hi
    rw [hi, huninit hmem]
  · simp only [MaybeUninit.Exposes] at hi
    rw [hi]

/-- Ends a shared exposure of possibly uninitialized values: the cells must still be the bytes of
the exposure. `huninit`: if some value is uninitialized, uninitialized bytes don't decode (it holds
for the scalars, see `Repr.uscalar_decode_uninit`). -/
@[step]
theorem RawPtr.endSharedUninitExposure.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (p : RawPtr (MaybeUninit T)) (vs : List (MaybeUninit T)) (hne : 0 < vs.length)
    (huninit : ⟨none⟩ ∈ vs → (Pointee.repr (T := T)).decode (Vector.replicate _ .uninit) = none) :
    ⦃ (p.cast T).uninitShared 1 vs ∗ (p.cast T).exposure vs.length ⦄
      p.endSharedUninitExposure (Pointee.repr (T := T)) vs ⦃ emp ⦄ := by
  have hEq : (p.cast T).uninitShared 1 vs ∗ (p.cast T).exposure vs.length ⊢
      iexists fun bptr => upClose (Bytes.alloc (Pointee.repr (T := T)) (p.cast T)
        (p.cast T).address vs.length false ∗ᵇ Bytes.rangeWith (Pointee.repr (T := T))
          (MaybeUninit.Exposes (Pointee.repr (T := T))) (p.cast T) bptr (listVec vs) 1) := by
    rintro h ⟨h₁, h₂, hd, rfl, ⟨bptr, hR⟩, hE⟩
    obtain ⟨c, ⟨a, b, hab, rfl, ha, hb⟩, hsc⟩ := sep_upClose _
      ⟨h₂, h₁, hd.symm, Fragment.union_comm _ _, hE, hR⟩
    exact ⟨bptr, a ∪ b, ⟨a, b, hab, rfl, ha, hb⟩, hsc⟩
  refine ispec_conseq (ispec_checked_local (B := fun _ _ => Bytes.empty) (fun bptr => ?_)
    (fun bptr => Bytes.endExposure.auth_any _ (p.cast T) vs.length 1 _
      (fun _ _ _ h => h.2))) hEq (fun _ _ _ => trivial)
  intro h F s hp hd hm hi
  obtain ⟨_, b, _, rfl, _, hb⟩ := id hp
  obtain ⟨data, hvalid, hrd⟩ := Heap.readUninitRange_of_rangeWith hne Pointee.Sized.pos hb
    ((Fragment.matches_union _ _ _).mp ((Fragment.matches_union _ _ _).mp hm).1).2
  rw [MaybeUninit.Exposes.map_decode _ vs data hvalid huninit] at hrd
  obtain ⟨⟨_, s₁, he⟩, post⟩ := Bytes.endExposure.local_rangeWith _ _ (p.cast T) bptr
    (listVec vs) 1 hne Pointee.Sized.pos _ F s hp hd hm hi
  refine ⟨⟨(), s₁, hrd, he⟩, ?_⟩
  rintro _ s' ⟨_, he'⟩
  exact post () s' he'

/-- Uninitialized bytes don't decode to an integer (the hypothesis of the ends of the shared
exposures of uninitialized values). -/
theorem Repr.uscalar_decode_uninit (ty : UScalarTy) :
    (Pointee.repr (T := UScalar ty)).decode (Vector.replicate _ .uninit) = none := by
  have hpos : 0 < ty.numBits / 8 := ty.numBits_div_eight_pos
  obtain ⟨n, hn⟩ : ∃ n, ty.numBits / 8 = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  show (Vector.replicate _ Byte.uninit).toList.mapM Byte.numeric >>= _ = none
  rw [Vector.toList_replicate]
  rw [hn]
  simp [List.replicate_succ, Byte.numeric]

/-! ## `MaybeUninit::as_mut_ptr` and `MaybeUninit::as_ptr` -/

theorem MaybeUninit.Refines.singleton_some {T : Type} {r : MaybeUninit T} {v : T}
    (h : MaybeUninit.Refines [r] [⟨some v⟩]) : r = ⟨some v⟩ := by
  have := h.2 0 (by simp) (by simp) v rfl
  cases r
  simp_all

/-- A list which refines an initialized prefix `xs` followed by anything starts with `xs`. -/
theorem MaybeUninit.Refines.eq_append {T : Type} {xs : List T} {r ys : List (MaybeUninit T)}
    (h : MaybeUninit.Refines r (xs.map (fun v => ⟨some v⟩) ++ ys)) :
    r = xs.map (fun v => ⟨some v⟩) ++ r.drop xs.length := by
  have hl := h.1
  simp only [List.length_append, List.length_map] at hl
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  by_cases hi : i < xs.length
  · have := h.2 i h₁ (by simp; omega) xs[i] (by simp [List.getElem_append_left, hi])
    rw [List.getElem_append_left (by simpa using hi)]
    cases hr : r[i]
    simp_all
  · rw [List.getElem_append_right (by simpa using hi)]
    simp only [List.length_map, List.getElem_drop]
    congr 1
    omega

/-- The backward computation of `MaybeUninit::as_mut_ptr`, on the pointer it returns. -/
def MaybeUninit.end_as_mut_ptr {T : Type} [Pointee T] (q : MutRawPtr T) :
    Result (MaybeUninit T) := do
  match ← (q.cast (MaybeUninit T)).endUninitExposure (Pointee.repr (T := T)) 1 with
  | [value] => .ok value
  | _ => .fail .undef

/-- `MaybeUninit::as_mut_ptr` exposes the value at the address of its placement: the pointer owns
the cells of the value (uninitialized bytes if it is uninitialized). -/
theorem core.mem.maybe_uninit.MaybeUninit.as_mut_ptr.spec_at {T : Type} [Pointee T]
    [Pointee.Sized T] (address : BasePtr) (x : MutBorrow (MaybeUninit T)) :
    ⦃ emp ⦄ MaybeUninit.as_mut_ptr address x
      ⦃ (q, back) => ⌜q.address = address⌝ ∗ ⌜back = MaybeUninit.end_as_mut_ptr q⌝ ∗
        q ↦?* [x.val] ∗ q.exposure 1 ⦄ := by
  unfold MaybeUninit.as_mut_ptr
  apply ispec_bind (MaybeUninit.allocExposure.spec [x.val] address (by simp))
    (entails_of_eq (sep_emp_r_eq emp).symm)
  intro p
  rw [sep_assoc_eq, ispec_ipure]
  intro haddr
  apply ispec_ok
  have hb : MaybeUninit.end_as_mut_ptr (p.cast T) =
      (do match ← p.endUninitExposure (Pointee.repr (T := T)) 1 with
        | [value] => .ok value
        | _ => .fail .undef) := rfl
  simp only [uncurry_apply_pair, List.length_singleton, haddr]
  rw [hb]
  iframe

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.as_mut_ptr.spec {T : Type} [Pointee T]
    [Pointee.Sized T] (address : BasePtr) (x : MutBorrow (MaybeUninit T)) :
    ⦃ emp ⦄ MaybeUninit.as_mut_ptr address x
      ⦃ (q, back) => ⌜back = MaybeUninit.end_as_mut_ptr q⌝ ∗ q ↦?* [x.val] ∗ q.exposure 1 ⦄ :=
  ispec_conseq (as_mut_ptr.spec_at address x) (entails_refl _) (fun r => by
    obtain ⟨q, back⟩ := r
    simp only [uncurry_apply_pair]
    exact fun h hh => ((sep_pure_l _ _ h).mp hh).2)

/-- The backward computation of `MaybeUninit::as_mut_ptr`: the value read back refines the final
cells (it is `⟨some v⟩` if they are known to be `⟨some v⟩`, see `Refines.singleton_some`). -/
@[step]
theorem MaybeUninit.end_as_mut_ptr.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (q : MutRawPtr T) (m : MaybeUninit T) :
    ⦃ q ↦?* [m] ∗ q.exposure 1 ⦄ MaybeUninit.end_as_mut_ptr q
      ⦃ r => ⌜MaybeUninit.Refines [r] [m]⌝ ⦄ := by
  unfold MaybeUninit.end_as_mut_ptr
  have h := RawPtr.endUninitExposure.spec (q.cast (MaybeUninit T)) [m] (by simp)
  simp only [RawPtr.cast_cast, RawPtr.cast_self, List.length_singleton] at h
  apply ispec_bind h (entails_of_eq (sep_emp_r_eq _).symm)
  intro values
  rw [sep_emp_r_eq, ← sep_emp_r_eq ⌜_⌝, ispec_ipure]
  intro href
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (href.1.trans (by simp))
  apply ispec_ok
  exact entails_trans (pure_sep_intro emp href) (entails_of_eq (sep_emp_r_eq _))

/-- `MaybeUninit::as_ptr` exposes the value, read-only, at the address of its placement. If the
value is initialized, the view is `q.readable 1 [v]` (`uninitShared_singleton_some`, and
`as_ptr.spec_some`); if it is uninitialized, the cell is uninitialized bytes, which can't be read
or written through the pointer. -/
theorem core.mem.maybe_uninit.MaybeUninit.as_ptr.spec_at {T : Type} [Pointee T]
    [Pointee.Sized T] (address : BasePtr) (x : SharedBorrow (MaybeUninit T)) :
    ⦃ emp ⦄ MaybeUninit.as_ptr address x
      ⦃ (q, back) => ⌜q.address = address⌝ ∗
        ⌜back = (q.cast (MaybeUninit T)).endSharedUninitExposure (Pointee.repr (T := T)) [x.val]⌝ ∗
        q.uninitShared 1 [x.val] ∗ q.exposure 1 ⦄ := by
  unfold MaybeUninit.as_ptr
  apply ispec_bind (MaybeUninit.allocSharedExposure.spec [x.val] address (by simp))
    (entails_of_eq (sep_emp_r_eq emp).symm)
  intro p
  rw [sep_assoc_eq, ispec_ipure]
  intro haddr
  apply ispec_ok
  simp only [uncurry_apply_pair, List.length_singleton, RawPtr.cast_cast, RawPtr.cast_self, haddr]
  iframe

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.as_ptr.spec {T : Type} [Pointee T]
    [Pointee.Sized T] (address : BasePtr) (x : SharedBorrow (MaybeUninit T)) :
    ⦃ emp ⦄ MaybeUninit.as_ptr address x
      ⦃ (q, back) =>
        ⌜back = (q.cast (MaybeUninit T)).endSharedUninitExposure (Pointee.repr (T := T)) [x.val]⌝ ∗
        q.uninitShared 1 [x.val] ∗ q.exposure 1 ⦄ :=
  ispec_conseq (as_ptr.spec_at address x) (entails_refl _) (fun r => by
    obtain ⟨q, back⟩ := r
    simp only [uncurry_apply_pair]
    exact fun h hh => ((sep_pure_l _ _ h).mp hh).2)

/-- `MaybeUninit::as_ptr` on an initialized value. -/
theorem core.mem.maybe_uninit.MaybeUninit.as_ptr.spec_some {T : Type} [Pointee T]
    [Pointee.Sized T] (address : BasePtr) (x : SharedBorrow (MaybeUninit T)) (v : T)
    (hx : x.val = ⟨some v⟩) :
    ⦃ emp ⦄ MaybeUninit.as_ptr address x
      ⦃ (q, back) => ⌜q.address = address⌝ ∗
        ⌜back = (q.cast (MaybeUninit T)).endSharedUninitExposure (Pointee.repr (T := T))
          [⟨some v⟩]⌝ ∗ q.readable 1 [v] ∗ q.exposure 1 ⦄ := by
  have h := as_ptr.spec_at address x
  rw [hx] at h
  simpa only [uninitShared_singleton_some] using h

/-- The backward computation of `MaybeUninit::as_ptr`. -/
@[step]
theorem MaybeUninit.end_as_ptr.spec {T : Type} [Pointee T] [Pointee.Sized T] (q : ConstRawPtr T)
    (m : MaybeUninit T)
    (huninit : m = ⟨none⟩ → (Pointee.repr (T := T)).decode (Vector.replicate _ .uninit) = none) :
    ⦃ q.uninitShared 1 [m] ∗ q.exposure 1 ⦄
      (q.cast (MaybeUninit T)).endSharedUninitExposure (Pointee.repr (T := T)) [m] ⦃ emp ⦄ := by
  have h := RawPtr.endSharedUninitExposure.spec (q.cast (MaybeUninit T)) [m] (by simp)
    (fun hm => huninit (by simpa [eq_comm] using hm))
  simpa only [RawPtr.cast_cast, RawPtr.cast_self, List.length_singleton] using h

/-- The backward computation of `MaybeUninit::as_ptr`, on an initialized value. -/
theorem MaybeUninit.end_as_ptr.spec_some {T : Type} [Pointee T] [Pointee.Sized T]
    (q : ConstRawPtr T) (v : T) :
    ⦃ q.readable 1 [v] ∗ q.exposure 1 ⦄
      (q.cast (MaybeUninit T)).endSharedUninitExposure (Pointee.repr (T := T)) [⟨some v⟩]
      ⦃ emp ⦄ := by
  have h := MaybeUninit.end_as_ptr.spec q ⟨some v⟩ (fun h => by cases h)
  simpa only [uninitShared_singleton_some] using h

/-! ## `as_mut_ptr` and `as_ptr` on slices of `MaybeUninit` -/

/-- The backward computation of `as_mut_ptr` on a slice of `MaybeUninit U`. -/
def MaybeUninit.end_slice_as_mut_ptr {U : Type} [Pointee U] (s : Slice (MaybeUninit U))
    (p : MutRawPtr (MaybeUninit U)) : Result (Slice (MaybeUninit U)) := do
  let values ← p.endUninitExposure (Pointee.repr (T := U)) s.length
  if h : values.length ≤ Usize.max then .ok (Slice.from values h) else .fail .undef

/-- `as_mut_ptr` on a slice of `MaybeUninit U` exposes its elements at the address of its
placement. The pointer is a pointer to `MaybeUninit U`, which callers cast to `U`: the cast pointer
owns `↦?* s.val.val`. -/
theorem Slice.as_mut_ptr.spec_uninit_at {U : Type} [Pointee U] [Pointee.Sized U]
    (address : BasePtr) (s : MutBorrow (Slice (MaybeUninit U))) (hne : 0 < s.val.length) :
    ⦃ emp ⦄ Slice.as_mut_ptr address s
      ⦃ (p, back) => ⌜(p.cast U).address = address⌝ ∗
        ⌜back = MaybeUninit.end_slice_as_mut_ptr s.val p⌝ ∗
        (p.cast U) ↦?* s.val.val ∗ (p.cast U).exposure s.val.length ⦄ := by
  change ispec emp (Aeneas.Std.bind (MaybeUninit.allocExposure (Pointee.repr (T := U)) s.val.val
    address) fun p => .ok (p, MaybeUninit.end_slice_as_mut_ptr s.val p)) _
  apply ispec_bind (MaybeUninit.allocExposure.spec s.val.val address hne)
    (entails_of_eq (sep_emp_r_eq emp).symm)
  intro p
  rw [sep_assoc_eq, ispec_ipure]
  intro haddr
  apply ispec_ok
  simp only [uncurry_apply_pair, haddr]
  iframe

@[step]
theorem Slice.as_mut_ptr.spec_uninit {U : Type} [Pointee U] [Pointee.Sized U]
    (address : BasePtr) (s : MutBorrow (Slice (MaybeUninit U))) (hne : 0 < s.val.length) :
    ⦃ emp ⦄ Slice.as_mut_ptr address s
      ⦃ (p, back) => ⌜back = MaybeUninit.end_slice_as_mut_ptr s.val p⌝ ∗
        (p.cast U) ↦?* s.val.val ∗ (p.cast U).exposure s.val.length ⦄ :=
  ispec_conseq (Slice.as_mut_ptr.spec_uninit_at address s hne) (entails_refl _) (fun r => by
    obtain ⟨q, back⟩ := r
    simp only [uncurry_apply_pair]
    exact fun h hh => ((sep_pure_l _ _ h).mp hh).2)

/-- The backward computation of `as_mut_ptr` on a slice of `MaybeUninit U`: the new slice refines
the final cells (the elements known to be `⟨some v⟩` are `⟨some v⟩`; the other ones are
`⟨some _⟩` if their bytes decode, and `⟨none⟩` otherwise). -/
@[step]
theorem MaybeUninit.end_slice_as_mut_ptr.spec {U : Type} [Pointee U] [Pointee.Sized U]
    (s : Slice (MaybeUninit U)) (p : MutRawPtr (MaybeUninit U)) (vs : List (MaybeUninit U))
    (hLen : vs.length = s.length) (hne : 0 < vs.length) :
    ⦃ (p.cast U) ↦?* vs ∗ (p.cast U).exposure s.length ⦄ MaybeUninit.end_slice_as_mut_ptr s p
      ⦃ r => ⌜MaybeUninit.Refines r.val vs⌝ ⦄ := by
  have hMax : vs.length ≤ Usize.max := by rw [hLen]; exact s.property
  unfold MaybeUninit.end_slice_as_mut_ptr
  rw [← hLen]
  apply ispec_bind (RawPtr.endUninitExposure.spec p vs hne)
    (entails_of_eq (sep_emp_r_eq _).symm)
  intro values
  rw [sep_emp_r_eq, ← sep_emp_r_eq ⌜_⌝, ispec_ipure]
  intro href
  have hv : values.length ≤ Usize.max := by rw [href.1]; exact hMax
  simp only [hv, dite_true]
  apply ispec_ok
  simp only [Slice.from_val]
  exact entails_trans (pure_sep_intro emp href) (entails_of_eq (sep_emp_r_eq _))

/-- `as_ptr` on a slice of `MaybeUninit U` exposes its elements, read-only, at the address of its
placement: the cast pointer has `uninitShared 1 s.val.val` (which is `readable 1 xs` for a slice of
initialized values `xs`, see `uninitShared_some`). -/
theorem Slice.as_ptr.spec_uninit_at {U : Type} [Pointee U] [Pointee.Sized U]
    (address : BasePtr) (s : SharedBorrow (Slice (MaybeUninit U))) (hne : 0 < s.val.length) :
    ⦃ emp ⦄ Slice.as_ptr address s
      ⦃ (p, back) => ⌜(p.cast U).address = address⌝ ∗
        ⌜back = p.endSharedUninitExposure (Pointee.repr (T := U)) s.val.val⌝ ∗
        (p.cast U).uninitShared 1 s.val.val ∗ (p.cast U).exposure s.val.length ⦄ := by
  change ispec emp (Aeneas.Std.bind (MaybeUninit.allocSharedExposure (Pointee.repr (T := U))
    s.val.val address) fun p =>
      .ok (p, p.endSharedUninitExposure (Pointee.repr (T := U)) s.val.val)) _
  apply ispec_bind (MaybeUninit.allocSharedExposure.spec s.val.val address hne)
    (entails_of_eq (sep_emp_r_eq emp).symm)
  intro p
  rw [sep_assoc_eq, ispec_ipure]
  intro haddr
  apply ispec_ok
  simp only [uncurry_apply_pair, haddr]
  iframe

@[step]
theorem Slice.as_ptr.spec_uninit {U : Type} [Pointee U] [Pointee.Sized U]
    (address : BasePtr) (s : SharedBorrow (Slice (MaybeUninit U))) (hne : 0 < s.val.length) :
    ⦃ emp ⦄ Slice.as_ptr address s
      ⦃ (p, back) => ⌜back = p.endSharedUninitExposure (Pointee.repr (T := U)) s.val.val⌝ ∗
        (p.cast U).uninitShared 1 s.val.val ∗ (p.cast U).exposure s.val.length ⦄ :=
  ispec_conseq (Slice.as_ptr.spec_uninit_at address s hne) (entails_refl _) (fun r => by
    obtain ⟨q, back⟩ := r
    simp only [uncurry_apply_pair]
    exact fun h hh => ((sep_pure_l _ _ h).mp hh).2)

/-! ## `from_raw_parts` on readable ranges, and on initialized prefixes -/

universe u in
/-- `ispec_realEntails_pre`, in any universe. -/
theorem ispec_realEntails_pre_u {α : Type u} {P P' : IPre} {m : Result α} {Q : IPost α}
    (hP : RealEntails P P') (hs : ispec P' m Q) : ispec P m Q := by
  rw [ispec_iff] at hs ⊢
  intro F s hR
  exact hs F s (hP F s hR)

/-- Shares the cells of a readable range. -/
theorem RawPtr.shareRange.spec_readable {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (d : Nat) (xs : List T) (hne : 0 < xs.length) :
    ⦃ p.readable d xs ⦄ RawPtr.shareRange (Pointee.repr (T := T)) p xs.length
      ⦃ r => ⌜r = xs⌝ ∗ p.readable (d + 1) xs ⦄ := by
  refine ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.shareRange.local_readable _ p bptr (listVec xs) d hne Pointee.Sized.pos)
      (fun bptr => ?_)) (entails_refl _) (fun _ => ?_)
  · refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.readableRange h.2) ?_
    rintro a F s _ _ _ _ x s' hx a' _ hm' _ ⟨_, data, _, hblock⟩ base hEx _
    have hlen :
        0 < (data.flatMap (fun bytes => bytes.map (Cell.shared (d + 1)))).toList.length := by
      simp; exact ⟨hne, Pointee.Sized.pos⟩
    have run := hx.2
    unfold Heap.shareRange Heap.modifyRange at run
    exact modify_step_nonExclusive run ((Fragment.matches_union _ _ _).mp hm').1
      (Bytes.block_cell hblock hlen) (by rw [flatMap_shared_getElem_depth]; simp) base hEx
  · simp only [listVec_toList]
    exact iexists_upClose_pure_and

/-- Ends a share of the cells of a readable range, which stay shared (`0 < d`: ending the share
of exclusive cells is not specified, as an alias of the shared cells may have been exposed). -/
@[step]
theorem RawPtr.endShareRange.spec_readable {T : Type} [Pointee T] [Pointee.Sized T]
    (p : RawPtr T) (d : Nat) (xs : List T) (positive : 0 < d) (hne : 0 < xs.length) :
    ⦃ p.readable (d + 1) xs ⦄ RawPtr.endShareRange (Pointee.repr (T := T)) p xs
      ⦃ p.readable d xs ⦄ := by
  refine ispec_checked_local (modify := State.endShareRange (Pointee.repr (T := T)) p xs)
    (B := fun bptr (_ : Unit) => readableRange (Pointee.repr (T := T)) p bptr (listVec xs) d)
    (fun bptr => by
      simpa only [listVec_toList] using Bytes.endShareRange.local_readable _ p bptr (listVec xs) d
        positive hne Pointee.Sized.pos)
    (fun bptr => ?_)
  refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.readableRange h) ?_
  rintro a F s _ _ _ _ x s' hx a' _ hm' _ ⟨data, _, hblock⟩ base hEx _
  have hlen : 0 < (data.flatMap (fun bytes => bytes.map (Cell.shared d))).toList.length := by
    simp; exact ⟨hne, Pointee.Sized.pos⟩
  have run := hx.2
  unfold Heap.endShareRange Heap.modifyRange at run
  exact modify_step_nonExclusive run ((Fragment.matches_union _ _ _).mp hm').1
    (Bytes.block_cell hblock hlen) (by rw [flatMap_shared_getElem_depth]; simp; omega) base hEx

/-- `slice::from_raw_parts` on a readable range: the cells are shared once more by the slice. -/
theorem core.slice.raw.from_raw_parts.spec_readable {T : Type} [Pointee T] [Pointee.Sized T]
    (p : ConstRawPtr T) (len : Usize) (d : Nat) (xs : List T)
    (hLen : len.val = xs.length) (hne : 0 < xs.length) :
    ⦃ p.readable d xs ⦄ core.slice.raw.from_raw_parts p len
      ⦃ (s, back) => ⌜s.val.val = xs⌝ ∗
        ⌜back = RawPtr.endShareRange (Pointee.repr (T := T)) p xs⌝ ∗
        p.readable (d + 1) xs ⦄ := by
  unfold core.slice.raw.from_raw_parts
  rw [hLen]
  apply ispec_bind (RawPtr.shareRange.spec_readable p d xs hne)
    (entails_of_eq (sep_emp_r_eq _).symm)
  intro vs
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  have hMax : vs.length ≤ Usize.max := by rw [← hLen]; scalar_tac
  simp only [hMax, dite_true]
  apply ispec_ok
  simp only [uncurry_apply_pair, Slice.from_val]
  iframe

/-- `slice::from_raw_parts` on the initialized prefix `xs` of a possibly uninitialized range
(for instance, a buffer of `MaybeUninit U` exposed by `as_mut_ptr`, and cast to `U`). The prefix
becomes readable, shared once; its backward computation is the end of the share
(`RawPtr.endShareRange.spec_readable` doesn't apply to it: the cells were exclusive). -/
theorem core.slice.raw.from_raw_parts.spec_uninit_prefix {T : Type} [Pointee T]
    [Pointee.Sized T] (p : ConstRawPtr T) (len : Usize) (xs : List T)
    (rest : List (MaybeUninit T)) (hLen : len.val = xs.length) (hne : 0 < xs.length) :
    ⦃ p ↦?* (xs.map (fun v => ⟨some v⟩) ++ rest) ⦄ core.slice.raw.from_raw_parts p len
      ⦃ (s, back) => ⌜s.val.val = xs⌝ ∗
        ⌜back = RawPtr.endShareRange (Pointee.repr (T := T)) p xs⌝ ∗
        (p.readable 1 xs ∗ (p.elem xs.length) ↦?* rest) ⦄ := by
  refine ispec_realEntails_pre_u (uninitRange_split_real p _ rest) ?_
  rw [List.length_map, ← readable_eq_uninitRange]
  refine ispec_conseq (ispec_frame (from_raw_parts.spec_readable p len 0 xs hLen hne)
    ((p.elem xs.length) ↦?* rest)) (entails_refl _) (fun r => ?_)
  obtain ⟨s, back⟩ := r
  simp only [postSep, uncurry_apply_pair, Nat.zero_add]
  iframe

/-- `slice::from_raw_parts` on the initialized prefix `xs` of a shared exposure of possibly
uninitialized values (`MaybeUninit` slices exposed by `as_ptr`, cast to `U`). Its backward
computation is specified by `RawPtr.endShareRange.spec_readable` (`0 < d`). -/
theorem core.slice.raw.from_raw_parts.spec_uninitShared_prefix {T : Type} [Pointee T]
    [Pointee.Sized T] (p : ConstRawPtr T) (len : Usize) (d : Nat) (xs : List T)
    (rest : List (MaybeUninit T)) (hLen : len.val = xs.length) (hne : 0 < xs.length) :
    ⦃ p.uninitShared d (xs.map (fun v => ⟨some v⟩) ++ rest) ⦄ core.slice.raw.from_raw_parts p len
      ⦃ (s, back) => ⌜s.val.val = xs⌝ ∗
        ⌜back = RawPtr.endShareRange (Pointee.repr (T := T)) p xs⌝ ∗
        (p.readable (d + 1) xs ∗ (p.elem xs.length).uninitShared d rest) ⦄ := by
  refine ispec_realEntails_pre_u (uninitShared_split_real p d _ rest) ?_
  rw [List.length_map, uninitShared_some]
  refine ispec_conseq (ispec_frame (from_raw_parts.spec_readable p len d xs hLen hne)
    ((p.elem xs.length).uninitShared d rest)) (entails_refl _) (fun r => ?_)
  obtain ⟨s, back⟩ := r
  simp only [postSep, uncurry_apply_pair]
  iframe

/-! ## `ptr::from_ref` (and `&raw const place`) -/

/-- `ptr::from_ref` exposes the borrowed value, read-only, at the address of its placement. -/
theorem core.ptr.from_ref_model.spec_at {T : Type} [Pointee T] [Pointee.Sized T]
    (address : BasePtr) (r : SharedBorrow T) :
    ⦃ emp ⦄ core.ptr.from_ref_model address r
      ⦃ (p, back) => ⌜p.address = address⌝ ∗
        ⌜back = p.endSharedExposure (Pointee.repr (T := T)) [r.val]⌝ ∗
        p.readable 1 [r.val] ∗ p.exposure 1 ⦄ := by
  unfold core.ptr.from_ref_model core.ptr.from_ref
  apply ispec_bind (ispec_allocatingModify_rel
    (R := State.sharedExposeAt (Pointee.repr (T := T)) [r.val] address)
    (RawPtr.allocSharedExposure.spec [r.val] address (by simp)))
    (entails_of_eq (sep_emp_r_eq emp).symm)
  intro p
  rw [sep_assoc_eq, ispec_ipure]
  rintro ⟨_, _, hx⟩
  have := State.sharedExposeAt_address hx
  apply ispec_ok
  simp only [uncurry_apply_pair, List.length_singleton]
  iframe

@[step]
theorem core.ptr.from_ref_model.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (address : BasePtr) (r : SharedBorrow T) :
    ⦃ emp ⦄ core.ptr.from_ref_model address r
      ⦃ (p, back) => ⌜back = p.endSharedExposure (Pointee.repr (T := T)) [r.val]⌝ ∗
        p.readable 1 [r.val] ∗ p.exposure 1 ⦄ :=
  ispec_conseq (from_ref_model.spec_at address r) (entails_refl _) (fun r => by
    obtain ⟨q, back⟩ := r
    simp only [uncurry_apply_pair]
    exact fun h hh => ((sep_pure_l _ _ h).mp hh).2)

/-- The backward computation of `ptr::from_ref`: the cell must still decode to the value. -/
theorem core.ptr.from_ref_model.end_spec {T : Type} [Pointee T] [Pointee.Sized T]
    (p : ConstRawPtr T) (v : T) :
    ⦃ p.readable 1 [v] ∗ p.exposure 1 ⦄ p.endSharedExposure (Pointee.repr (T := T)) [v]
      ⦃ emp ⦄ := by
  have h := RawPtr.endSharedExposure.spec p [v] (by simp)
  simp only [List.length_singleton] at h
  exact ispec_conseq h (entails_of_eq (sep_comm_eq _ _)) (fun _ => entails_refl _)

/-! ## `&*p`: `as_ref_unchecked` -/

/-- `&*q` shares the cell once more, until the backward computation ends the share (which is
specified by `RawPtr.endShareRange.spec` when `0 < d`). -/
@[step]
theorem RawPtr.as_ref_unchecked.spec {T : Type} [Pointee T] [Pointee.Sized T] (q : RawPtr T)
    (d : Nat) (v : T) :
    ⦃ q.range d [v] ⦄ RawPtr.as_ref_unchecked q
      ⦃ (r, back) => ⌜r.val = v⌝ ∗ ⌜back = q.endShareRange (Pointee.repr (T := T)) [v]⌝ ∗
        q.range (d + 1) [v] ⦄ := by
  unfold RawPtr.as_ref_unchecked
  have h := RawPtr.shareRange.spec q d [v] (by simp)
  simp only [List.length_singleton] at h
  apply ispec_bind h (entails_of_eq (sep_emp_r_eq _).symm)
  intro values
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  apply ispec_ok
  simp only [uncurry_apply_pair]
  iframe

/-- `&*q` from `q ↦ v`. -/
theorem RawPtr.as_ref_unchecked.spec_pointsTo {T : Type} [Pointee T] [Pointee.Sized T]
    (q : RawPtr T) (v : T) :
    ⦃ q ↦ v ⦄ RawPtr.as_ref_unchecked q
      ⦃ (r, back) => ⌜r.val = v⌝ ∗ ⌜back = q.endShareRange (Pointee.repr (T := T)) [v]⌝ ∗
        q.range 1 [v] ⦄ := by
  rw [← RawPtr.range_singleton]
  exact RawPtr.as_ref_unchecked.spec q 0 v

/-- `&*q` on a readable cell (specified by `RawPtr.endShareRange.spec_readable` when `0 < d`). -/
theorem RawPtr.as_ref_unchecked.spec_readable {T : Type} [Pointee T] [Pointee.Sized T]
    (q : RawPtr T) (d : Nat) (v : T) :
    ⦃ q.readable d [v] ⦄ RawPtr.as_ref_unchecked q
      ⦃ (r, back) => ⌜r.val = v⌝ ∗ ⌜back = q.endShareRange (Pointee.repr (T := T)) [v]⌝ ∗
        q.readable (d + 1) [v] ⦄ := by
  unfold RawPtr.as_ref_unchecked
  have h := RawPtr.shareRange.spec_readable q d [v] (by simp)
  simp only [List.length_singleton] at h
  apply ispec_bind h (entails_of_eq (sep_emp_r_eq _).symm)
  intro values
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  apply ispec_ok
  simp only [uncurry_apply_pair]
  iframe

/-- Focuses on the `i`-th element of a possibly uninitialized range. -/
theorem uninitRange_focus_real {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (vs : List (MaybeUninit T)) (i : Nat) (hi : i < vs.length) :
    RealEntails (p ↦?* vs)
      (p ↦?* vs.take i ∗ ((p.elem i) ↦?* [vs[i]] ∗ (p.elem (i + 1)) ↦?* vs.drop (i + 1))) := by
  have hvs : vs = vs.take i ++ (vs[i] :: vs.drop (i + 1)) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hlen : (vs.take i).length = i := by simp; omega
  refine RealEntails.trans (RealEntails.of_entails (entails_of_eq (congrArg (p ↦?* ·) hvs)))
    (RealEntails.trans (uninitRange_split_real p _ _) ?_)
  rw [hlen]
  have h := uninitRange_cons_real (p.elem i) vs[i] (vs.drop (i + 1))
  rw [RawPtr.elem_elem] at h
  exact h.frame_left _

/-- `&*p` on the `i`-th element of a possibly uninitialized range, which is initialized: the
element is carved out of the range, readable and shared once. -/
theorem RawPtr.as_ref_unchecked.spec_uninit {T : Type} [Pointee T] [Pointee.Sized T]
    (p : RawPtr T) (vs : List (MaybeUninit T)) (i : Nat) (v : T) (hi : i < vs.length)
    (hv : vs[i] = ⟨some v⟩) :
    ⦃ p ↦?* vs ⦄ RawPtr.as_ref_unchecked (p.elem i)
      ⦃ (r, back) => ⌜r.val = v⌝ ∗
        ⌜back = (p.elem i).endShareRange (Pointee.repr (T := T)) [v]⌝ ∗
        (p ↦?* vs.take i ∗ (p.elem i).readable 1 [v] ∗ (p.elem (i + 1)) ↦?* vs.drop (i + 1)) ⦄ := by
  refine ispec_realEntails_pre_u (uninitRange_focus_real p vs i hi) ?_
  have he : ((p.elem i) ↦?* [vs[i]]) = (p.elem i).readable 0 [v] := by
    rw [hv, readable_eq_uninitRange]; rfl
  rw [he]
  have h := ispec_frame_left (ispec_frame (RawPtr.as_ref_unchecked.spec_readable (p.elem i) 0 v)
    ((p.elem (i + 1)) ↦?* vs.drop (i + 1))) (p ↦?* vs.take i)
  refine ispec_conseq h (by iframe) (fun r => ?_)
  obtain ⟨s, back⟩ := r
  simp only [postSep, uncurry_apply_pair, Nat.zero_add]
  iframe

/-! ## `&mut *p`: `as_mut_unchecked` -/

/-- Borrows a cell with its backward computation. -/
theorem RawPtr.borrowWithBack.spec {T : Type} [Pointee T] [Pointee.Sized T] (q : RawPtr T)
    (v : T) :
    ⦃ q ↦ v ⦄ RawPtr.borrowWithBack (Pointee.repr (T := T)) q
      ⦃ (x, back) => ⌜x = v⌝ ∗ ⌜back = fun v' => q.endBorrow (Pointee.repr (T := T)) v'⌝ ∗
        q ↦† 1 ⦄ := by
  unfold RawPtr.borrowWithBack RawPtr.borrow
  have h := RawPtr.borrowRange.spec q [v] (by simp)
  simp only [RawPtr.range_singleton, List.length_singleton] at h
  refine ispec_bind (Qm := fun value => ⌜value = v⌝ ∗ q ↦† 1) ?_
    (entails_of_eq (sep_emp_r_eq _).symm) ?_
  · apply ispec_bind h (entails_of_eq (sep_emp_r_eq _).symm)
    intro values
    rw [sep_assoc_eq, ispec_ipure]
    rintro rfl
    apply ispec_ok
    iframe
  · intro value
    rw [sep_assoc_eq, ispec_ipure]
    rintro rfl
    apply ispec_ok
    simp only [uncurry_apply_pair]
    iframe

/-- `&mut *q`: the cell is exclusively borrowed (`q ↦† 1`: raw accesses to it fail) until the
backward computation writes the final value back with `endBorrow`. The backward computation is not
specified: ending a borrow makes the cells exclusive again, which the separation logic can't
justify (an alias of the borrowed cells may have been exposed meanwhile, and the authority to return
an owned block isn't tracked through borrows). -/
@[step]
theorem RawPtr.as_mut_unchecked.spec {T : Type} [Pointee T] [Pointee.Sized T] (q : MutRawPtr T)
    (v : T) :
    ⦃ q ↦ v ⦄ RawPtr.as_mut_unchecked q
      ⦃ (r, back) => ⌜r.val = v⌝ ∗ ⌜back = fun v' => q.endBorrow (Pointee.repr (T := T)) v'⌝ ∗
        q ↦† 1 ⦄ := by
  unfold RawPtr.as_mut_unchecked
  apply ispec_bind (RawPtr.borrowWithBack.spec q v) (entails_of_eq (sep_emp_r_eq _).symm)
  rintro ⟨x, back⟩
  simp only [uncurry_apply_pair]
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  apply ispec_ok
  simp only [uncurry_apply_pair]
  iframe

end Aeneas.Std
