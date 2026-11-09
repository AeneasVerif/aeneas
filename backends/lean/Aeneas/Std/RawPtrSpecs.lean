/- Specifications of the raw-pointer functions, in the separation logic over the byte heap. -/
module
public import Aeneas.Std.Core.Ptr
public import Aeneas.Std.Slice
public import Aeneas.Std.Alloc.Boxed
public import Aeneas.Std.WP
public import Aeneas.SepLogic.Specs
public import Aeneas.SepLogic.Ranges
public import Aeneas.SepLogic.RangeAccess
public import Aeneas.SepLogic.RangeWrite
public import Aeneas.SepLogic.SliceExposure
public import Aeneas.SepLogic.SharedExposure
public import Aeneas.SepLogic.Allocation
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import Aeneas.Tactic.Solver.ScalarTac
@[expose] public section

namespace Aeneas.Std

open Aeneas.SepLogic Aeneas.Std.WP

/-! ## Points-to

- `p ↦ value`: `p` owns the cells of an admissible encoding of `value`, in some block.
- `p ↦* values`: `p` owns the cells of admissible encodings of `values`, one after the other in
  some block.
- `p ↦† n`: `p` holds the `n` cells from `p` on, borrowed (they are given back by
  `endBorrowRange`). -/

/-- The vector of the elements of a list. -/
abbrev listVec {T : Type} (values : List T) : Vector T values.length := ⟨values.toArray, by simp⟩

@[simp] theorem listVec_toList {T : Type} (values : List T) : (listVec values).toList = values := by
  simp [listVec]

namespace RawPtr

/-- `p` owns the cells of admissible encodings of `values`, shared `depth` times (`0`:
exclusively), one after the other in some block. -/
def range {T : Type} [Pointee T] (p : RawPtr T) (depth : Nat) (values : List T) : IProp :=
  iexists fun bptr : BasePtr =>
    upClose (Bytes.pointsToRange (Pointee.repr (T := T)) p bptr (listVec values) depth)

/-- `p` holds the `n` cells from `p` on, borrowed. -/
def borrowed {T : Type} [Pointee T] (p : RawPtr T) (n : Nat) : IProp :=
  iexists fun bptr : BasePtr =>
    upClose (Bytes.block (Pointee.repr (T := T)) p bptr
      (List.replicate (n * (Pointee.repr (T := T)).size) .borrowed))

/-- The pointer to the `i`-th element from `p` on. -/
def elem {T : Type} [Pointee T] (p : RawPtr T) (i : Nat) : RawPtr T :=
  ⟨p.provenance, ⟨BitVec.ofNat _ (p.address.val + i * (Pointee.repr (T := T)).size)⟩⟩

end RawPtr

instance instPointsToRawPtr {T : Type} [Pointee T] : PointsTo (RawPtr T) T :=
  ⟨fun p value => iexists fun bptr : BasePtr =>
    upClose (Bytes.pointsTo (Pointee.repr (T := T)) p bptr value)⟩

instance instPointsToRangeRawPtr {T : Type} [Pointee T] : PointsToRange (RawPtr T) T :=
  ⟨fun p values => p.range 0 values⟩

end Aeneas.Std

namespace Aeneas

scoped notation:50 q:50 " ↦† " n:50 => Std.RawPtr.borrowed q n

end Aeneas

namespace Aeneas.Std

open Aeneas.SepLogic Aeneas.Std.WP

/-! ## Lifting local heap operations -/

/-- A family of local heap operations, indexed by the base pointer of the block, lifted to the
upward closures. -/
theorem ispec_checked_local {α : Type} {A : BasePtr → Fragment → Prop}
    {modify : Heap → α → Heap → Prop} {B : BasePtr → α → Fragment → Prop}
    (hLocal : ∀ bptr, Bytes.LocalOp (A bptr) modify (B bptr)) :
    ispec (iexists fun bptr => upClose (A bptr)) (Result.checkedModify modify)
      (fun x => iexists fun bptr => upClose (B bptr x)) := by
  apply ispec_exists.mpr
  intro bptr
  exact ispec_conseq (ispec_checkedModify (Bytes.LocalOp.upClose (hLocal bptr)))
    (entails_refl _) (fun _ _ hB => ⟨bptr, hB⟩)

/-- A pure fact of a postcondition on fragments. -/
theorem upClose_pure_and {P : Prop} {A : Fragment → Prop} :
    upClose (fun h => P ∧ A h) ⊢ ⌜P⌝ ∗ upClose A := by
  rintro h ⟨a, ⟨hP, hA⟩, hSub⟩
  exact (sep_pure_l _ _ h).mpr ⟨hP, a, hA, hSub⟩

theorem iexists_upClose_pure_and {P : Prop} {A : BasePtr → Fragment → Prop} :
    (iexists fun bptr => upClose (fun h => P ∧ A bptr h)) ⊢
      ⌜P⌝ ∗ iexists fun bptr => upClose (A bptr) := by
  rintro h ⟨bptr, a, ⟨hP, hA⟩, hSub⟩
  exact (sep_pure_l _ _ h).mpr ⟨hP, bptr, a, hA, hSub⟩

/-! ## Reads and writes -/

@[step]
theorem RawPtr.read.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T) (value : T) :
    ⦃ p ↦ value ⦄ RawPtr.read p ⦃ result => ⌜result = value⌝ ∗ p ↦ value ⦄ :=
  ispec_conseq (ispec_checked_local fun bptr =>
      Bytes.read.spec _ p bptr value 0 Pointee.Sized.pos)
    (entails_refl _) (fun _ => iexists_upClose_pure_and)

@[step]
theorem MutRawPtr.write.spec {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.NoPointers T]
    (p : MutRawPtr T) (oldValue newValue : T) :
    ⦃ p ↦ oldValue ⦄ MutRawPtr.write p newValue ⦃ p ↦ newValue ⦄ :=
  ispec_checked_local fun bptr =>
    Bytes.write_pointsTo.spec _ p bptr oldValue newValue
      (Pointee.NoPointers.no_pointers newValue) Pointee.Sized.pos

/-! ## Ranges -/

theorem Bytes.readRange.local {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Bytes.LocalOp (Bytes.pointsToRange repr p bptr values depth) (State.readRange repr p count)
      (fun result h => result = values.toList ∧ Bytes.pointsToRange repr p bptr values depth h) := by
  intro h F s hp hd hm hi
  have hr := Bytes.read_of_pointsToRange hcount hsize hp ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨values.toList, s, hr, rfl⟩, ?_⟩
  rintro result s' ⟨hv, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hv.symm.trans hr), hp⟩

@[step]
theorem RawPtr.readRange.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (values : List T) (hne : 0 < values.length) :
    ⦃ p ↦* values ⦄ RawPtr.readRange (Pointee.repr (T := T)) p values.length
      ⦃ result => ⌜result = values⌝ ∗ p ↦* values ⦄ := by
  refine ispec_conseq (ispec_checked_local fun bptr =>
      Bytes.readRange.local _ p bptr (listVec values) 0 hne Pointee.Sized.pos)
    (entails_refl _) (fun _ => ?_)
  simp only [listVec_toList]
  exact iexists_upClose_pure_and

theorem Bytes.borrowRange.local {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Bytes.LocalOp (Bytes.pointsToRange repr p bptr values) (State.borrowRange repr p count)
      (fun result h => result = values.toList ∧
        Bytes.block repr p bptr (List.replicate (count * repr.size) .borrowed) h) := by
  intro h F s hp hd hm hinv
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have hr := Bytes.read_of_pointsToRange hcount hsize hp localMatch
  obtain ⟨data, encoded, hlo, ha, rfl⟩ := hp
  obtain ⟨blk, hb, hl, _, hbase, selected⟩ :=
    Bytes.bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
      (data := data.flatMap (fun bytes => bytes.map (Cell.shared 0)))
      (Nat.mul_pos hcount hsize) localMatch
  have mutable : State.mutableValues repr p values.toList s := by
    refine ⟨blk, hl, ?_⟩
    intro i hi
    have hic : i < count := by simpa using hi
    have hb' : p.offsetFrom blk.bptr + count * repr.size ≤ blk.repr.length := by
      simpa [hbase, RawPtr.cast, RawPtr.offsetFrom, Repr.region] using hb
    have hs := repr.select_region blk.bytes (p.offsetFrom blk.bptr) count
      (data.map fun bytes => bytes.map (Cell.shared 0)) hb'
      (by simpa [hbase, RawPtr.cast, RawPtr.offsetFrom, Vector.flatMap_map] using selected) i hic
    refine ⟨data[i], range_element_bound hic hb', ?_, ?_⟩
    · simpa only [Vector.getElem_map, hs] using Repr.readBytes_shared data[i] 0
    · simpa using encoded ⟨i, hic⟩
  obtain ⟨⟨_, s', hb'⟩, post⟩ :=
    Bytes.borrowRange_cells.spec repr p bptr data hcount hsize _ F s ⟨hlo, ha, rfl⟩ hd hm hinv
  refine ⟨⟨values.toList, s', hr, mutable, hb'⟩, ?_⟩
  rintro result s' ⟨hv, _, he⟩
  obtain ⟨h', hd', hm', hi', hq⟩ := post () s' he
  exact ⟨h', hd', hm', hi', Option.some.inj (hv.symm.trans hr), hq⟩

@[step]
theorem RawPtr.borrowRange.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (values : List T) (hne : 0 < values.length) :
    ⦃ p ↦* values ⦄ RawPtr.borrowRange (Pointee.repr (T := T)) p values.length
      ⦃ result => ⌜result = values⌝ ∗ p ↦† values.length ⦄ := by
  refine ispec_conseq (ispec_checked_local fun bptr =>
      Bytes.borrowRange.local _ p bptr (listVec values) hne Pointee.Sized.pos)
    (entails_refl _) (fun _ => ?_)
  simp only [listVec_toList]
  exact iexists_upClose_pure_and

theorem Bytes.shareRange.local {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Bytes.LocalOp (Bytes.pointsToRange repr p bptr values depth) (State.shareRange repr p count)
      (fun result h => result = values.toList ∧
        Bytes.pointsToRange repr p bptr values (depth + 1) h) := by
  apply Bytes.readRange_transfer.spec repr p bptr values depth _ _ hcount hsize
  rintro h F s ⟨data, decoded, hp⟩ hd hm hi
  exact Bytes.LocalOp.conseq (fun _ h => h) (fun _ _ h => ⟨data, decoded, h⟩)
    (Bytes.shareRange_cells.spec repr p bptr data depth hcount hsize) h F s hp hd hm hi

/-- Shares the cells of a range (they become readable, but not writable). -/
@[step]
theorem RawPtr.shareRange.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (depth : Nat) (values : List T) (hne : 0 < values.length) :
    ⦃ p.range depth values ⦄ RawPtr.shareRange (Pointee.repr (T := T)) p values.length
      ⦃ result => ⌜result = values⌝ ∗ p.range (depth + 1) values ⦄ := by
  refine ispec_conseq (ispec_checked_local fun bptr =>
      Bytes.shareRange.local _ p bptr (listVec values) depth hne Pointee.Sized.pos)
    (entails_refl _) (fun _ => ?_)
  simp only [listVec_toList]
  exact iexists_upClose_pure_and

theorem Bytes.endShareRange.local {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) (positive : 0 < depth) (hcount : 0 < count)
    (hsize : 0 < repr.size) :
    Bytes.LocalOp (Bytes.pointsToRange repr p bptr values (depth + 1))
      (State.endShareRange repr p values.toList)
      (fun _ => Bytes.pointsToRange repr p bptr values depth) := by
  intro h F s hp hd hm hi
  have hr := Bytes.read_of_pointsToRange hcount hsize hp ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨data, decoded, hp⟩ := hp
  obtain ⟨⟨_, s₁, hc⟩, hpost⟩ :=
    Bytes.endShareRange_cells.spec repr p bptr data depth positive hcount hsize h F s hp hd hm hi
  refine ⟨⟨(), s₁, ?_, ?_⟩, ?_⟩
  · simpa using hr
  · simpa using hc
  · rintro _ s' ⟨_, he⟩
    obtain ⟨h', hd', hm', hi', hq⟩ := hpost () s' (by simpa using he)
    exact ⟨h', hd', hm', hi', data, decoded, hq⟩

/-- Ends a share of the cells of a range. -/
@[step]
theorem RawPtr.endShareRange.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (depth : Nat) (values : List T) (positive : 0 < depth) (hne : 0 < values.length) :
    ⦃ p.range (depth + 1) values ⦄ RawPtr.endShareRange (Pointee.repr (T := T)) p values
      ⦃ p.range depth values ⦄ := by
  have h := ispec_checked_local fun bptr =>
    Bytes.endShareRange.local (Pointee.repr (T := T)) p bptr (listVec values) depth positive hne
      Pointee.Sized.pos
  simp only [listVec_toList] at h
  exact h

/-! ## Pointer arithmetic -/

theorem Bytes.add.local {T : Type} (repr : Repr T) (p : RawPtr T) (base : BasePtr)
    (values : Vector T count) (depth : Nat) (i : Usize) (hcount : 0 < count)
    (hsize : 0 < repr.size) (hle : i.val ≤ count) :
    Bytes.LocalOp (Bytes.pointsToRange repr p base values depth) (State.offset repr p i.val)
      (fun result h => result.provenance = p.provenance ∧
        result.address.val = p.address.val + i.val * repr.size ∧
        Bytes.pointsToRange repr p base values depth h) := by
  intro h F s hp hd hm hi
  have keep := hp
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have bound := readableRange_bound repr p base values depth hcount hsize h s
    (pointsToRange_readable hp) localMatch hi
  have hfit : p.address.val + i.val * repr.size < 2 ^ UScalarTy.numBits .Usize := by
    have := Nat.mul_le_mul_right repr.size hle
    omega
  obtain ⟨data, _, hlo, _, cells⟩ := pointsToRange_readable hp
  rw [cells] at localMatch
  obtain ⟨blk, hb, hl, hlive, hbase, _⟩ :=
    Bytes.bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
      (data := data.flatMap (fun bytes => bytes.map (Cell.shared depth)))
      (Nat.mul_pos hcount hsize) localMatch
  change p.offsetFrom base + count * repr.size ≤ blk.repr.length at hb
  change s.allocations p.provenance = some blk at hl
  have htarget : p.address.val + i.val * repr.size ≤ base.val + blk.repr.length := by
    have hmul := Nat.mul_le_mul_right repr.size hle
    simp only [RawPtr.offsetFrom] at hb
    omega
  have hstart : p.address.val ≤ base.val + blk.repr.length := by omega
  have hlo' : (base.val : Int) ≤ (p.address.val : Int) + i.val * repr.size := by omega
  have hhi' : (p.address.val : Int) + i.val * repr.size ≤ base.val + blk.repr.length := by
    exact_mod_cast htarget
  have hfit' : (p.address.val : Int) + i.val * repr.size <
      (2 ^ UScalarTy.numBits .Usize : Nat) := by exact_mod_cast hfit
  let result : RawPtr T := ⟨p.provenance,
    ⟨BitVec.ofNat _ (p.address.val + i.val * repr.size)⟩⟩
  have hval : result.address.val = p.address.val + i.val * repr.size := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  have hrun : Heap.offset repr p i.val s = some result := by
    have hf : (p.address.val : Int) + i.val * repr.size <
        (2 : Int) ^ System.Platform.numBits := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, UScalarTy.Usize_numBits_eq] using hfit'
    have target_nat : ((p.address.val : Int) + i.val * repr.size).toNat =
        p.address.val + i.val * repr.size := by
      exact_mod_cast Int.toNat_natCast (p.address.val + i.val * repr.size)
    simp [Heap.offset, hl, hlive, hbase, hlo, hstart, hlo', hhi', hf, target_nat, result]
  refine ⟨⟨result, s, hrun, rfl⟩, ?_⟩
  rintro answer s' ⟨he, rfl⟩
  have he := Option.some.inj (he.symm.trans hrun)
  subst answer
  exact ⟨h, hd, hm, hi, rfl, hval, keep⟩

/-- Pointer arithmetic within a range, including the pointer one past its end. -/
@[step]
theorem RawPtr.add.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (values : List T) (count : Usize) (hne : 0 < values.length)
    (hCount : count.val ≤ values.length) :
    ⦃ p ↦* values ⦄ RawPtr.add p count
      ⦃ result => ⌜result = p.elem count.val⌝ ∗ p ↦* values ⦄ := by
  refine ispec_conseq (ispec_checked_local fun bptr =>
      Bytes.add.local _ p bptr (listVec values) 0 count hne Pointee.Sized.pos hCount)
    (entails_refl _) (fun result => ?_)
  rintro h ⟨bptr, a, ⟨hprov, haddr, hA⟩, hSub⟩
  refine (sep_pure_l _ _ h).mpr ⟨?_, bptr, a, hA, hSub⟩
  cases result with
  | mk prov addr =>
    simp only at hprov haddr
    subst hprov
    simp only [RawPtr.elem, RawPtr.mk.injEq, true_and]
    cases addr with
    | mk bv =>
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      have h1 : bv.toNat = p.address.val + count.val * (Pointee.repr (T := T)).size := haddr
      rw [← h1]
      exact (Nat.mod_eq_of_lt bv.isLt).symm

/-! ## Exposures and allocations

- `p.exposure n`: `p` is the start of an exposure of `n` values (a block which is not owned, such
  as the raw view of a safe place), which the matching backward computation retires.
- `p.freeable n`: `p` is the start of an owned block of `n` values.
- `p.readable depth values`: the cells from `p` on decode to `values` (they may not be an admissible
  encoding of them), shared `depth` times. -/

namespace RawPtr

def exposure {T : Type} [Pointee T] (p : RawPtr T) (n : Nat) : IProp :=
  upClose (Bytes.alloc (Pointee.repr (T := T)) p p.address n false)

def freeable {T : Type} [Pointee T] (p : RawPtr T) (n : Nat) : IProp :=
  upClose (Bytes.alloc (Pointee.repr (T := T)) p p.address n true)

def readable {T : Type} [Pointee T] (p : RawPtr T) (depth : Nat) (values : List T) : IProp :=
  iexists fun bptr : BasePtr =>
    upClose (readableRange (Pointee.repr (T := T)) p bptr (listVec values) depth)

end RawPtr

/-- The separating conjunction of predicates on fragments, upward closed. -/
theorem upClose_sep {A B : Fragment → Prop} : upClose (Bytes.sep A B) ⊢ upClose A ∗ upClose B := by
  rintro _ ⟨_, ⟨x, y, hxy, rfl, hA, hB⟩, hSub⟩
  obtain ⟨r, hr, rfl⟩ := PartialCommMonoid.subheap_iff.mp hSub
  have hd := Fragment.disjoint_union_left.mp hr
  refine ⟨x, y ∪ r, Fragment.disjoint_union_right.mpr ⟨hxy, hd.1⟩, Fragment.union_assoc _ _ _,
    ⟨x, hA, PartialCommMonoid.Subheap.refl _⟩, ⟨y, hB, PartialCommMonoid.Subheap.union_left hd.2⟩⟩

/-- An allocation from the empty precondition: every successor extends the heap with a fragment of
`A`, keeping every frame. -/
theorem ispec_allocating_emp {α : Type} {modify : Heap → α → Heap → Prop}
    {A : α → Fragment → Prop}
    (hPost : ∀ s F, s.Inv → Fragment.Matches s F → ∀ x s', modify s x s' →
      ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧ A x h) :
    ispec emp (Result.allocatingModify modify) (fun x => upClose (A x)) := by
  apply ispec_allocatingModify
  intro s h frame _ hd hm hi x s' hx
  obtain ⟨h', hd', hm', hi', hA⟩ := hPost s (h ∪ frame) hi hm x s' hx
  have hd'' := Fragment.disjoint_union_right.mp hd'
  refine ⟨h' ∪ h, Fragment.disjoint_union_left.mpr ⟨hd''.2, hd⟩, ?_, hi',
    h', hA, PartialCommMonoid.Subheap.union_left hd''.1⟩
  rwa [Fragment.union_assoc]

/-- The cells of a block and its cleanup, which hold in the same heap, have the same base pointer.
-/
theorem Bytes.bptr_eq_of_matches {T : Type} {repr : Repr T} {p : RawPtr T} {a bptr : BasePtr}
    {n : Nat} {own : Bool} {cells : List Cell} {h₁ h₂ : Fragment} {s : Heap}
    (hne : 0 < cells.length) (h₁A : Bytes.alloc repr p a n own h₁)
    (h₂B : Bytes.block repr p bptr cells h₂) (hm₁ : Fragment.Matches s h₁)
    (hm₂ : Fragment.Matches s h₂) : bptr = a := by
  obtain ⟨_, rfl⟩ := h₁A
  obtain ⟨_, _, rfl⟩ := h₂B
  obtain ⟨blk, hl, _, _, hbptr, _⟩ := hm₁ _ rfl
  obtain ⟨blk', hl', _, hbptr', _⟩ := hm₂ (.cell p.provenance (p.offsetFrom bptr + 0) bptr cells[0])
    ⟨0, hne, rfl⟩
  rw [hl] at hl'
  cases hl'
  rw [← hbptr, hbptr']

theorem Bytes.allocExposure.post {T : Type} (repr : Repr T) (values : Vector T count)
    (calibrated : ∀ value bytes, repr.decode bytes = some value →
      (∀ i : Fin repr.size, ∀ q lane,
        bytes[i.val] = .pointer q lane → repr.Carries value q) → repr.encode value bytes)
    (s₀ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    ∀ p s₁, State.newBlock repr values.toList false s₀ p s₁ →
      ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧
        (Bytes.alloc repr p p.address count false ∗ᵇ
          Bytes.pointsToRange repr p p.address values) h := by
  rintro p s₁ ⟨data, bptr, root, exposed, created⟩
  obtain ⟨len, each⟩ := exposesList_index repr s₀ bptr.val values.toList data exposed
  let bytes : Vector (Vector Byte repr.size) count := ⟨data.toArray, by simp [len]⟩
  have bytesList : bytes.toList = data := by simp [bytes]
  have exposed' : ∀ i : Fin count,
      State.exposes repr s₀ (bptr.val + i.val * repr.size) values[i.val] bytes[i.val] := by
    intro i
    simpa [bytes] using each i.val (by simp)
  unfold Heap.newBlock at created
  simp only [Bool.not_false, Bool.true_or, Bool.and_true] at created
  split at created
  · rename_i aligned
    obtain ⟨⟨id, result⟩, run, he⟩ := Option.map_eq_some_iff.mp created
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have run' : s₀.createRepr
        ⟨bptr, root.getD s₀.next, repr.create bytes.toList 0, false, true, true⟩ =
          some (id, result) := by simpa only [bytesList] using run
    have carries := create_range_carries repr values bytes bptr root s₀ result id hi exposed'
      run'
    obtain ⟨h, hd, hm, hi, a, b, hab, hh, ha, hb⟩ :=
      create_range_resources repr bytes 0 bptr root s₀ result id
        (of_decide_eq_true aligned) hi F hm run'
    exact ⟨h, hd, hm, hi, a, b, hab, hh, ha, bytes,
      fun i => calibrated _ _ (exposed' i).1 (carries i), hb⟩
  · contradiction

theorem Bytes.allocSharedExposure.post {T : Type} (repr : Repr T) (values : Vector T count)
    (s₀ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    ∀ p s₁, State.newSharedExposure repr values.toList s₀ p s₁ →
      ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧
        (Bytes.alloc repr p p.address count false ∗ᵇ
          readableRange repr p p.address values 1) h := by
  rintro p s₁ ⟨data, bptr, root, exposed, created⟩
  obtain ⟨len, each⟩ := exposesList_index repr s₀ bptr.val values.toList data exposed
  let bytes : Vector (Vector Byte repr.size) count := ⟨data.toArray, by simp [len]⟩
  have bytesList : bytes.toList = data := by simp [bytes]
  unfold Heap.newSharedExposure at created
  split at created
  · rename_i aligned
    obtain ⟨⟨id, result⟩, run, he⟩ := Option.map_eq_some_iff.mp created
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨h, hd, hm, hi, a, b, hab, hh, ha, hb⟩ :=
      create_range_resources repr bytes 1 bptr root s₀ result id aligned hi F hm
        (by simpa only [bytesList] using run)
    refine ⟨h, hd, hm, hi, a, b, hab, hh, ha, bytes, ?_, hb⟩
    intro i
    simpa [bytes] using (each i.val (by simp)).1
  · contradiction

/-- Exposes a mutable safe place, whose values are `values`. -/
@[step]
theorem RawPtr.allocExposure.spec {T : Type} [Pointee T] [Pointee.Calibrated T] (values : List T) :
    ⦃ emp ⦄ RawPtr.allocExposure (Pointee.repr (T := T)) values
      ⦃ p => p.exposure values.length ∗ p ↦* values ⦄ := by
  have h := ispec_allocating_emp (A := fun p => Bytes.alloc (Pointee.repr (T := T)) p p.address
      values.length false ∗ᵇ Bytes.pointsToRange (Pointee.repr (T := T)) p p.address
        (listVec values) 0)
    (modify := State.newBlock (Pointee.repr (T := T)) values false)
    (fun s F hi hm => by
      simpa using Bytes.allocExposure.post (Pointee.repr (T := T)) (listVec values)
        Pointee.Calibrated.calibrated s F hi hm)
  refine ispec_conseq h (entails_refl _) (fun p => entails_trans upClose_sep ?_)
  exact sep_mono (entails_refl _) (fun h hU => ⟨p.address, hU⟩)

/-- Exposes a shared safe place, whose values are `values`. -/
@[step]
theorem RawPtr.allocSharedExposure.spec {T : Type} [Pointee T] (values : List T) :
    ⦃ emp ⦄ RawPtr.allocSharedExposure (Pointee.repr (T := T)) values
      ⦃ p => p.exposure values.length ∗ p.readable 1 values ⦄ := by
  have h := ispec_allocating_emp (A := fun p => Bytes.alloc (Pointee.repr (T := T)) p p.address
      values.length false ∗ᵇ readableRange (Pointee.repr (T := T)) p p.address
        (listVec values) 1)
    (modify := State.newSharedExposure (Pointee.repr (T := T)) values)
    (fun s F hi hm => by
      simpa using Bytes.allocSharedExposure.post (Pointee.repr (T := T)) (listVec values)
        s F hi hm)
  refine ispec_conseq h (entails_refl _) (fun p => entails_trans upClose_sep ?_)
  exact sep_mono (entails_refl _) (fun h hU => ⟨p.address, hU⟩)

/-- Retiring an exposure whose cells decode to `values`, shared `depth` times. -/
theorem Bytes.endExposure.local {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Bytes.LocalOp
      (Bytes.alloc repr p p.address count false ∗ᵇ readableRange repr p bptr values depth)
      (fun s (_ : Unit) s' => Heap.endExposureAt repr p count depth s = some s')
      (fun _ => Bytes.empty) := by
  intro h F s hp hd hm hi
  obtain ⟨a, b, hab, rfl, ha, hb⟩ := id hp
  have hmab := (Fragment.matches_union _ _ _).mp ((Fragment.matches_union _ _ _).mp hm).1
  have hb' := hb
  obtain ⟨data, _, hblock⟩ := hb'
  have hlen : 0 < (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList.length := by
    simp; exact ⟨hcount, hsize⟩
  have hbptr := Bytes.bptr_eq_of_matches hlen ha hblock hmab.1 hmab.2
  subst hbptr
  exact end_range_exposure.spec repr p values depth _ F s hp hd hm hi

/-- Retires the exposure of `as_ptr`: its cells must still decode to the original values. -/
@[step]
theorem RawPtr.endSharedExposure.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (values : List T) (hne : 0 < values.length) :
    ⦃ p.exposure values.length ∗ p.readable 1 values ⦄
      RawPtr.endSharedExposure (Pointee.repr (T := T)) p values ⦃ emp ⦄ := by
  have hsep : ∀ bptr, (p.exposure values.length ∗ upClose (readableRange
      (Pointee.repr (T := T)) p bptr (listVec values) 1)) ⊢ upClose (Bytes.alloc
        (Pointee.repr (T := T)) p p.address values.length false ∗ᵇ readableRange
          (Pointee.repr (T := T)) p bptr (listVec values) 1) := by
    rintro bptr _ ⟨h₁, h₂, hd, rfl, ⟨a, ha, hsa⟩, ⟨b, hb, hsb⟩⟩
    obtain ⟨r₁, hr₁, rfl⟩ := PartialCommMonoid.subheap_iff.mp hsa
    obtain ⟨r₂, hr₂, rfl⟩ := PartialCommMonoid.subheap_iff.mp hsb
    have hd' := Fragment.disjoint_union_left.mp hd
    have hd₁ := Fragment.disjoint_union_right.mp hd'.1
    have hd₂ := Fragment.disjoint_union_right.mp hd'.2
    refine ⟨a ∪ b, ⟨a, b, hd₁.1, rfl, ha, hb⟩, PartialCommMonoid.subheap_iff.mpr
      ⟨r₁ ∪ r₂, ?_, ?_⟩⟩
    · exact Fragment.disjoint_union_left.mpr
        ⟨Fragment.disjoint_union_right.mpr ⟨hr₁, hd₁.2⟩,
         Fragment.disjoint_union_right.mpr ⟨hd₂.1.symm, hr₂⟩⟩
    · funext r; apply propext
      show ((a r ∨ r₁ r) ∨ (b r ∨ r₂ r)) ↔ ((a r ∨ b r) ∨ (r₁ r ∨ r₂ r))
      tauto
  have hEq : p.exposure values.length ∗ p.readable 1 values ⊢
      iexists fun bptr => upClose (Bytes.alloc (Pointee.repr (T := T)) p p.address
        values.length false ∗ᵇ readableRange (Pointee.repr (T := T)) p bptr
          (listVec values) 1) := by
    rintro h ⟨h₁, h₂, hd, rfl, hE, bptr, hR⟩
    exact ⟨bptr, hsep bptr _ ⟨h₁, h₂, hd, rfl, hE, hR⟩⟩
  refine ispec_conseq (ispec_checked_local (modify := State.endSharedExposure
    (Pointee.repr (T := T)) p values) (B := fun _ _ => Bytes.empty) fun bptr => ?_) hEq
    (fun _ _ _ => trivial)
  intro h F s hp hd hm hi
  obtain ⟨_, b, _, rfl, _, hb⟩ := id hp
  have hr := Bytes.read_of_readableRange hne Pointee.Sized.pos hb
    ((Fragment.matches_union _ _ _).mp ((Fragment.matches_union _ _ _).mp hm).1).2
  obtain ⟨⟨_, s₁, he⟩, post⟩ := Bytes.endExposure.local _ p bptr (listVec values) 1 hne
    Pointee.Sized.pos _ F s hp hd hm hi
  refine ⟨⟨(), s₁, by simpa using hr, he⟩, ?_⟩
  rintro _ s' ⟨_, he'⟩
  exact post () s' he'

end Aeneas.Std
