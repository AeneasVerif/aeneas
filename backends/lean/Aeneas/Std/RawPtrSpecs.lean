/- Specifications of the raw-pointer functions, in the separation logic over the byte heap. -/
module
public import Aeneas.Std.Core.Ptr
public import Aeneas.Std.Core.PtrMovement
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
public import Aeneas.SepLogic.Lifecycle
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Alloc.Boxed
import all Aeneas.Std.Slice
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

/-! ## The authority of the owned exclusive blocks

`Realizes` asks the owned blocks whose cleanup is owned, and whose cells are all exclusive, to have
the authority to be returned (`AuthOK`). The specifications show that their operations keep it
(`Bytes.AuthPres`): an operation either doesn't change the heap, changes cells which it owns (a write
keeps them exclusive, a borrow or a share makes them non-exclusive), creates a block (a non-empty
exposure can't be a view of a block whose cells are exclusive) or retires a block. -/

/-- The fragment contains no owned cleanup. -/
def NoOwned (a : Fragment) : Prop := ∀ base size bptr, ¬ a (.cleanup base size bptr true)

theorem NoOwned.cellsHeap {bptr : BasePtr} {base start : Nat} {cells : List Cell} :
    NoOwned (Bytes.cellsHeap bptr base start cells) := by
  rintro _ _ _ ⟨i, hi, h⟩
  cases h

theorem NoOwned.block {T : Type} {repr : Repr T} {p : RawPtr T} {bptr : BasePtr}
    {cells : List Cell} {a : Fragment} (h : Bytes.block repr p bptr cells a) : NoOwned a := by
  obtain ⟨_, _, rfl⟩ := h
  exact NoOwned.cellsHeap

theorem NoOwned.pointsTo {T : Type} {repr : Repr T} {p : RawPtr T} {bptr : BasePtr} {value : T}
    {depth : Nat} {a : Fragment} (h : Bytes.pointsTo repr p bptr value depth a) : NoOwned a :=
  let ⟨_, _, hb⟩ := h; NoOwned.block hb

theorem NoOwned.pointsToRange {T : Type} {repr : Repr T} {p : RawPtr T} {bptr : BasePtr}
    {values : Vector T count} {depth : Nat} {a : Fragment}
    (h : Bytes.pointsToRange repr p bptr values depth a) : NoOwned a :=
  let ⟨_, _, hb⟩ := h; NoOwned.block hb

theorem NoOwned.readableRange {T : Type} {repr : Repr T} {p : RawPtr T} {bptr : BasePtr}
    {values : Vector T count} {depth : Nat} {a : Fragment}
    (h : readableRange repr p bptr values depth a) : NoOwned a :=
  let ⟨_, _, hb⟩ := h; NoOwned.block hb

theorem NoOwned.alloc_false {T : Type} {repr : Repr T} {p : RawPtr T} {bptr : BasePtr} {n : Nat}
    {a : Fragment} (h : Bytes.alloc repr p bptr n false a) : NoOwned a := by
  obtain ⟨_, rfl⟩ := h
  rintro _ _ _ h
  simp [Bytes.allocHeap, Fragment.single] at h

theorem NoOwned.union {a b : Fragment} (ha : NoOwned a) (hb : NoOwned b) : NoOwned (a ∪ b) := by
  rintro base size bptr (h | h)
  · exact ha base size bptr h
  · exact hb base size bptr h

theorem NoOwned.sep {A B : Fragment → Prop} (hA : ∀ a, A a → NoOwned a)
    (hB : ∀ b, B b → NoOwned b) {h : Fragment} (hAB : Bytes.sep A B h) : NoOwned h := by
  obtain ⟨a, b, _, rfl, ha, hb⟩ := hAB
  exact (hA a ha).union (hB b hb)

theorem NoOwned.empty {a : Fragment} (h : Bytes.empty a) : NoOwned a := by
  rw [h]
  rintro _ _ _ h
  exact h

/-- The authority is kept, from the cleanups of the frame. -/
theorem Bytes.AuthPres.of_step {α : Type} {A : Fragment → Prop} {op : Heap → α → Heap → Prop}
    {B : α → Fragment → Prop} (hB : ∀ x a', B x a' → NoOwned a')
    (hStep : ∀ a F s, A a → a.Disjoint F → Fragment.Matches s (a ∪ F) → s.Inv →
      ∀ x s', op s x s' → ∀ a', a'.Disjoint F → Fragment.Matches s' (a' ∪ F) → s'.Inv → B x a' →
      ∀ base, AllExclusive s' base → s.allocations base ≠ none →
        AllExclusive s base ∧ (Bytes.RootReturn s base → Bytes.RootReturn s' base)) :
    Bytes.AuthPres A op B := by
  unfold Bytes.AuthPres
  intro a F s hA hd hm hi hAuth x s' a' hx hd' hm' hi' hB'
  unfold AuthOK
  intro base size bptr hc hEx
  rcases hc with hc | hc
  · exact (hB x a' hB' base size bptr hc).elim
  · have hHolds := ((Fragment.matches_union _ _ _).mp hm).2 _ hc
    obtain ⟨blk, hl, _⟩ := hHolds
    obtain ⟨hEx₀, hRet⟩ := hStep a F s hA hd hm hi x s' hx a' hd' hm' hi' hB' base hEx
      (by simp [hl])
    exact hRet (hAuth base size bptr (Or.inr hc) hEx₀)

/-- The operations which don't change the heap keep the authority. -/
theorem Bytes.AuthPres.of_eq {α : Type} {A : Fragment → Prop} {op : Heap → α → Heap → Prop}
    {B : α → Fragment → Prop} (hB : ∀ x a', B x a' → NoOwned a')
    (hop : ∀ s x s', op s x s' → s' = s) : Bytes.AuthPres A op B :=
  Bytes.AuthPres.of_step hB fun _ _ _ _ _ _ _ x s' hx _ _ _ _ _ _ hEx _ => by
    obtain rfl := hop _ x s' hx
    exact ⟨hEx, id⟩

theorem Heap.modify_run {T : Type} {repr : Repr T} {p : RawPtr T}
    {change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r)} {s s' : Heap}
    (run : Heap.modify repr p change s = some s') :
    ∃ blk bytes, s.allocations p.provenance = some blk ∧
      change blk.bytes (p.offsetFrom blk.bptr) = some bytes ∧
      s' = s.storeRepr p.provenance bytes.toList := by
  unfold Heap.modify at run
  cases hl : s.allocations p.provenance
  · simp [hl] at run
  · rename_i blk
    simp only [hl, Bind.bind, Option.bind] at run
    split at run
    · cases hc : change blk.bytes (p.offsetFrom blk.bptr)
      · simp [hc] at run
      · rename_i bytes
        simp only [hc] at run
        exact ⟨blk, bytes, rfl, hc, (Heap.commit_success _ _ run).1⟩
    · contradiction

theorem Heap.storeRepr_allocations_ne {s : Heap} {id base : Nat} {bytes : List Cell}
    (hne : base ≠ id) : (s.storeRepr id bytes).allocations base = s.allocations base := by
  simp [Heap.storeRepr, update, hne]

/-- A modification of the cells of `p.provenance` keeps the authority, provided that it doesn't make
the block exclusive. -/
theorem modify_step {T : Type} {repr : Repr T} {p : RawPtr T}
    {change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r)} {s s' : Heap}
    (run : Heap.modify repr p change s = some s')
    (hEx : AllExclusive s' p.provenance → AllExclusive s p.provenance) :
    ∀ base, AllExclusive s' base →
      AllExclusive s base ∧ (Bytes.RootReturn s base → Bytes.RootReturn s' base) := by
  intro base hEx'
  refine ⟨?_, fun h => Bytes.RootReturn.modify h run⟩
  by_cases hb : base = p.provenance
  · subst hb; exact hEx hEx'
  · obtain ⟨_, _, _, _, rfl⟩ := Heap.modify_run run
    intro blk hl
    exact hEx' blk (by rw [Heap.storeRepr_allocations_ne hb]; exact hl)

/-- A block with a cell which is not exclusive is not exclusive. -/
theorem not_allExclusive_of_cell {s : Heap} {a : Fragment} {base index : Nat} {bptr : BasePtr}
    {c : Cell} (hm : Fragment.Matches s a) (hc : a (.cell base index bptr c))
    (hdepth : c.depth ≠ some 0) : ¬ AllExclusive s base := by
  intro hEx
  obtain ⟨blk, hl, _, _, hcell⟩ := hm _ hc
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hcell
  have := hEx blk hl index hi
  rw [hget] at this
  exact hdepth this

/-- A write keeps the cells exclusive. -/
theorem write_step {T : Type} {repr : Repr T} {q : RawPtr T} {bptr : BasePtr}
    {old : Vector Byte repr.size} {value : T} {s s' : Heap} (hsize : 0 < repr.size)
    (hm : Fragment.Matches s
      (Bytes.cellsHeap bptr q.provenance (q.offsetFrom bptr) (old.map (Cell.shared 0)).toList))
    (run : State.write repr q value s () s') :
    ∀ base, AllExclusive s' base →
      AllExclusive s base ∧ (Bytes.RootReturn s base → Bytes.RootReturn s' base) := by
  obtain ⟨data, encoded, hrun⟩ := run
  apply modify_step hrun
  intro hEx' blk hl i hi
  obtain ⟨blk₀, hb, hl₀, _, hbase, selected⟩ := Bytes.bytes_of_matches (data := old.map (Cell.shared 0))
    hsize hm
  have hblk := Option.some.inj (hl₀.symm.trans hl)
  subst hblk
  subst hbase
  obtain ⟨blk', bytes, hl', hc, rfl⟩ := Heap.modify_run hrun
  have hblk' := Option.some.inj (hl₀.symm.trans hl')
  subst hblk'
  have hc' : bytes = repr.update blk₀.bytes (q.offsetFrom blk₀.bptr) hb
      ((data.map (Cell.shared 0))) := by
    simp only [Repr.write, hsize, hb, and_self, dite_true, selected,
      Repr.writeBytes_shared, Option.map_some, Option.some.injEq] at hc
    exact hc.symm
  subst hc'
  have hs' : (s.storeRepr q.provenance (repr.update blk₀.bytes (q.offsetFrom blk₀.bptr) hb
      (data.map (Cell.shared 0))).toList).allocations q.provenance =
      some { blk₀ with repr := (repr.update blk₀.bytes (q.offsetFrom blk₀.bptr) hb
        (data.map (Cell.shared 0))).toList } := by
    simp [Heap.storeRepr, update, hl₀]
  have hEx'' := hEx' _ hs'
  have hb2 : blk₀.bytes.toList = blk₀.repr := by simp [Block.bytes]
  by_cases hin : q.offsetFrom blk₀.bptr ≤ i ∧ i < q.offsetFrom blk₀.bptr + repr.size
  · have hsel := Repr.select_getElem? repr blk₀.bytes (q.offsetFrom blk₀.bptr) hb
      (i - q.offsetFrom blk₀.bptr) (by omega)
    rw [selected, show q.offsetFrom blk₀.bptr + (i - q.offsetFrom blk₀.bptr) = i by omega,
      Vector.getElem?_map, hb2] at hsel
    rw [List.getElem?_eq_getElem hi] at hsel
    simp only [Vector.getElem?_eq_getElem (show i - q.offsetFrom blk₀.bptr < repr.size by omega),
      Option.map_some, Option.some.injEq] at hsel
    rw [← hsel]
    rfl
  · have hout := Repr.update_outside repr blk₀.bytes (q.offsetFrom blk₀.bptr) hb
      (data.map (Cell.shared 0)) i (by omega)
    have hlen : i < (repr.update blk₀.bytes (q.offsetFrom blk₀.bptr) hb
        (data.map (Cell.shared 0))).toList.length := by
      rw [Vector.length_toList]; exact hi
    have := hEx'' i hlen
    rw [hb2, List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem hi] at hout
    rw [Option.some.inj hout] at this
    exact this

theorem retire_step {s : Heap} {id : Nat} :
    ∀ base, AllExclusive (s.retire id) base →
      AllExclusive s base ∧ (Bytes.RootReturn s base → Bytes.RootReturn (s.retire id) base) := by
  intro base hEx
  refine ⟨fun blk hl => ?_, fun h => Bytes.RootReturn.retire h id⟩
  by_cases hne : base = id
  · subst hne
    exact hEx { blk with active := false } (by simp [Heap.retire, update, hl])
  · exact hEx blk (by simp [Heap.retire, update, hne, hl])

theorem Heap.endExposureAt_run {T : Type} {repr : Repr T} {p : RawPtr T} {count depth : Nat}
    {s s' : Heap} (run : Heap.endExposureAt repr p count depth s = some s') :
    s' = s.retire p.provenance := by
  unfold Heap.endExposureAt at run
  cases hl : s.allocations p.provenance
  · simp [hl] at run
  · simp only [hl, Bind.bind, Option.bind] at run
    split at run
    · exact (Heap.commit_success _ _ run).1
    · contradiction

/-- A block, with some cell which is not exclusive. -/
theorem Bytes.block_cell {T : Type} {repr : Repr T} {p : RawPtr T} {bptr : BasePtr}
    {cells : List Cell} {a : Fragment} (h : Bytes.block repr p bptr cells a)
    (hne : 0 < cells.length) :
    a (.cell p.provenance (p.offsetFrom bptr + 0) bptr (cells[0]'hne)) := by
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨0, hne, rfl⟩

theorem flatMap_shared_getElem_depth {n k : Nat} {size : Nat} (data : Vector (Vector Byte size) n)
    (i : Nat) (hi : i < (data.flatMap (fun bytes => bytes.map (Cell.shared k))).toList.length) :
    ((data.flatMap (fun bytes => bytes.map (Cell.shared k))).toList[i]).depth = some k := by
  rw [Vector.getElem_toList, Vector.getElem_flatMap (by simpa using hi)]
  simp

/-- The operations whose post fragments have a cell of the block which is not exclusive keep the
authority. -/
theorem modify_step_nonExclusive {T : Type} {repr : Repr T} {p : RawPtr T}
    {change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r)} {s s' : Heap} {a' : Fragment}
    {index : Nat} {bptr : BasePtr} {c : Cell}
    (run : Heap.modify repr p change s = some s') (hm' : Fragment.Matches s' a')
    (hc : a' (.cell p.provenance index bptr c)) (hdepth : c.depth ≠ some 0) :
    ∀ base, AllExclusive s' base →
      AllExclusive s base ∧ (Bytes.RootReturn s base → Bytes.RootReturn s' base) :=
  modify_step run fun hEx => (not_allExclusive_of_cell hm' hc hdepth hEx).elim

/-! ### The authority, for each operation -/

theorem Bytes.read.auth {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (value : T)
    (depth : Nat) :
    Bytes.AuthPres (Bytes.pointsTo repr p bptr value depth) (State.read repr p)
      (fun x h => x = value ∧ Bytes.pointsTo repr p bptr value depth h) :=
  Bytes.AuthPres.of_eq (fun _ _ h => NoOwned.pointsTo h.2) (fun _ _ _ h => h.2)

theorem Bytes.write_pointsTo.auth {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old value : T) (hsize : 0 < repr.size) :
    Bytes.AuthPres (Bytes.pointsTo repr p bptr old) (State.write repr p value)
      (fun _ => Bytes.pointsTo repr p bptr value) := by
  refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.pointsTo h) ?_
  rintro a F s ⟨bytes, _, hblock⟩ hd hm hi x s' hx a' hd' hm' hi' hB' base hEx _
  obtain ⟨_, _, rfl⟩ := hblock
  exact write_step hsize ((Fragment.matches_union _ _ _).mp hm).1 hx base hEx

theorem Bytes.readRange.auth {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) :
    Bytes.AuthPres (Bytes.pointsToRange repr p bptr values depth) (State.readRange repr p count)
      (fun result h => result = values.toList ∧ Bytes.pointsToRange repr p bptr values depth h) :=
  Bytes.AuthPres.of_eq (fun _ _ h => NoOwned.pointsToRange h.2) (fun _ _ _ h => h.2)

theorem Bytes.borrowRange.auth {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Bytes.AuthPres (Bytes.pointsToRange repr p bptr values) (State.borrowRange repr p count)
      (fun result h => result = values.toList ∧
        Bytes.block repr p bptr (List.replicate (count * repr.size) .borrowed) h) := by
  refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.block h.2) ?_
  rintro a F s _ _ _ _ x s' hx a' _ hm' _ hB' base hEx _
  have hlen : 0 < (List.replicate (count * repr.size) Cell.borrowed).length := by
    simp; first | exact ⟨hcount, hsize⟩ | exact Nat.mul_pos hcount hsize
  have run := hx.2.2
  unfold Heap.borrowRange Heap.modifyRange at run
  exact modify_step_nonExclusive run ((Fragment.matches_union _ _ _).mp hm').1
    (Bytes.block_cell hB'.2 hlen) (by simp) base hEx

theorem Bytes.shareRange.auth {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Bytes.AuthPres (Bytes.pointsToRange repr p bptr values depth) (State.shareRange repr p count)
      (fun result h => result = values.toList ∧
        Bytes.pointsToRange repr p bptr values (depth + 1) h) := by
  refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.pointsToRange h.2) ?_
  rintro a F s _ _ _ _ x s' hx a' _ hm' _ ⟨_, data, _, hblock⟩ base hEx _
  have hlen : 0 < (data.flatMap (fun bytes => bytes.map (Cell.shared (depth + 1)))).toList.length := by
    simp; first | exact ⟨hcount, hsize⟩ | exact Nat.mul_pos hcount hsize
  have run := hx.2
  unfold Heap.shareRange Heap.modifyRange at run
  exact modify_step_nonExclusive run ((Fragment.matches_union _ _ _).mp hm').1
    (Bytes.block_cell hblock hlen) (by rw [flatMap_shared_getElem_depth]; simp) base hEx

theorem Bytes.endShareRange.auth {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) (positive : 0 < depth) (hcount : 0 < count)
    (hsize : 0 < repr.size) :
    Bytes.AuthPres (Bytes.pointsToRange repr p bptr values (depth + 1))
      (State.endShareRange repr p values.toList)
      (fun _ => Bytes.pointsToRange repr p bptr values depth) := by
  refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.pointsToRange h) ?_
  rintro a F s _ _ _ _ x s' hx a' _ hm' _ ⟨data, _, hblock⟩ base hEx _
  have hlen : 0 < (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList.length := by
    simp; first | exact ⟨hcount, hsize⟩ | exact Nat.mul_pos hcount hsize
  have run := hx.2
  unfold Heap.endShareRange Heap.modifyRange at run
  exact modify_step_nonExclusive run ((Fragment.matches_union _ _ _).mp hm').1
    (Bytes.block_cell hblock hlen) (by rw [flatMap_shared_getElem_depth]; simp; omega) base hEx

/-- Retiring an exposure keeps the authority. -/
theorem Bytes.endExposure.auth {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat)
    {op : Heap → Unit → Heap → Prop}
    (hop : ∀ s x s', op s x s' → Heap.endExposureAt repr p count depth s = some s') :
    Bytes.AuthPres
      (Bytes.alloc repr p p.address count false ∗ᵇ readableRange repr p bptr values depth) op
      (fun _ => Bytes.empty) := by
  refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.empty h) ?_
  rintro a F s _ _ _ _ x s' hx _ _ _ _ _ base hEx _
  obtain rfl := Heap.endExposureAt_run (hop s x s' hx)
  exact retire_step base hEx

theorem Bytes.add.auth {T : Type} (repr : Repr T) (p : RawPtr T) (base : BasePtr)
    (values : Vector T count) (depth : Nat) (i : Usize) (P : Fragment → Prop)
    (view : ∀ h, P h → readableRange repr p base values depth h) :
    Bytes.AuthPres P (State.offset repr p i.val)
      (fun result h => result.provenance = p.provenance ∧
        result.address.val = p.address.val + i.val * repr.size ∧ P h) :=
  Bytes.AuthPres.of_eq (fun _ _ h => NoOwned.readableRange (view _ h.2.2)) (fun _ _ _ h => h.2)

theorem Bytes.readElem.auth {T : Type} [Pointee T] (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) (i : Fin count) (P : Fragment → Prop)
    (view : ∀ h, P h → readableRange (Pointee.repr (T := T)) p bptr values depth h) :
    Bytes.AuthPres P (State.read (Pointee.repr (T := T)) (p.elem i.val))
      (fun result h => result = values[i.val] ∧ P h) :=
  Bytes.AuthPres.of_eq (fun _ _ h => NoOwned.readableRange (view _ h.2)) (fun _ _ _ h => h.2)


/-! ### The authority, for the allocations -/

theorem Heap.newBlock_fresh {T : Type} {repr : Repr T} {data : List (Vector Byte repr.size)}
    {own : Bool} {bptr : BasePtr} {root : Option Nat} {s s' : Heap} {p : RawPtr T}
    (run : Heap.newBlock repr data own bptr root s = some (p, s')) :
    s' = ⟨update s.allocations s.next
      (some ⟨bptr, root.getD s.next, repr.create data 0, own, true, true⟩), s.next + 1⟩ := by
  cases hcr : s.createRepr ⟨bptr, root.getD s.next, repr.create data 0, own, true, true⟩ with
  | none => simp [Heap.newBlock, hcr] at run
  | some r =>
    obtain ⟨id, s₁⟩ := r
    simp only [Heap.newBlock, hcr, Option.map_some] at run
    rw [Option.ite_none_right_eq_some] at run
    obtain ⟨_, hrun⟩ := run
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨_, rfl⟩ := hrun
    exact (Heap.createRepr.success hcr).2

theorem Heap.newSharedExposure_fresh {T : Type} {repr : Repr T}
    {data : List (Vector Byte repr.size)} {bptr : BasePtr} {root : Option Nat} {s s' : Heap}
    {p : RawPtr T} (run : Heap.newSharedExposure repr data bptr root s = some (p, s')) :
    s' = ⟨update s.allocations s.next
      (some ⟨bptr, root.getD s.next, repr.create data 1, false, true, true⟩), s.next + 1⟩ := by
  cases hcr : s.createRepr ⟨bptr, root.getD s.next, repr.create data 1, false, true, true⟩ with
  | none => simp [Heap.newSharedExposure, hcr] at run
  | some r =>
    obtain ⟨id, s₁⟩ := r
    simp only [Heap.newSharedExposure, hcr, Option.map_some] at run
    rw [Option.ite_none_right_eq_some] at run
    obtain ⟨_, hrun⟩ := run
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨_, rfl⟩ := hrun
    exact (Heap.createRepr.success hcr).2

theorem Repr.create_shared {T : Type} {repr : Repr T} {data : List (Vector Byte repr.size)}
    {depth : Nat} : ∀ c ∈ repr.create data depth, ∃ b, c = Cell.shared depth b := by
  intro c hc
  simp only [Repr.create, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨_, _, b, _, rfl⟩ := hc
  exact ⟨b, rfl⟩

/-- A fresh non-empty block (whose cells are not borrowed) can't be a view of the root of an active
block whose cells are all exclusive: it would overlap one of its cells. -/
theorem fresh_block_authority {s : Heap} {E : Block} {base : Nat} {blk : Block}
    (hi : s.Inv) (hi' : (Heap.mk (update s.allocations s.next (some E)) (s.next + 1)).Inv)
    (hE : 0 < E.repr.length) (hshared : ∀ c ∈ E.repr, ∃ d b, c = Cell.shared d b)
    (hl : s.allocations base = some blk) (hActive : blk.active = true)
    (hEx : ∀ (i : Nat) (hi : i < blk.repr.length), blk.repr[i].depth = some 0)
    (hAuth : Bytes.RootReturn s base) :
    Bytes.RootReturn (Heap.mk (update s.allocations s.next (some E)) (s.next + 1)) base := by
  have hbase := hi.base_lt hl
  intro blk' hl'
  have hlb : (update s.allocations s.next (some E)) base = s.allocations base := by
    simp [update, Nat.ne_of_lt hbase]
  change (update s.allocations s.next (some E)) base = some blk' at hl'
  rw [hlb, hl] at hl'
  cases hl'
  obtain ⟨root, hr, hbptr, hlen, hna⟩ := hAuth blk hl
  have hroot := hi.base_lt hr
  have hlr : (update s.allocations s.next (some E)) blk.root = some root := by
    simp [update, Nat.ne_of_lt hroot, hr]
  refine ⟨root, hlr, hbptr, hlen, ?_⟩
  unfold Heap.noAliases at hna ⊢
  simp only [List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro j hj
    have hj' := List.mem_range.mp hj
    have := List.all_eq_true.mp hna j hj
    simpa [update, Nat.ne_of_lt hj'] using this
  · have hfresh₀ : (update s.allocations s.next (some E)) s.next = some E := by simp [update]
    rw [hfresh₀]
    by_cases hb : s.next = base
    · simp [hb]
    · have hNot : E.active = false ∨ E.root ≠ blk.root := by
        cases hEa : E.active
        · exact Or.inl rfl
        · refine Or.inr fun hER => ?_
          -- `E` is within the range of the root, which is the range of `blk`
          have hvalid := hi'.validBlock hfresh₀
          simp only [Heap.validBlock, Bool.and_eq_true] at hvalid
          have hRange := hvalid.1.2
          rw [hER, hlr] at hRange
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hRange
          have hcompat := (Heap.compatible_iff _ _).mp
            (hi'.compatible (i := s.next) (j := base) hfresh₀ (hlb.trans hl) hb)
          rcases hcompat with h | h | h
          · simp [hEa] at h
          · simp [hActive] at h
          · obtain ⟨⟨⟨_, hlo⟩, hhi⟩, _⟩ := hRange
            rw [← hbptr] at hlo hhi
            rw [← hlen] at hhi
            have hj : E.bptr.val - blk.bptr.val < blk.repr.length := by omega
            have hc := h 0 hE (E.bptr.val - blk.bptr.val) hj (by omega)
            obtain ⟨d, x, hx⟩ := hshared _ (List.getElem_mem hE)
            have hd := hEx _ hj
            cases hy : blk.repr[E.bptr.val - blk.bptr.val] with
            | borrowed => simp [hy] at hd
            | shared n y =>
              simp [hy] at hd
              subst hd
              simp [hx, hy, Cell.compatible] at hc
      rcases hNot with h | h <;> simp [h, hb]

/-- A fresh block without owned cleanup (an exposure) keeps the authority of the owned exclusive
blocks of the frame. -/
theorem authOK_fresh {s : Heap} {E : Block} {h F : Fragment}
    (hi : s.Inv) (hi' : (Heap.mk (update s.allocations s.next (some E)) (s.next + 1)).Inv)
    (hE : 0 < E.repr.length) (hshared : ∀ c ∈ E.repr, ∃ d b, c = Cell.shared d b)
    (hm : Fragment.Matches s F) (hAuth : AuthOK s F) (hNo : NoOwned h) :
    AuthOK (Heap.mk (update s.allocations s.next (some E)) (s.next + 1)) (h ∪ F) := by
  intro base size bptr hc hEx
  rcases hc with hc | hc
  · exact (hNo base size bptr hc).elim
  · obtain ⟨blk, hl, _, hlive, _, _⟩ := hm _ hc
    have hbase := hi.base_lt hl
    have hlb : (update s.allocations s.next (some E)) base = s.allocations base := by
      simp [update, Nat.ne_of_lt hbase]
    have hEx' : AllExclusive s base := fun b hb => hEx b (by
      change (update s.allocations s.next (some E)) base = some b
      rw [hlb]; exact hb)
    have hActive : blk.active = true := by
      simp only [Heap.live, Bool.and_eq_true] at hlive
      exact hlive.1
    exact fresh_block_authority hi hi' hE hshared hl hActive (hEx' blk hl)
      (hAuth base size bptr hc hEx')

/-! ## Lifting local heap operations -/

/-- A family of local heap operations, indexed by the base pointer of the block, lifted to the
upward closures. -/
theorem ispec_checked_local {α : Type} {A : BasePtr → Fragment → Prop}
    {modify : Heap → α → Heap → Prop} {B : BasePtr → α → Fragment → Prop}
    (hLocal : ∀ bptr, Bytes.LocalOp (A bptr) modify (B bptr))
    (hAuth : ∀ bptr, Bytes.AuthPres (A bptr) modify (B bptr)) :
    ispec (iexists fun bptr => upClose (A bptr)) (Result.checkedModify modify)
      (fun x => iexists fun bptr => upClose (B bptr x)) := by
  apply ispec_exists.mpr
  intro bptr
  exact ispec_conseq (ispec_checkedModify (Bytes.LocalOp.upClose (hLocal bptr) (hAuth bptr)))
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
  ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.read.spec _ p bptr value 0 Pointee.Sized.pos)
      (fun bptr => Bytes.read.auth _ p bptr value 0))
    (entails_refl _) (fun _ => iexists_upClose_pure_and)

@[step]
theorem MutRawPtr.write.spec {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.NoPointers T]
    (p : MutRawPtr T) (oldValue newValue : T) :
    ⦃ p ↦ oldValue ⦄ MutRawPtr.write p newValue ⦃ p ↦ newValue ⦄ :=
  ispec_checked_local
    (fun bptr => Bytes.write_pointsTo.spec _ p bptr oldValue newValue
      (Pointee.NoPointers.no_pointers newValue) Pointee.Sized.pos)
    (fun bptr => Bytes.write_pointsTo.auth _ p bptr oldValue newValue Pointee.Sized.pos)

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
  refine ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.readRange.local _ p bptr (listVec values) 0 hne Pointee.Sized.pos)
      (fun bptr => Bytes.readRange.auth _ p bptr (listVec values) 0))
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
  refine ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.borrowRange.local _ p bptr (listVec values) hne Pointee.Sized.pos)
      (fun bptr => Bytes.borrowRange.auth _ p bptr (listVec values) hne Pointee.Sized.pos))
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
  refine ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.shareRange.local _ p bptr (listVec values) depth hne Pointee.Sized.pos)
      (fun bptr => Bytes.shareRange.auth _ p bptr (listVec values) depth hne Pointee.Sized.pos))
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
  have h := ispec_checked_local
    (fun bptr => Bytes.endShareRange.local (Pointee.repr (T := T)) p bptr (listVec values) depth
      positive hne Pointee.Sized.pos)
    (fun bptr => Bytes.endShareRange.auth (Pointee.repr (T := T)) p bptr (listVec values) depth
      positive hne Pointee.Sized.pos)
  simp only [listVec_toList] at h
  exact h

/-! ## Pointer arithmetic -/

theorem Bytes.add.local {T : Type} (repr : Repr T) (p : RawPtr T) (base : BasePtr)
    (values : Vector T count) (depth : Nat) (i : Usize) (hcount : 0 < count)
    (hsize : 0 < repr.size) (hle : i.val ≤ count) (P : Fragment → Prop)
    (view : ∀ h, P h → readableRange repr p base values depth h) :
    Bytes.LocalOp P (State.offset repr p i.val)
      (fun result h => result.provenance = p.provenance ∧
        result.address.val = p.address.val + i.val * repr.size ∧ P h) := by
  intro h F s hP hd hm hi
  have keep := hP
  have hp := view h hP
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have bound := readableRange_bound repr p base values depth hcount hsize h s
    hp localMatch hi
  have hfit : p.address.val + i.val * repr.size < 2 ^ UScalarTy.numBits .Usize := by
    have := Nat.mul_le_mul_right repr.size hle
    omega
  obtain ⟨data, _, hlo, _, cells⟩ := hp
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

theorem RawPtr.eq_elem {T : Type} [Pointee T] {p result : RawPtr T} {i : Nat}
    (hprov : result.provenance = p.provenance)
    (haddr : result.address.val = p.address.val + i * (Pointee.repr (T := T)).size) :
    result = p.elem i := by
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
      have h1 : bv.toNat = p.address.val + i * (Pointee.repr (T := T)).size := haddr
      rw [← h1]
      exact (Nat.mod_eq_of_lt bv.isLt).symm

/-- Pointer arithmetic within a range, including the pointer one past its end. -/
@[step]
theorem RawPtr.add.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (values : List T) (count : Usize) (hne : 0 < values.length)
    (hCount : count.val ≤ values.length) :
    ⦃ p ↦* values ⦄ RawPtr.add p count
      ⦃ result => ⌜result = p.elem count.val⌝ ∗ p ↦* values ⦄ := by
  refine ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.add.local _ p bptr (listVec values) 0 count hne Pointee.Sized.pos hCount _
        (fun _ hp => pointsToRange_readable hp))
      (fun bptr => Bytes.add.auth _ p bptr (listVec values) 0 count _
        (fun _ hp => pointsToRange_readable hp)))
    (entails_refl _) (fun result => ?_)
  rintro h ⟨bptr, a, ⟨hprov, haddr, hA⟩, hSub⟩
  exact (sep_pure_l _ _ h).mpr ⟨RawPtr.eq_elem hprov haddr, bptr, a, hA, hSub⟩

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
    (hPost : ∀ s F, s.Inv → Fragment.Matches s F → AuthOK s F → ∀ x s', modify s x s' →
      ∃ h, h.Disjoint F ∧ Fragment.Matches s' (h ∪ F) ∧ s'.Inv ∧ AuthOK s' (h ∪ F) ∧ A x h) :
    ispec emp (Result.allocatingModify modify) (fun x => upClose (A x)) := by
  apply ispec_allocatingModify
  intro s h frame _ hd hm hi hAuth x s' hx
  obtain ⟨h', hd', hm', hi', hAuth', hA⟩ := hPost s (h ∪ frame) hi hm hAuth x s' hx
  have hd'' := Fragment.disjoint_union_right.mp hd'
  refine ⟨h' ∪ h, Fragment.disjoint_union_left.mpr ⟨hd''.2, hd⟩, ?_, hi', ?_,
    h', hA, PartialCommMonoid.Subheap.union_left hd''.1⟩
  · rwa [Fragment.union_assoc]
  · rwa [Fragment.union_assoc]

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

theorem Repr.create_length {T : Type} {repr : Repr T} (data : List (Vector Byte repr.size))
    (depth : Nat) : (repr.create data depth).length = data.length * repr.size := by
  induction data with
  | nil => simp [Repr.create]
  | cons x xs ih =>
    simp only [Repr.create, List.flatMap_cons, List.length_append, List.length_map,
      Vector.length_toList, List.length_cons] at ih ⊢
    rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem exposure_authOK {T : Type} {repr : Repr T} {data : List (Vector Byte repr.size)}
    {bptr : BasePtr} {root : Option Nat} {depth : Nat} {s : Heap} {h F : Fragment}
    (hi : s.Inv) (hm : Fragment.Matches s F) (hAuth : AuthOK s F) (hNo : NoOwned h)
    (hlen : 0 < data.length) (hsize : 0 < repr.size)
    (hi' : (Heap.mk (update s.allocations s.next
      (some ⟨bptr, root.getD s.next, repr.create data depth, false, true, true⟩))
        (s.next + 1)).Inv) :
    AuthOK (Heap.mk (update s.allocations s.next
      (some ⟨bptr, root.getD s.next, repr.create data depth, false, true, true⟩))
        (s.next + 1)) (h ∪ F) :=
  authOK_fresh hi hi' (by rw [Repr.create_length]; exact Nat.mul_pos hlen hsize)
    (fun c hc => let ⟨b, hb⟩ := Repr.create_shared c hc; ⟨depth, b, hb⟩) hm hAuth hNo

/-- An exposure at an address is an exposure. -/
theorem State.exposeAt_newBlock {T : Type} {repr : Repr T} {values : List T} {address : BasePtr}
    {s₀ s₁ : Heap} {p : RawPtr T} (h : State.exposeAt repr values address s₀ p s₁) :
    State.newBlock repr values false s₀ p s₁ := by
  obtain ⟨data, root, hexp, hnew⟩ := h
  exact ⟨data, address, root, by simpa using hexp, hnew⟩

/-- An exposure at an address is there. -/
theorem State.exposeAt_address {T : Type} {repr : Repr T} {values : List T} {address : BasePtr}
    {s₀ s₁ : Heap} {p : RawPtr T} (h : State.exposeAt repr values address s₀ p s₁) :
    p.address = address := by
  obtain ⟨data, root, -, hnew⟩ := h
  unfold Heap.newBlock at hnew
  split_ifs at hnew
  obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp hnew
  cases h
  rfl

/-- A shared exposure at an address is a shared exposure. -/
theorem State.sharedExposeAt_newSharedExposure {T : Type} {repr : Repr T} {values : List T}
    {address : BasePtr} {s₀ s₁ : Heap} {p : RawPtr T}
    (h : State.sharedExposeAt repr values address s₀ p s₁) :
    State.newSharedExposure repr values s₀ p s₁ := by
  obtain ⟨data, root, hexp, hnew⟩ := h
  exact ⟨data, address, root, hexp, hnew⟩

/-- A shared exposure at an address is there. -/
theorem State.sharedExposeAt_address {T : Type} {repr : Repr T} {values : List T}
    {address : BasePtr} {s₀ s₁ : Heap} {p : RawPtr T}
    (h : State.sharedExposeAt repr values address s₀ p s₁) : p.address = address := by
  obtain ⟨data, root, -, hnew⟩ := h
  unfold Heap.newSharedExposure at hnew
  split_ifs at hnew
  obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp hnew
  cases h
  rfl

/-- Exposes a mutable safe place, whose values are `values`. -/
@[step]
theorem RawPtr.allocExposure.spec {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.Calibrated T]
    (values : List T) (address : BasePtr) (hne : 0 < values.length) :
    ⦃ emp ⦄ RawPtr.allocExposure (Pointee.repr (T := T)) values address
      ⦃ p => p.exposure values.length ∗ p ↦* values ⦄ := by
  have h := ispec_allocating_emp (A := fun p => Bytes.alloc (Pointee.repr (T := T)) p p.address
      values.length false ∗ᵇ Bytes.pointsToRange (Pointee.repr (T := T)) p p.address
        (listVec values) 0)
    (modify := State.exposeAt (Pointee.repr (T := T)) values address)
    (fun s F hi hm hAuth p s₁ hx => by
      replace hx := State.exposeAt_newBlock hx
      have hx' : State.newBlock (Pointee.repr (T := T)) (listVec values).toList false s p s₁ := by
        simpa using hx
      obtain ⟨h, hd, hm', hi', hA⟩ := Bytes.allocExposure.post (Pointee.repr (T := T))
        (listVec values) Pointee.Calibrated.calibrated s F hi hm p s₁ hx'
      refine ⟨h, hd, hm', hi', ?_, hA⟩
      obtain ⟨data, bptr, root, exposed, created⟩ := hx
      obtain ⟨len, _⟩ := exposesList_index _ s bptr.val values data exposed
      have hs := Heap.newBlock_fresh created
      subst hs
      exact exposure_authOK hi hm hAuth
        (NoOwned.sep (fun _ ha => NoOwned.alloc_false ha) (fun _ hb => NoOwned.pointsToRange hb) hA)
        (by omega) Pointee.Sized.pos hi')
  refine ispec_conseq h (entails_refl _) (fun p => entails_trans upClose_sep ?_)
  exact sep_mono (entails_refl _) (fun h hU => ⟨p.address, hU⟩)

/-- Exposes a shared safe place, whose values are `values`. -/
@[step]
theorem RawPtr.allocSharedExposure.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (values : List T) (address : BasePtr) (hne : 0 < values.length) :
    ⦃ emp ⦄ RawPtr.allocSharedExposure (Pointee.repr (T := T)) values address
      ⦃ p => p.exposure values.length ∗ p.readable 1 values ⦄ := by
  have h := ispec_allocating_emp (A := fun p => Bytes.alloc (Pointee.repr (T := T)) p p.address
      values.length false ∗ᵇ readableRange (Pointee.repr (T := T)) p p.address
        (listVec values) 1)
    (modify := State.sharedExposeAt (Pointee.repr (T := T)) values address)
    (fun s F hi hm hAuth p s₁ hx => by
      replace hx := State.sharedExposeAt_newSharedExposure hx
      have hx' : State.newSharedExposure (Pointee.repr (T := T)) (listVec values).toList s p s₁ := by
        simpa using hx
      obtain ⟨h, hd, hm', hi', hA⟩ := Bytes.allocSharedExposure.post (Pointee.repr (T := T))
        (listVec values) s F hi hm p s₁ hx'
      refine ⟨h, hd, hm', hi', ?_, hA⟩
      obtain ⟨data, bptr, root, exposed, created⟩ := hx
      obtain ⟨len, _⟩ := exposesList_index _ s bptr.val values data exposed
      have hs := Heap.newSharedExposure_fresh created
      subst hs
      exact exposure_authOK hi hm hAuth
        (NoOwned.sep (fun _ ha => NoOwned.alloc_false ha) (fun _ hb => NoOwned.readableRange hb) hA)
        (by omega) Pointee.Sized.pos hi')
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
    (Pointee.repr (T := T)) p values) (B := fun _ _ => Bytes.empty) (fun bptr => ?_)
    (fun bptr => Bytes.endExposure.auth _ p bptr (listVec values) 1 (fun _ _ _ h => h.2))) hEq
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

/-- Pointer arithmetic within a range whose cells decode to `values`. -/
@[step]
theorem RawPtr.add.spec_readable {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (depth : Nat) (values : List T) (count : Usize) (hne : 0 < values.length)
    (hCount : count.val ≤ values.length) :
    ⦃ p.readable depth values ⦄ RawPtr.add p count
      ⦃ result => ⌜result = p.elem count.val⌝ ∗ p.readable depth values ⦄ := by
  refine ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.add.local _ p bptr (listVec values) depth count hne Pointee.Sized.pos
        hCount _ (fun _ hp => hp))
      (fun bptr => Bytes.add.auth _ p bptr (listVec values) depth count _ (fun _ hp => hp)))
    (entails_refl _) (fun result => ?_)
  rintro h ⟨bptr, a, ⟨hprov, haddr, hA⟩, hSub⟩
  exact (sep_pure_l _ _ h).mpr ⟨RawPtr.eq_elem hprov haddr, bptr, a, hA, hSub⟩

/-! ## Ending exposures, and accesses within ranges -/

theorem sep_upClose {A B : Fragment → Prop} : upClose A ∗ upClose B ⊢ upClose (Bytes.sep A B) := by
  rintro _ ⟨h₁, h₂, hd, rfl, ⟨a, ha, hsa⟩, ⟨b, hb, hsb⟩⟩
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

/-- Retires the exposure of `as_mut_ptr` and `from_mut`. -/
@[step]
theorem RawPtr.endExposure.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (values : List T) (hne : 0 < values.length) :
    ⦃ p.exposure values.length ∗ p ↦* values ⦄
      RawPtr.endExposure (Pointee.repr (T := T)) p values.length ⦃ emp ⦄ := by
  have hEq : p.exposure values.length ∗ p ↦* values ⊢
      iexists fun bptr => upClose (Bytes.alloc (Pointee.repr (T := T)) p p.address
        values.length false ∗ᵇ readableRange (Pointee.repr (T := T)) p bptr
          (listVec values) 0) := by
    rintro h ⟨h₁, h₂, hd, rfl, hE, bptr, a, ha, hsa⟩
    obtain ⟨c, hc, hsc⟩ := sep_upClose (A := Bytes.alloc (Pointee.repr (T := T)) p p.address
      values.length false) (B := readableRange (Pointee.repr (T := T)) p bptr (listVec values) 0)
      _ ⟨h₁, h₂, hd, rfl, hE, a, pointsToRange_readable ha, hsa⟩
    exact ⟨bptr, c, hc, hsc⟩
  refine ispec_conseq (ispec_checked_local (modify := State.removeExposure
    (Pointee.repr (T := T)) p values.length) (B := fun _ _ => Bytes.empty)
    (fun bptr => Bytes.endExposure.local _ p bptr (listVec values) 0 hne Pointee.Sized.pos)
    (fun bptr => Bytes.endExposure.auth _ p bptr (listVec values) 0 (fun _ _ _ h => h))) hEq
    (fun _ _ _ => trivial)

theorem Bytes.pointsToRange_singleton {T : Type} {repr : Repr T} {p : RawPtr T} {bptr : BasePtr}
    {value : T} {depth : Nat} {h : Fragment} :
    Bytes.pointsToRange repr p bptr (listVec [value]) depth h ↔
      Bytes.pointsTo repr p bptr value depth h := by
  constructor
  · rintro ⟨data, encoded, hb⟩
    refine ⟨data[0], encoded ⟨0, by simp⟩, ?_⟩
    have : (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList =
        (data[0].map (Cell.shared depth)).toList := by
      obtain ⟨⟨arr⟩, harr⟩ := data
      match arr, harr with
      | [x], _ => simp [Vector.flatMap, Vector.toList]
    rwa [← this]
  · rintro ⟨bytes, encoded, hb⟩
    refine ⟨#v[bytes], fun i => ?_, ?_⟩
    · obtain ⟨i, hi⟩ := i
      have : i = 0 := by simp at hi; omega
      subst this
      simpa using encoded
    · have : (#v[bytes].flatMap (fun bytes => bytes.map (Cell.shared depth))).toList =
          (bytes.map (Cell.shared depth)).toList := by
        simp [Vector.flatMap, Vector.toList]
      rwa [this]

@[simp] theorem RawPtr.range_singleton {T : Type} [Pointee T] (p : RawPtr T) (value : T) :
    (p ↦* [value]) = (p ↦ value) := by
  apply IProp.ext
  intro h
  constructor
  · rintro ⟨bptr, a, ha, hsa⟩
    exact ⟨bptr, a, Bytes.pointsToRange_singleton.mp ha, hsa⟩
  · rintro ⟨bptr, a, ha, hsa⟩
    exact ⟨bptr, a, Bytes.pointsToRange_singleton.mpr ha, hsa⟩

theorem RawPtr.elem_provenance {T : Type} [Pointee T] (p : RawPtr T) (i : Nat) :
    (p.elem i).provenance = p.provenance := rfl

theorem RawPtr.elem_address {T : Type} [Pointee T] (p : RawPtr T) (i : Nat)
    (hfit : p.address.val + i * (Pointee.repr (T := T)).size < 2 ^ UScalarTy.numBits .Usize) :
    (p.elem i).address.val = p.address.val + i * (Pointee.repr (T := T)).size := by
  change (BitVec.ofNat _ _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]

theorem Bytes.readElem.local {T : Type} [Pointee T] (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) (i : Fin count)
    (hsize : 0 < (Pointee.repr (T := T)).size) (P : Fragment → Prop)
    (view : ∀ h, P h → readableRange (Pointee.repr (T := T)) p bptr values depth h) :
    Bytes.LocalOp P (State.read (Pointee.repr (T := T)) (p.elem i.val))
      (fun result h => result = values[i.val] ∧ P h) := by
  intro h F s hP hd hm hi
  have hp := view h hP
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have bound := readableRange_bound _ p bptr values depth
    (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt) hsize h s hp localMatch hi
  have hfit : p.address.val + i.val * (Pointee.repr (T := T)).size <
      2 ^ UScalarTy.numBits .Usize :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left
      (Nat.mul_le_mul_right (Pointee.repr (T := T)).size (Nat.le_of_lt i.isLt)) _) bound
  have hr := read_range_element (p := p) (q := p.elem i.val) i hsize rfl
    (p.elem_address i.val hfit) hp localMatch
  refine ⟨⟨values[i.val], s, hr, rfl⟩, ?_⟩
  rintro x s' ⟨hx, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hx.symm.trans hr), hP⟩

/-- Reads the `i`-th value of a range whose cells decode to `values`. -/
@[step]
theorem RawPtr.read.spec_readable {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (depth : Nat) (values : List T) (i : Nat) (hi : i < values.length) :
    ⦃ p.readable depth values ⦄ RawPtr.read (p.elem i)
      ⦃ result => ⌜result = values[i]⌝ ∗ p.readable depth values ⦄ := by
  refine ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.readElem.local p bptr (listVec values) depth ⟨i, hi⟩ Pointee.Sized.pos _
        (fun _ h => h))
      (fun bptr => Bytes.readElem.auth p bptr (listVec values) depth ⟨i, hi⟩ _ (fun _ h => h)))
    (entails_refl _) (fun _ => ?_)
  have : (listVec values)[i] = values[i] := by simp [listVec]
  simp only [this]
  exact iexists_upClose_pure_and

@[simp] theorem RawPtr.elem_zero {T : Type} [Pointee T] (p : RawPtr T) : p.elem 0 = p := by
  obtain ⟨prov, ⟨bv⟩⟩ := p
  simp [RawPtr.elem, UScalar.val]

/-- Reading the first value of a readable range. -/
theorem RawPtr.read.spec_readable_head {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (depth : Nat) (values : List T) (hne : 0 < values.length) :
    ⦃ p.readable depth values ⦄ RawPtr.read p
      ⦃ result => ⌜result = values[0]⌝ ∗ p.readable depth values ⦄ := by
  simpa using RawPtr.read.spec_readable p depth values 0 hne

/-- Reads the `i`-th value of a range. -/
@[step]
theorem RawPtr.read.spec_range {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (values : List T) (i : Nat) (hi : i < values.length) :
    ⦃ p ↦* values ⦄ RawPtr.read (p.elem i)
      ⦃ result => ⌜result = values[i]⌝ ∗ p ↦* values ⦄ := by
  refine ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.readElem.local p bptr (listVec values) 0 ⟨i, hi⟩ Pointee.Sized.pos _
        (fun _ hp => pointsToRange_readable hp))
      (fun bptr => Bytes.readElem.auth p bptr (listVec values) 0 ⟨i, hi⟩ _
        (fun _ hp => pointsToRange_readable hp)))
    (entails_refl _) (fun _ => ?_)
  have : (listVec values)[i] = values[i] := by simp [listVec]
  simp only [this]
  exact iexists_upClose_pure_and

/-! ## Writes within ranges, allocation, `from_mut` -/

theorem Bytes.pointsToRange_congr {T : Type} {repr : Repr T} {p : RawPtr T} {bptr : BasePtr}
    {depth : Nat} {n m : Nat} (hnm : n = m) (v : Vector T n) (w : Vector T m)
    (hvw : v.toList = w.toList) :
    Bytes.pointsToRange repr p bptr v depth = Bytes.pointsToRange repr p bptr w depth := by
  subst hnm
  have : v = w := Vector.toList_inj.mp hvw
  rw [this]

theorem Bytes.writeElem.local {T : Type} [Pointee T] (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (i : Fin count) (value : T)
    (noPointers : ∀ q, ¬ (Pointee.repr (T := T)).Carries value q)
    (hsize : 0 < (Pointee.repr (T := T)).size) :
    Bytes.LocalOp (Bytes.pointsToRange (Pointee.repr (T := T)) p bptr values 0)
      (State.write (Pointee.repr (T := T)) (p.elem i.val) value)
      (fun _ => Bytes.pointsToRange (Pointee.repr (T := T)) p bptr (values.set i.val value i.isLt) 0) := by
  intro h F s hp hd hm hi
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have bound := readableRange_bound _ p bptr values 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
    hsize h s (pointsToRange_readable hp) localMatch hi
  have hfit : p.address.val + i.val * (Pointee.repr (T := T)).size <
      2 ^ UScalarTy.numBits .Usize :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left
      (Nat.mul_le_mul_right (Pointee.repr (T := T)).size (Nat.le_of_lt i.isLt)) _) bound
  obtain ⟨rest, hsep, rebuild⟩ := pointsToRange_focus _ p (p.elem i.val) bptr values 0 i hsize rfl
    (p.elem_address i.val hfit) h hp
  obtain ⟨hE, hPost⟩ := Bytes.LocalOp.frame (R := rest)
    (Bytes.write_pointsTo.spec _ (p.elem i.val) bptr values[i.val] value noPointers hsize)
    h F s hsep hd hm hi
  refine ⟨hE, fun x s' hx => ?_⟩
  obtain ⟨h', hd', hm', hi', hq⟩ := hPost x s' hx
  exact ⟨h', hd', hm', hi', rebuild value h' hq⟩

theorem Bytes.writeElem.auth {T : Type} [Pointee T] (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (i : Fin count) (value : T)
    (hsize : 0 < (Pointee.repr (T := T)).size) :
    Bytes.AuthPres (Bytes.pointsToRange (Pointee.repr (T := T)) p bptr values 0)
      (State.write (Pointee.repr (T := T)) (p.elem i.val) value)
      (fun _ => Bytes.pointsToRange (Pointee.repr (T := T)) p bptr (values.set i.val value i.isLt) 0) := by
  refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.pointsToRange h) ?_
  rintro h F s hp hd hm hi x s' hx a' _ _ _ _ base hEx _
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have bound := readableRange_bound _ p bptr values 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
    hsize h s (pointsToRange_readable hp) localMatch hi
  have hfit : p.address.val + i.val * (Pointee.repr (T := T)).size <
      2 ^ UScalarTy.numBits .Usize :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left
      (Nat.mul_le_mul_right (Pointee.repr (T := T)).size (Nat.le_of_lt i.isLt)) _) bound
  obtain ⟨rest, ⟨c, r, _, rfl, ⟨bytes, _, hblock⟩, _⟩, _⟩ := pointsToRange_focus _ p (p.elem i.val)
    bptr values 0 i hsize rfl (p.elem_address i.val hfit) h hp
  obtain ⟨_, _, rfl⟩ := hblock
  exact write_step hsize ((Fragment.matches_union _ _ _).mp localMatch).1 hx base hEx

/-- Writes the `i`-th value of a range. -/
@[step]
theorem MutRawPtr.write.spec_range {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.NoPointers T]
    (p : MutRawPtr T) (values : List T) (i : Nat) (value : T) (hi : i < values.length) :
    ⦃ p ↦* values ⦄ MutRawPtr.write (p.elem i) value ⦃ p ↦* values.set i value ⦄ := by
  refine ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.writeElem.local p bptr (listVec values) ⟨i, hi⟩ value
        (Pointee.NoPointers.no_pointers value) Pointee.Sized.pos)
      (fun bptr => Bytes.writeElem.auth p bptr (listVec values) ⟨i, hi⟩ value Pointee.Sized.pos))
    (entails_refl _) (fun _ => ?_)
  rintro h ⟨bptr, a, ha, hsa⟩
  refine ⟨bptr, a, ?_, hsa⟩
  rw [Bytes.pointsToRange_congr (by simp) _ (listVec (values.set i value)) (by simp [listVec])] at ha
  exact ha

theorem Bytes.newOwned.post {T : Type} (repr : Repr T) (value : T)
    (s₀ : Heap) (F : Fragment) (hi : s₀.Inv) (hm : Fragment.Matches s₀ F) :
    ∀ p s₁, State.newBlock repr [value] true s₀ p s₁ →
      ∃ h, h.Disjoint F ∧ Fragment.Matches s₁ (h ∪ F) ∧ s₁.Inv ∧
        (Bytes.alloc repr p p.address 1 true ∗ᵇ Bytes.pointsTo repr p p.address value) h := by
  rintro p s₁ ⟨data, bptr, root, encoded, created⟩
  match data, encoded with
  | [bytes], ⟨encoded, _⟩ =>
    obtain ⟨_, h, hd, hm, hi, a, b, hab, hh, ha, hb⟩ :=
      newBlock_single.resources repr bytes true bptr root hi hm created
    exact ⟨h, hd, hm, hi, a, b, hab, hh, ha, bytes, encoded, hb⟩

/-- `Box::into_raw`: the value is moved to a new block of the global allocator. -/
@[step]
theorem alloc.boxed.Box.into_raw.spec {T : Type} [Pointee T] (b : Box T) :
    ⦃ emp ⦄ alloc.boxed.Box.into_raw b ⦃ p => p ↦ b.val ∗ p.freeable 1 ⦄ := by
  unfold alloc.boxed.Box.into_raw RawPtr.newBlock
  have h := ispec_allocating_emp (A := fun p => Bytes.alloc (Pointee.repr (T := T)) p p.address
      1 true ∗ᵇ Bytes.pointsTo (Pointee.repr (T := T)) p p.address b.val)
    (modify := State.newBlock (Pointee.repr (T := T)) [b.val] true)
    (fun s F hi hm hAuth p s₁ hx => by
      obtain ⟨h, hd, hm', hi', hA⟩ := Bytes.newOwned.post (Pointee.repr (T := T)) b.val s F hi hm
        p s₁ hx
      refine ⟨h, hd, hm', hi', ?_, hA⟩
      obtain ⟨data, bptr, root, _, created⟩ := hx
      intro base size bptr' hc hEx
      rcases hc with hc | hc
      · obtain ⟨a, c, _, rfl, ⟨_, rfl⟩, hc'⟩ := hA
        rcases hc with hc | hc
        · simp only [Bytes.allocHeap, Fragment.single, Resource.cleanup.injEq] at hc
          obtain ⟨rfl, _⟩ := hc
          exact Bytes.owned_newBlock_root hi created
        · exact (NoOwned.pointsTo hc' base size bptr' hc).elim
      · obtain ⟨blk, hl, _, hlive, _, _⟩ := hm _ hc
        have hbase := hi.base_lt hl
        have hs := Heap.newBlock_fresh created
        have hlb : s₁.allocations base = s.allocations base := by
          subst hs; simp [update, Nat.ne_of_lt hbase]
        have hActive : blk.active = true := by
          simp only [Heap.live, Bool.and_eq_true] at hlive
          exact hlive.1
        have hEx' : AllExclusive s base := fun b hb => hEx b (by rw [hlb]; exact hb)
        exact Bytes.RootReturn.newOwned hi (hAuth base size bptr' hc hEx') hl hActive created)
  refine ispec_conseq h (entails_refl _) (fun p => entails_trans upClose_sep ?_)
  refine entails_trans (entails_of_eq (sep_comm_eq _ _)) ?_
  exact sep_mono (fun h hU => ⟨p.address, hU⟩) (entails_refl _)

/-- `ptr::from_mut`: exposes the place of a mutable borrow. -/
@[step]
theorem core.ptr.from_mut.spec {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.Calibrated T]
    (address : BasePtr) (r : MutBorrow T) :
    ⦃ emp ⦄ core.ptr.from_mut address r
      ⦃ (p, back) => ⌜back = core.ptr.end_from_mut p⌝ ∗ p ↦ r.val ∗ p.exposure 1 ⦄ := by
  unfold core.ptr.from_mut
  apply ispec_bind (RawPtr.allocExposure.spec [r.val] address (by simp))
    (entails_of_eq (sep_emp_r_eq emp).symm)
  intro p
  apply ispec_ok
  simp only [RawPtr.range_singleton, List.length_singleton, uncurry_apply_pair]
  iframe

/-- The backward computation of `ptr::from_mut`: reads the value, and retires the exposure. -/
@[step]
theorem core.ptr.end_from_mut.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : MutRawPtr T)
    (value : T) :
    ⦃ p ↦ value ∗ p.exposure 1 ⦄ core.ptr.end_from_mut p ⦃ result => ⌜result = value⌝ ⦄ := by
  unfold core.ptr.end_from_mut
  apply ispec_bind (RawPtr.read.spec p value) (entails_refl _)
  intro result
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  have hEnd := RawPtr.endExposure.spec p [result] (by simp)
  simp only [RawPtr.range_singleton, List.length_singleton] at hEnd
  apply ispec_bind hEnd (by iframe)
  intro _
  apply ispec_ok
  iframe

/-! ## Raw pointers to slices -/

/-- `as_mut_ptr`: exposes the cells of a mutable slice. -/
@[step]
theorem Slice.as_mut_ptr.spec {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.Calibrated T]
    (address : BasePtr) (s : MutBorrow (Slice T)) (hne : 0 < s.val.length) :
    ⦃ emp ⦄ Slice.as_mut_ptr address s
      ⦃ (p, back) => ⌜back = Slice.end_as_mut_ptr (Pointee.repr (T := T)) s.val p⌝ ∗
        p ↦* s.val.val ∗ p.exposure s.val.length ⦄ := by
  rw [Slice.as_mut_ptr_eq]
  apply ispec_bind (RawPtr.allocExposure.spec s.val.val address hne) (entails_of_eq (sep_emp_r_eq emp).symm)
  intro p
  apply ispec_ok
  simp only [uncurry_apply_pair]
  iframe

/-- The backward computation of `as_mut_ptr`: the cells become the new slice, and the exposure is
retired. -/
@[step]
theorem Slice.end_as_mut_ptr.spec {T : Type} [Pointee T] [Pointee.Sized T] (s : Slice T)
    (p : MutRawPtr T) (values : List T) (hLen : values.length = s.length)
    (hne : 0 < values.length) :
    ⦃ p ↦* values ∗ p.exposure s.length ⦄ Slice.end_as_mut_ptr (Pointee.repr (T := T)) s p
      ⦃ s' => ⌜s'.val = values⌝ ⦄ := by
  have hMax : values.length ≤ Usize.max := by rw [hLen]; exact s.property
  unfold Slice.end_as_mut_ptr
  rw [← hLen]
  apply ispec_bind (RawPtr.readRange.spec p values hne) (entails_refl _)
  intro vs
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  apply ispec_bind (RawPtr.endExposure.spec p vs hne) (by iframe)
  intro _
  simp only [hMax, dite_true]
  apply ispec_ok
  simp only [Slice.from_val]
  iframe

/-- `as_ptr`: exposes the cells of a shared slice, read-only. -/
@[step]
theorem Slice.as_ptr.spec {T : Type} [Pointee T] [Pointee.Sized T] (address : BasePtr)
    (s : SharedBorrow (Slice T)) (hne : 0 < s.val.length) :
    ⦃ emp ⦄ Slice.as_ptr address s
      ⦃ (p, back) => ⌜back = Slice.end_as_ptr (Pointee.repr (T := T)) s.val p⌝ ∗
        p.readable 1 s.val.val ∗ p.exposure s.val.length ⦄ := by
  rw [Slice.as_ptr_eq]
  apply ispec_bind (RawPtr.allocSharedExposure.spec s.val.val address hne)
    (entails_of_eq (sep_emp_r_eq emp).symm)
  intro p
  apply ispec_ok
  simp only [uncurry_apply_pair]
  iframe

/-- The backward computation of `as_ptr`: the cells must still decode to the slice, and the
exposure is retired. -/
@[step]
theorem Slice.end_as_ptr.spec {T : Type} [Pointee T] [Pointee.Sized T] (s : Slice T)
    (p : ConstRawPtr T) (hne : 0 < s.length) :
    ⦃ p.readable 1 s.val ∗ p.exposure s.length ⦄ Slice.end_as_ptr (Pointee.repr (T := T)) s p
      ⦃ emp ⦄ := by
  unfold Slice.end_as_ptr
  apply ispec_conseq (RawPtr.endSharedExposure.spec p s.val hne) (by iframe) (fun _ => entails_refl _)

/-- Borrows the cells of a range as a slice. -/
@[step]
theorem RawPtr.borrowSlice.spec {T : Type} [Pointee T] [Pointee.Sized T] (q : RawPtr T)
    (len : Usize) (values : List T) (hLen : len.val = values.length) (hne : 0 < values.length) :
    ⦃ q ↦* values ⦄ RawPtr.borrowSlice (Pointee.repr (T := T)) q len
      ⦃ s => ⌜s.val = values⌝ ∗ q ↦† len.val ⦄ := by
  unfold RawPtr.borrowSlice
  rw [hLen]
  apply ispec_bind (RawPtr.borrowRange.spec q values hne) (entails_of_eq (sep_emp_r_eq _).symm)
  intro vs
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  have hMax : vs.length ≤ Usize.max := by rw [← hLen]; scalar_tac
  simp only [hMax, dite_true]
  apply ispec_ok
  simp only [Slice.from_val]
  iframe

/-- `slice::from_raw_parts`: the cells of the range are shared by the slice (they become readable,
but not writable) until the borrow ends. -/
@[step]
theorem core.slice.raw.from_raw_parts.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (p : ConstRawPtr T) (len : Usize) (depth : Nat) (values : List T)
    (hLen : len.val = values.length) (hne : 0 < values.length) :
    ⦃ p.range depth values ⦄ core.slice.raw.from_raw_parts p len
      ⦃ (s, back) => ⌜s.val.val = values⌝ ∗
        ⌜back = RawPtr.endShareRange (Pointee.repr (T := T)) p values⌝ ∗
        p.range (depth + 1) values ⦄ := by
  unfold core.slice.raw.from_raw_parts
  rw [hLen]
  apply ispec_bind (RawPtr.shareRange.spec p depth values hne)
    (entails_of_eq (sep_emp_r_eq _).symm)
  intro vs
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  have hMax : vs.length ≤ Usize.max := by rw [← hLen]; scalar_tac
  simp only [hMax, dite_true]
  apply ispec_ok
  simp only [uncurry_apply_pair, Slice.from_val]
  iframe

/-- `slice::from_raw_parts_mut`: the cells of the range are borrowed by the slice. -/
@[step]
theorem core.slice.raw.from_raw_parts_mut.spec {T : Type} [Pointee T] [Pointee.Sized T]
    (p : MutRawPtr T) (len : Usize) (values : List T) (hLen : len.val = values.length)
    (hne : 0 < values.length) :
    ⦃ p ↦* values ⦄ core.slice.raw.from_raw_parts_mut p len
      ⦃ (s, back) => ⌜s.val.val = values⌝ ∗
        ⌜back = core.slice.raw.from_raw_parts_mut.back (Pointee.repr (T := T)) p len⌝ ∗
        p ↦† len.val ⦄ := by
  unfold core.slice.raw.from_raw_parts_mut
  apply ispec_bind (RawPtr.borrowSlice.spec p len values hLen hne)
    (entails_of_eq (sep_emp_r_eq _).symm)
  intro s
  rw [sep_assoc_eq, ispec_ipure]
  intro hs
  apply ispec_ok
  simp only [uncurry_apply_pair, hs]
  iframe

/-! ## Freeing an owned block -/

/-- Returns an owned block of one value to the allocator. Owning its cleanup and its (exclusive)
cells gives the authority to do so (see `AuthOK`); the proof is that of fournet/wip-memory-model
(`Bytes.returnView.spec`). -/
theorem RawPtr.returnOwned.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : MutRawPtr T)
    (value : T) :
    ⦃ p ↦ value ∗ p.freeable 1 ⦄
      Result.checkedModify (State.returnOwned (Pointee.repr (T := T)) p 1) ⦃ emp ⦄ := by
  have hEq : p ↦ value ∗ p.freeable 1 ⊢
      iexists fun bptr => upClose (Bytes.sep (Bytes.alloc (Pointee.repr (T := T)) p p.address 1
        true) (Bytes.pointsTo (Pointee.repr (T := T)) p bptr value)) := by
    rintro h ⟨h₁, h₂, hd, rfl, ⟨bptr, hP⟩, hF⟩
    refine ⟨bptr, sep_upClose (A := Bytes.alloc (Pointee.repr (T := T)) p p.address 1 true)
      (B := Bytes.pointsTo (Pointee.repr (T := T)) p bptr value) _
      ⟨h₂, h₁, hd.symm, Fragment.union_comm _ _, hF, hP⟩⟩
  refine ispec_conseq (ispec_exists.mpr fun bptr => ?_) hEq (fun _ => entails_refl _)
  apply ispec_checkedModify
  rintro s _ frame ⟨e, he, hse⟩ hd hm hi hAuth
  obtain ⟨rest, hrest, rfl⟩ := PartialCommMonoid.subheap_iff.mp hse
  have hdParts := Fragment.disjoint_union_left.mp hd
  have hme : Fragment.Matches s e :=
    ((Fragment.matches_union _ _ _).mp ((Fragment.matches_union _ _ _).mp hm).1).1
  have hsize := (Pointee.Sized.pos (T := T))
  -- The cells and the cleanup are in the same block: same base pointer
  obtain ⟨c, a, hca, rfl, hc, ⟨bytes, encoded, hblock⟩⟩ := he
  have hbptr : bptr = p.address := by
    have hmca := (Fragment.matches_union _ _ _).mp hme
    exact Bytes.bptr_eq_of_matches (by simpa using hsize) hc hblock hmca.1 hmca.2
  subst hbptr
  have hp' : Bytes.sep (Bytes.alloc (Pointee.repr (T := T)) p p.address 1 true)
      (Bytes.readable (Pointee.repr (T := T)) p p.address value) (c ∪ a) :=
    ⟨c, a, hca, rfl, hc, bytes, (Pointee.repr (T := T)).encode_decode _ _ encoded, hblock⟩
  obtain ⟨blk, hl, _, _, _, hown, _, hdepth, hh⟩ := Bytes.whole_readable hsize hp' hme
  -- The authority to return the block
  have hEx : AllExclusive s p.provenance := by
    intro blk' hl' i hi'
    rw [hl] at hl'
    cases hl'
    have := List.all_eq_true.mp hdepth _ (List.getElem_mem hi')
    simpa using this
  have hcl : ((c ∪ a ∪ rest) ∪ frame)
      (.cleanup p.provenance blk.repr.length blk.bptr true) := by
    left; left
    rw [hh, ← hown]
    left; rfl
  have authority := hAuth _ _ _ hcl hEx
  have hdA : (c ∪ a).Disjoint (rest ∪ frame) :=
    Fragment.disjoint_union_right.mpr ⟨hrest, hdParts.1⟩
  have hmA : Fragment.Matches s ((c ∪ a) ∪ (rest ∪ frame)) := by
    rwa [← Fragment.union_assoc]
  obtain ⟨⟨_, s₁, hrun⟩, post⟩ := Bytes.returnView.spec (Pointee.repr (T := T)) p p.address value
    true s hsize (fun _ => authority) (c ∪ a) (rest ∪ frame) hp' hdA hmA hi
  refine ⟨⟨(), s₁, by unfold State.returnOwned; simpa using hrun⟩, fun x s' hx => ?_⟩
  have hx' : Heap.returnOwned (Pointee.repr (T := T)) p 1 s = some s' := hx
  obtain ⟨a', _, hm', hi', ha'⟩ := post x s' (by simpa using hx')
  rw [ha', Fragment.empty_union] at hm'
  refine ⟨rest, hdParts.2, hm', hi', ?_, trivial⟩
  have hs' : s' = s.retire p.provenance := Heap.returnOwned_retire hx'
  intro base size bptr' hb hEx'
  rw [hs'] at hEx' ⊢
  obtain ⟨hEx₀, hRet⟩ := retire_step base hEx'
  apply hRet
  apply hAuth base size bptr' _ hEx₀
  rcases hb with hb | hb
  · exact Or.inl (Or.inr hb)
  · exact Or.inr hb

/-- `Box::from_raw`: reads the value, and returns the owned block to the allocator. -/
@[step]
theorem alloc.boxed.Box.from_raw.spec {T : Type} [Pointee T] [Pointee.Sized T] (p : MutRawPtr T)
    (value : T) :
    ⦃ p ↦ value ∗ p.freeable 1 ⦄ alloc.boxed.Box.from_raw p ⦃ b => ⌜b.val = value⌝ ⦄ := by
  unfold alloc.boxed.Box.from_raw
  apply ispec_bind (RawPtr.read.spec p value) (entails_refl _)
  intro v
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  apply ispec_bind (RawPtr.returnOwned.spec p v) (entails_of_eq (sep_emp_r_eq _).symm)
  intro _
  apply ispec_ok
  iframe

/-! ## Prefixes of readable ranges, pointer distance, and heap-level reasoning

Lemmas for the proof of `DecimalBuffer.format` (`tests/lean/RawZmijMweProofs.lean`), the formatter
of the Zmij MWE of fournet/wip-memory-model:
- `p.readable2 d₁ d₂ xs ys`: a readable range of `xs ++ ys` whose prefix `xs` is shared `d₁` times
  and whose suffix is shared `d₂` times, so that `from_raw_parts` can share a prefix of the cells of
  an `as_ptr` exposure;
- `RawPtr.add.spec_elem`: pointer arithmetic from an element of a range;
- `Slice.as_ptr.spec_at`, `Slice.as_mut_ptr.spec_at`: the exposures are at their placement;
- heap-level reasoning (`DWP`) about retired views, whose base pointer, length and allocation remain
  observable (`Heap.Retained`), and `offset_from` between a retired view and a re-exposure at the
  same address (`offset_from_reexposed`, after fournet/wip-memory-model). -/

theorem Vector.toList_flatMap' {α β : Type _} {n m : Nat} (xs : Vector α n) (f : α → Vector β m) :
    (xs.flatMap f).toList = xs.toList.flatMap (fun a => (f a).toList) := by
  rw [Vector.flatMap]; simp only [Array.toList_flatMap, Vector.toList]

theorem flatMap_shared_length {size : Nat} (l : List (Vector Byte size)) (d : Nat) :
    (l.flatMap (fun b => (b.map (Cell.shared d)).toList)).length = l.length * size := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, Vector.toList_map, List.length_map,
      Vector.length_toList, List.length_cons, Nat.succ_mul] at ih ⊢
    omega

/-- A readable range of `xs ++ ys` is a readable range of `xs` and a readable range of `ys` after
it, in the same block. -/
theorem readableRange_append {T : Type} (repr : Repr T) (p q : RawPtr T) (bptr : BasePtr)
    (xs ys : List T) (d : Nat) (hprov : q.provenance = p.provenance)
    (hoff : q.address.val = p.address.val + xs.length * repr.size) (h : Fragment) :
    readableRange repr p bptr (listVec (xs ++ ys)) d h ↔
      (readableRange repr p bptr (listVec xs) d ∗ᵇ readableRange repr q bptr (listVec ys) d) h := by
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
    · have := dec ⟨i.val, by simp; omega⟩
      have e₁ : data₁[i.val] = data[i.val] := by
        simp only [data₁, Vector.getElem_mk, List.getElem_toArray, List.getElem_take]
        rfl
      simp only [listVec, Vector.getElem_mk, List.getElem_toArray] at this ⊢
      rw [e₁, this, List.getElem_append_left]
    · have := dec ⟨xs.length + i.val, by simp⟩
      have e₂ : data₂[i.val] = data[xs.length + i.val] := by
        simp only [data₂, Vector.getElem_mk, List.getElem_toArray, List.getElem_drop]
        rfl
      simp only [listVec, Vector.getElem_mk, List.getElem_toArray] at this ⊢
      rw [e₂, this, List.getElem_append_right (by omega)]
      simp
  · rintro ⟨a, b, hab, rfl, ⟨data₁, dec₁, ha⟩, ⟨data₂, dec₂, hb⟩⟩
    let data : Vector (Vector Byte repr.size) (xs ++ ys).length :=
      ⟨(data₁.toList ++ data₂.toList).toArray, by simp⟩
    have h₀ : data.toList = data₁.toList ++ data₂.toList := by simp [data, Vector.toList]
    refine ⟨data, fun i => ?_, ?_⟩
    · by_cases hi : i.val < xs.length
      · have := dec₁ ⟨i.val, hi⟩
        have e : data[i.val] = data₁[i.val] := by
          simp only [data, Vector.getElem_mk, List.getElem_toArray]
          rw [List.getElem_append_left (by simpa using hi)]
          simp
        simp only [listVec, Vector.getElem_mk, List.getElem_toArray] at this ⊢
        rw [e, this, List.getElem_append_left]
      · have hi' : i.val - xs.length < ys.length := by have := i.isLt; simp at this; omega
        have := dec₂ ⟨i.val - xs.length, hi'⟩
        have e : data[i.val] = data₂[i.val - xs.length] := by
          simp only [data, Vector.getElem_mk, List.getElem_toArray]
          rw [List.getElem_append_right (by simpa using hi)]
          simp
        simp only [listVec, Vector.getElem_mk, List.getElem_toArray] at this ⊢
        rw [e, this, List.getElem_append_right (by omega)]
    · have hsplit : (data.flatMap (fun b => b.map (Cell.shared d))).toList =
          (data₁.flatMap (fun b => b.map (Cell.shared d))).toList ++
            (data₂.flatMap (fun b => b.map (Cell.shared d))).toList := by
        rw [hcells, hcells, hcells, h₀, List.flatMap_append]
      rw [hsplit]
      exact (Bytes.block_append repr p q bptr _ _ hprov
        (by rw [hoff, hcells, flatMap_shared_length]; simp)
        (by rw [hcells, flatMap_shared_length]; exact Repr.aligned_stride repr _) _).mpr
        ⟨a, b, hab, rfl, ha, hb⟩

/-! ### Sharing a prefix of a readable range -/

theorem Bytes.shareRange.local_readable {T : Type} (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Bytes.LocalOp (readableRange repr p bptr values depth) (State.shareRange repr p count)
      (fun result h => result = values.toList ∧
        readableRange repr p bptr values (depth + 1) h) := by
  intro h F s hp hd hm hi
  have hr := Bytes.read_of_readableRange hcount hsize hp ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨data, decoded, hb⟩ := hp
  obtain ⟨⟨_, s₁, hc⟩, hpost⟩ :=
    Bytes.shareRange_cells.spec repr p bptr data depth hcount hsize h F s hb hd hm hi
  refine ⟨⟨values.toList, s₁, hr, hc⟩, ?_⟩
  rintro result s' ⟨hv, hc'⟩
  obtain ⟨h', hd', hm', hi', hq⟩ := hpost () s' hc'
  exact ⟨h', hd', hm', hi', Option.some.inj (hv.symm.trans hr), data, decoded, hq⟩

theorem Bytes.endShareRange.local_readable {T : Type} (repr : Repr T) (p : RawPtr T)
    (bptr : BasePtr) (values : Vector T count) (depth : Nat) (positive : 0 < depth)
    (hcount : 0 < count) (hsize : 0 < repr.size) :
    Bytes.LocalOp (readableRange repr p bptr values (depth + 1))
      (State.endShareRange repr p values.toList)
      (fun _ => readableRange repr p bptr values depth) := by
  intro h F s hp hd hm hi
  have hr := Bytes.read_of_readableRange hcount hsize hp ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨data, decoded, hp⟩ := hp
  obtain ⟨⟨_, s₁, hc⟩, hpost⟩ :=
    Bytes.endShareRange_cells.spec repr p bptr data depth positive hcount hsize h F s hp hd hm hi
  refine ⟨⟨(), s₁, by simpa using hr, by simpa using hc⟩, ?_⟩
  rintro _ s' ⟨_, he⟩
  obtain ⟨h', hd', hm', hi', hq⟩ := hpost () s' (by simpa using he)
  exact ⟨h', hd', hm', hi', data, decoded, hq⟩

/-- A readable range of `xs`, shared `d₁` times, followed by a readable range of `ys`, shared
`d₂` times, in the same block. -/
def RawPtr.readable2 {T : Type} [Pointee T] (p : RawPtr T) (d₁ d₂ : Nat) (xs ys : List T) :
    IProp :=
  iexists fun bptr : BasePtr => upClose (fun h =>
    p.address.val + xs.length * (Pointee.repr (T := T)).size < 2 ^ UScalarTy.numBits .Usize ∧
    (readableRange (Pointee.repr (T := T)) p bptr (listVec xs) d₁ ∗ᵇ
      readableRange (Pointee.repr (T := T)) (p.elem xs.length) bptr (listVec ys) d₂) h)

theorem RawPtr.readable_split {T : Type} [Pointee T] (p : RawPtr T) (d : Nat) (xs ys : List T)
    (hfit : p.address.val + xs.length * (Pointee.repr (T := T)).size <
      2 ^ UScalarTy.numBits .Usize) :
    p.readable d (xs ++ ys) ⊢ p.readable2 d d xs ys := by
  rintro h ⟨bptr, a, ha, hsub⟩
  exact ⟨bptr, a, ⟨hfit, (readableRange_append _ p (p.elem xs.length) bptr xs ys d
    (RawPtr.elem_provenance p _) (RawPtr.elem_address p _ hfit) a).mp ha⟩, hsub⟩

theorem RawPtr.readable2_merge {T : Type} [Pointee T] (p : RawPtr T) (d : Nat) (xs ys : List T) :
    p.readable2 d d xs ys ⊢ p.readable d (xs ++ ys) := by
  rintro h ⟨bptr, a, ⟨hfit, ha⟩, hsub⟩
  exact ⟨bptr, a, (readableRange_append _ p (p.elem xs.length) bptr xs ys d
    (RawPtr.elem_provenance p _) (RawPtr.elem_address p _ hfit) a).mpr ha, hsub⟩

theorem RawPtr.shareRange.spec_readable2 {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (d₁ d₂ : Nat) (xs ys : List T) (hne : 0 < xs.length) :
    ⦃ p.readable2 d₁ d₂ xs ys ⦄ RawPtr.shareRange (Pointee.repr (T := T)) p xs.length
      ⦃ result => ⌜result = xs⌝ ∗ p.readable2 (d₁ + 1) d₂ xs ys ⦄ := by
  refine ispec_conseq (ispec_checked_local
      (A := fun bptr h =>
        p.address.val + xs.length * (Pointee.repr (T := T)).size < 2 ^ UScalarTy.numBits .Usize ∧
        (readableRange (Pointee.repr (T := T)) p bptr (listVec xs) d₁ ∗ᵇ
          readableRange (Pointee.repr (T := T)) (p.elem xs.length) bptr (listVec ys) d₂) h)
      (B := fun bptr result h => result = xs ∧
        p.address.val + xs.length * (Pointee.repr (T := T)).size < 2 ^ UScalarTy.numBits .Usize ∧
        (readableRange (Pointee.repr (T := T)) p bptr (listVec xs) (d₁ + 1) ∗ᵇ
          readableRange (Pointee.repr (T := T)) (p.elem xs.length) bptr (listVec ys) d₂) h)
      (fun bptr => ?_) (fun bptr => ?_)) (entails_refl _) (fun _ => ?_)
  · apply Bytes.LocalOp.pure_pre
    intro hfit
    refine Bytes.LocalOp.conseq (fun _ h => h) ?_
      (Bytes.LocalOp.frame (Bytes.shareRange.local_readable _ p bptr (listVec xs) d₁ hne
        Pointee.Sized.pos))
    rintro x _ ⟨a, b, hab, rfl, ⟨hx, ha⟩, hb⟩
    exact ⟨by simpa using hx, hfit, a, b, hab, rfl, ha, hb⟩
  · refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.sep (fun _ ha => NoOwned.readableRange ha)
      (fun _ hb => NoOwned.readableRange hb) h.2.2) ?_
    rintro a F s _ _ _ _ x s' hx a' _ hm' _ ⟨_, _, a₁, b₁, _, rfl, ⟨data, _, hblock⟩, _⟩ base hEx _
    have hlen :
        0 < (data.flatMap (fun bytes => bytes.map (Cell.shared (d₁ + 1)))).toList.length := by
      simp; exact ⟨hne, Pointee.Sized.pos⟩
    have run := hx.2
    unfold Heap.shareRange Heap.modifyRange at run
    exact modify_step_nonExclusive run ((Fragment.matches_union _ _ _).mp hm').1
      (Or.inl (Bytes.block_cell hblock hlen)) (by rw [flatMap_shared_getElem_depth]; simp) base hEx
  · rintro h ⟨bptr, a, ⟨hx, hA⟩, hsub⟩
    exact (sep_pure_l _ _ h).mpr ⟨hx, bptr, a, hA, hsub⟩

theorem RawPtr.endShareRange.spec_readable2 {T : Type} [Pointee T] [Pointee.Sized T]
    (p : RawPtr T) (d₁ d₂ : Nat) (xs ys : List T) (positive : 0 < d₁) (hne : 0 < xs.length) :
    ⦃ p.readable2 (d₁ + 1) d₂ xs ys ⦄ RawPtr.endShareRange (Pointee.repr (T := T)) p xs
      ⦃ p.readable2 d₁ d₂ xs ys ⦄ := by
  have h := ispec_checked_local
      (A := fun bptr h =>
        p.address.val + xs.length * (Pointee.repr (T := T)).size < 2 ^ UScalarTy.numBits .Usize ∧
        (readableRange (Pointee.repr (T := T)) p bptr (listVec xs) (d₁ + 1) ∗ᵇ
          readableRange (Pointee.repr (T := T)) (p.elem xs.length) bptr (listVec ys) d₂) h)
      (B := fun bptr (_ : Unit) h =>
        p.address.val + xs.length * (Pointee.repr (T := T)).size < 2 ^ UScalarTy.numBits .Usize ∧
        (readableRange (Pointee.repr (T := T)) p bptr (listVec xs) d₁ ∗ᵇ
          readableRange (Pointee.repr (T := T)) (p.elem xs.length) bptr (listVec ys) d₂) h)
      (modify := State.endShareRange (Pointee.repr (T := T)) p xs)
      (fun bptr => ?_) (fun bptr => ?_)
  · exact h
  · apply Bytes.LocalOp.pure_pre
    intro hfit
    have hl := Bytes.LocalOp.frame (R := readableRange (Pointee.repr (T := T)) (p.elem xs.length)
      bptr (listVec ys) d₂) (Bytes.endShareRange.local_readable _ p bptr (listVec xs) d₁ positive
        hne Pointee.Sized.pos)
    simp only [listVec_toList] at hl
    exact Bytes.LocalOp.conseq (fun _ h => h) (fun _ _ h => ⟨hfit, h⟩) hl
  · refine Bytes.AuthPres.of_step (fun _ _ h => NoOwned.sep (fun _ ha => NoOwned.readableRange ha)
      (fun _ hb => NoOwned.readableRange hb) h.2) ?_
    rintro a F s _ _ _ _ x s' hx a' _ hm' _ ⟨_, a₁, b₁, _, rfl, ⟨data, _, hblock⟩, _⟩ base hEx _
    have hlen : 0 < (data.flatMap (fun bytes => bytes.map (Cell.shared d₁))).toList.length := by
      simp; exact ⟨hne, Pointee.Sized.pos⟩
    have run := hx.2
    unfold Heap.endShareRange Heap.modifyRange at run
    exact modify_step_nonExclusive run ((Fragment.matches_union _ _ _).mp hm').1
      (Or.inl (Bytes.block_cell hblock hlen)) (by rw [flatMap_shared_getElem_depth]; simp; omega)
      base hEx

/-- `slice::from_raw_parts` on a prefix of a readable range. -/
theorem core.slice.raw.from_raw_parts.spec_readable2 {T : Type} [Pointee T] [Pointee.Sized T]
    (p : ConstRawPtr T) (len : Usize) (d₁ d₂ : Nat) (xs ys : List T)
    (hLen : len.val = xs.length) (hne : 0 < xs.length) :
    ⦃ p.readable2 d₁ d₂ xs ys ⦄ core.slice.raw.from_raw_parts p len
      ⦃ (s, back) => ⌜s.val.val = xs⌝ ∗
        ⌜back = RawPtr.endShareRange (Pointee.repr (T := T)) p xs⌝ ∗
        p.readable2 (d₁ + 1) d₂ xs ys ⦄ := by
  unfold core.slice.raw.from_raw_parts
  rw [hLen]
  apply ispec_bind (RawPtr.shareRange.spec_readable2 p d₁ d₂ xs ys hne)
    (entails_of_eq (sep_emp_r_eq _).symm)
  intro vs
  rw [sep_assoc_eq, ispec_ipure]
  rintro rfl
  have hMax : vs.length ≤ Usize.max := by rw [← hLen]; scalar_tac
  simp only [hMax, dite_true]
  apply ispec_ok
  simp only [uncurry_apply_pair, Slice.from_val]
  iframe


section HeapLevel

universe u

open Aeneas.Data.Coinductive

unseal Result

/-! ### Heap-level facts about checked and allocating effects -/

theorem _root_.Aeneas.Data.Coinductive.DWP.fail_iff {α : Type} {e : Error} {Q : effectWP.Post α}
    {s : Heap} :
    DWP effectWP (Result.fail e : Result α) Q s ↔ e = .oom := by
  simp only [Result.fail, Result.vis]
  exact ⟨fun h => h.vis_view, fun h => DWP.vis h⟩

/-- The results of a checked effect come with a successor of its relation. -/
theorem _root_.Aeneas.Data.Coinductive.DWP.checkedModify_rel {α : Type} {R : Heap → α → Heap → Prop}
    {Q : effectWP.Post α} {s : Heap} (h : DWP effectWP (Result.checkedModify R) Q s) :
    DWP effectWP (Result.checkedModify R) (fun x s' => Q x s' ∧ R s x s') s := by
  unfold Result.checkedModify Result.vis at *
  obtain ⟨hen, hall⟩ := h.vis_view
  refine DWP.vis ⟨hen, fun x s' hx => ?_⟩
  have hk := hall x s' hx
  cases x with
  | none => exact DWP.fail_iff.mpr (DWP.fail_iff.mp hk)
  | some v =>
    simp only [Result.ofOption, Result.ok] at hk ⊢
    exact DWP.ret_iff.mpr ⟨DWP.ret_iff.mp hk, hx⟩

/-- The results of an allocating effect come with a successor of its relation. -/
theorem _root_.Aeneas.Data.Coinductive.DWP.allocatingModify_rel {α : Type}
    {R : Heap → α → Heap → Prop} {Q : effectWP.Post α} {s : Heap}
    (h : DWP effectWP (Result.allocatingModify R) Q s) :
    DWP effectWP (Result.allocatingModify R) (fun x s' => Q x s' ∧ R s x s') s := by
  unfold Result.allocatingModify Result.vis at *
  obtain ⟨hen, hall⟩ := h.vis_view
  refine DWP.vis ⟨hen, fun x s' hx => ?_⟩
  have hk := hall x s' hx
  cases x with
  | none => exact DWP.fail_iff.mpr (DWP.fail_iff.mp hk)
  | some v =>
    simp only [Result.ofOption, Result.ok] at hk ⊢
    exact DWP.ret_iff.mpr ⟨DWP.ret_iff.mp hk, hx⟩

/-- A checked effect which is enabled, and whose successors all satisfy `Q`. -/
theorem _root_.Aeneas.Data.Coinductive.DWP.checkedModify_intro {α : Type}
    {R : Heap → α → Heap → Prop} {Q : effectWP.Post α} {s : Heap} (hen : ∃ x s', R s x s')
    (hpost : ∀ x s', R s x s' → Q x s') :
    DWP effectWP (Result.checkedModify R) Q s := by
  unfold Result.checkedModify Result.vis
  obtain ⟨x₀, s₀, h₀⟩ := hen
  refine DWP.vis ⟨⟨some x₀, s₀, h₀⟩, fun x s' hx => ?_⟩
  cases x with
  | none => exact (hx.1 ⟨x₀, s₀, h₀⟩).elim
  | some v =>
    simp only [Result.ofOption, Result.ok]
    exact DWP.ret_iff.mpr (hpost v s' hx)

/-- An allocation returns a result of its relation. -/
theorem ispec_allocatingModify_rel {α : Type} {P : IPre} {R : Heap → α → Heap → Prop}
    {Q : IPost α} (h : ispec P (Result.allocatingModify R) Q) :
    ispec P (Result.allocatingModify R) (fun x => ⌜∃ s s', R s x s'⌝ ∗ Q x) := by
  rw [ispec_iff] at h ⊢
  intro F s hR
  refine (DWP.allocatingModify_rel (h F s hR)).mono ?_
  rintro x s' ⟨hQ, hx⟩
  exact Realizes.mono (sep_mono (pure_sep_intro _ ⟨s, s', hx⟩) (entails_refl F)) hQ

/-! ### Exposures in realized assertions -/

theorem WP.Realizes.pure_sep {P : Prop} {H F : IProp} {s : Heap} :
    Realizes ((⌜P⌝ ∗ H) ∗ F) s ↔ P ∧ Realizes (H ∗ F) s := by
  rw [sep_assoc_eq]
  constructor
  · rintro ⟨hi, h, hh, hm, ha⟩
    obtain ⟨hP, hh⟩ := (sep_pure_l _ _ h).mp hh
    exact ⟨hP, hi, h, hh, hm, ha⟩
  · rintro ⟨hP, hi, h, hh, hm, ha⟩
    exact ⟨hi, h, (sep_pure_l _ _ h).mpr ⟨hP, hh⟩, hm, ha⟩

/-- The block of an exposure. -/
theorem WP.Realizes.exposure_block {T : Type} [Pointee T] {p : RawPtr T} {n : Nat} {R : IProp}
    {s : Heap} (h : Realizes (p.exposure n ∗ R) s) :
    ∃ blk, s.allocations p.provenance = some blk ∧
      blk.repr.length = n * (Pointee.repr (T := T)).size ∧ s.live blk = true ∧
      blk.bptr = p.address ∧ blk.owned = false := by
  obtain ⟨_, h, ⟨h₁, h₂, _, rfl, ⟨a, ⟨_, rfl⟩, hsub⟩, _⟩, hm, _⟩ := h
  obtain ⟨rest, _, rfl⟩ := PartialCommMonoid.subheap_iff.mp hsub
  exact hm _ (Or.inl (Or.inl rfl))

/-- An exposure lies in the address space. -/
theorem WP.Realizes.exposure_fit {T : Type} [Pointee T] {p : RawPtr T} {n : Nat} {R : IProp}
    {s : Heap} (h : Realizes (p.exposure n ∗ R) s) :
    p.address.val + n * (Pointee.repr (T := T)).size < 2 ^ UScalarTy.numBits .Usize := by
  obtain ⟨blk, hl, hlen, -, hb, -⟩ := Realizes.exposure_block h
  have hv := h.1.validBlock hl
  simp only [Heap.validBlock, Bool.and_eq_true, Heap.bounded, decide_eq_true_eq] at hv
  rw [← hb, ← hlen]
  exact hv.1.1.2

theorem ispec_exposure_fit {α : Type u} {T : Type} [Pointee T] {p : RawPtr T} {n : Nat}
    {P R : IPre} {m : Result α} {Q : IPost α} (hP : P ⊢ p.exposure n ∗ R)
    (h : p.address.val + n * (Pointee.repr (T := T)).size < 2 ^ UScalarTy.numBits .Usize →
      ispec P m Q) :
    ispec P m Q := by
  rw [ispec_iff]
  intro F s hR
  have hfit := Realizes.exposure_fit
    (Realizes.mono (entails_trans (sep_mono hP (entails_refl F))
      (entails_of_eq (sep_assoc_eq _ _ _))) hR)
  exact ispec_iff.mp (h hfit) F s hR

/-! ### Exposures at their placement -/

/-- `as_mut_ptr` exposes the slice at the address of its placement. -/
theorem Slice.as_mut_ptr.spec_at {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.Calibrated T]
    (address : BasePtr) (s : MutBorrow (Slice T)) (hne : 0 < s.val.length) :
    ⦃ emp ⦄ Slice.as_mut_ptr address s
      ⦃ (p, back) => ⌜p.address = address⌝ ∗
        ⌜back = Slice.end_as_mut_ptr (Pointee.repr (T := T)) s.val p⌝ ∗
        p ↦* s.val.val ∗ p.exposure s.val.length ⦄ := by
  rw [Slice.as_mut_ptr_eq]
  apply ispec_bind (ispec_allocatingModify_rel
    (R := State.exposeAt (Pointee.repr (T := T)) s.val.val address)
    (RawPtr.allocExposure.spec s.val.val address hne)) (entails_of_eq (sep_emp_r_eq emp).symm)
  intro p
  rw [sep_assoc_eq, ispec_ipure]
  rintro ⟨_, _, hx⟩
  have := State.exposeAt_address hx
  apply ispec_ok
  simp only [uncurry_apply_pair]
  iframe

/-- `as_ptr` exposes the slice at the address of its placement. -/
theorem Slice.as_ptr.spec_at {T : Type} [Pointee T] [Pointee.Sized T] (address : BasePtr)
    (s : SharedBorrow (Slice T)) (hne : 0 < s.val.length) :
    ⦃ emp ⦄ Slice.as_ptr address s
      ⦃ (p, back) => ⌜p.address = address⌝ ∗
        ⌜back = Slice.end_as_ptr (Pointee.repr (T := T)) s.val p⌝ ∗
        p.readable 1 s.val.val ∗ p.exposure s.val.length ⦄ := by
  rw [Slice.as_ptr_eq]
  apply ispec_bind (ispec_allocatingModify_rel
    (R := State.sharedExposeAt (Pointee.repr (T := T)) s.val.val address)
    (RawPtr.allocSharedExposure.spec s.val.val address hne))
    (entails_of_eq (sep_emp_r_eq emp).symm)
  intro p
  rw [sep_assoc_eq, ispec_ipure]
  rintro ⟨_, _, hx⟩
  have := State.sharedExposeAt_address hx
  apply ispec_ok
  simp only [uncurry_apply_pair]
  iframe

/-! ### Pointer arithmetic from an element of a range -/

theorem Bytes.add.local_elem {T : Type} [Pointee T] (p : RawPtr T) (base : BasePtr)
    (values : Vector T count) (depth : Nat) (j : Nat) (i : Usize) (hcount : 0 < count)
    (hsize : 0 < (Pointee.repr (T := T)).size) (hle : j + i.val ≤ count) (P : Fragment → Prop)
    (view : ∀ h, P h → readableRange (Pointee.repr (T := T)) p base values depth h) :
    Bytes.LocalOp P (State.offset (Pointee.repr (T := T)) (p.elem j) i.val)
      (fun result h => result = p.elem (j + i.val) ∧ P h) := by
  intro h F s hP hd hm hi
  have keep := hP
  have hp := view h hP
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have bound := readableRange_bound _ p base values depth hcount hsize h s hp localMatch hi
  have hmul := Nat.mul_le_mul_right (Pointee.repr (T := T)).size hle
  rw [Nat.add_mul] at hmul
  have hqaddr : (p.elem j).address.val = p.address.val + j * (Pointee.repr (T := T)).size :=
    RawPtr.elem_address p j (by omega)
  have hfit : (p.elem j).address.val + i.val * (Pointee.repr (T := T)).size <
      2 ^ UScalarTy.numBits .Usize := by omega
  obtain ⟨data, _, hlo, _, cells⟩ := hp
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
  have hlo' : (base.val : Int) ≤ ((p.elem j).address.val : Int) +
      i.val * (Pointee.repr (T := T)).size := by omega
  have hhi' : ((p.elem j).address.val : Int) + i.val * (Pointee.repr (T := T)).size ≤
      base.val + blk.repr.length := by omega
  have hfit' : ((p.elem j).address.val : Int) + i.val * (Pointee.repr (T := T)).size <
      (2 ^ UScalarTy.numBits .Usize : Nat) := by exact_mod_cast hfit
  let result : RawPtr T := ⟨(p.elem j).provenance,
    ⟨BitVec.ofNat _ ((p.elem j).address.val + i.val * (Pointee.repr (T := T)).size)⟩⟩
  have hrun : Heap.offset (Pointee.repr (T := T)) (p.elem j) i.val s = some result := by
    have hf : ((p.elem j).address.val : Int) + i.val * (Pointee.repr (T := T)).size <
        (2 : Int) ^ System.Platform.numBits := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, UScalarTy.Usize_numBits_eq] using hfit'
    have target_nat : (((p.elem j).address.val : Int) +
        i.val * (Pointee.repr (T := T)).size).toNat =
        (p.elem j).address.val + i.val * (Pointee.repr (T := T)).size := by
      exact_mod_cast Int.toNat_natCast _
    simp [Heap.offset, hl, hlive, hbase, hqlo, hstart, hlo', hhi', hf, target_nat, result]
  refine ⟨⟨result, s, hrun, rfl⟩, ?_⟩
  rintro answer s' ⟨he, rfl⟩
  have he := Option.some.inj (he.symm.trans hrun)
  subst answer
  refine ⟨h, hd, hm, hi, RawPtr.eq_elem rfl ?_, keep⟩
  change (BitVec.ofNat _ _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, hqaddr, Nat.add_mul, Nat.add_assoc]

/-- Pointer arithmetic from the `j`-th element of a range, within the range or one past it. -/
theorem RawPtr.add.spec_elem {T : Type} [Pointee T] [Pointee.Sized T] (p : RawPtr T)
    (values : List T) (j : Nat) (count : Usize) (hne : 0 < values.length)
    (hle : j + count.val ≤ values.length) :
    ⦃ p ↦* values ⦄ RawPtr.add (p.elem j) count
      ⦃ result => ⌜result = p.elem (j + count.val)⌝ ∗ p ↦* values ⦄ :=
  ispec_conseq (ispec_checked_local
      (fun bptr => Bytes.add.local_elem p bptr (listVec values) 0 j count hne Pointee.Sized.pos hle
        _ (fun _ hp => pointsToRange_readable hp))
      (fun _ => Bytes.AuthPres.of_eq (fun _ _ h => NoOwned.pointsToRange h.2)
        (fun _ _ _ h => h.2)))
    (entails_refl _) (fun _ => iexists_upClose_pure_and)

/-! ### Retained views and pointer distance -/

/-- The view `id` is retained, possibly retired, with its base pointer, its length and a live
allocation. -/
def Heap.Retained (s : Heap) (id : Nat) (bptr : BasePtr) (len : Nat) : Prop :=
  ∃ blk, s.allocations id = some blk ∧ blk.bptr = bptr ∧ blk.repr.length = len ∧
    s.allocationAlive blk = true

theorem Heap.Retained.of_extends {s s' : Heap} {id : Nat} {bptr : BasePtr} {len : Nat}
    (hext : ∀ j, s.allocations j ≠ none → s'.allocations j = s.allocations j)
    (h : Heap.Retained s id bptr len) : Heap.Retained s' id bptr len := by
  obtain ⟨blk, hl, hb, hlen, halive⟩ := h
  refine ⟨blk, by rw [hext id (by simp [hl]), hl], hb, hlen, ?_⟩
  simp only [Heap.allocationAlive] at halive ⊢
  cases hr : s.allocations blk.root with
  | none => simp [hr] at halive
  | some r => rw [hext _ (by simp [hr]), hr]; simpa [hr] using halive

theorem Heap.Retained.retire {s : Heap} {id id' : Nat} {bptr : BasePtr} {len : Nat}
    (h : Heap.Retained s id bptr len) : Heap.Retained (s.retire id') id bptr len := by
  obtain ⟨blk, hl, hb, hlen, halive⟩ := h
  by_cases hid : id = id'
  · subst hid
    refine ⟨{ blk with active := false }, by simp [Heap.retire, update, hl], hb, hlen, ?_⟩
    simp only [Heap.allocationAlive] at halive ⊢
    by_cases hr : blk.root = id
    · simp [Heap.retire, update, hr] at halive ⊢; simpa [hl] using halive
    · simpa [Heap.retire, update, hr] using halive
  · refine ⟨blk, by simp [Heap.retire, update, hid, hl], hb, hlen, ?_⟩
    simp only [Heap.allocationAlive] at halive ⊢
    by_cases hr : blk.root = id'
    · subst hr
      cases hr' : s.allocations blk.root with
      | none => simp [hr'] at halive
      | some r => simp [Heap.retire, update, hr'] at halive ⊢; exact halive
    · simpa [Heap.retire, update, hr] using halive

theorem Heap.createRepr_allocations {s s' : Heap} {block : Block} {id : Nat}
    (h : s.createRepr block = some (id, s')) :
    ∀ j, s.allocations j ≠ none → s'.allocations j = s.allocations j := by
  intro j hj
  unfold Heap.createRepr at h
  split at h
  · rename_i hnext
    simp only [Heap.commit] at h
    split at h
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have : j ≠ s.next := by rintro rfl; exact hj hnext
      simp [update, this]
    · simp at h
  · simp at h

theorem State.sharedExposeAt_allocations {T : Type} {repr : Repr T} {values : List T}
    {address : BasePtr} {s s' : Heap} {p : RawPtr T}
    (h : State.sharedExposeAt repr values address s p s') :
    ∀ j, s.allocations j ≠ none → s'.allocations j = s.allocations j := by
  obtain ⟨data, root, -, hnew⟩ := h
  unfold Heap.newSharedExposure at hnew
  split_ifs at hnew
  obtain ⟨⟨_, _⟩, hrun, he⟩ := Option.map_eq_some_iff.mp hnew
  cases he
  exact Heap.createRepr_allocations hrun

/-- Overlapping views of live allocations have the same root (from fournet/wip-memory-model). -/
theorem Heap.Inv.same_root_of_overlap {s : Heap} (hi : s.Inv)
    {i j : Nat} {a b : Block} (ha : s.allocations i = some a)
    (hb : s.allocations j = some b)
    (aliveA : s.allocationAlive a = true) (aliveB : s.allocationAlive b = true)
    (overlap : a.bptr.val < b.bptr.val + b.repr.length ∧
      b.bptr.val < a.bptr.val + a.repr.length) :
    a.root = b.root := by
  have va := hi.validBlock ha
  have vb := hi.validBlock hb
  cases hra : s.allocations a.root
  · simp [Heap.allocationAlive, hra] at aliveA
  · rename_i ra
    cases hrb : s.allocations b.root
    · simp [Heap.allocationAlive, hrb] at aliveB
    · rename_i rb
      have ar : ra.alive = true := by simpa [Heap.allocationAlive, hra] using aliveA
      have br : rb.alive = true := by simpa [Heap.allocationAlive, hrb] using aliveB
      simp only [Heap.validBlock, hra, hrb, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at va vb
      by_contra different
      have row := List.all_eq_true.mp hi.2 a.root (List.mem_range.mpr (hi.base_lt hra))
      simp only [hra, Bool.and_eq_true] at row
      have pair := List.all_eq_true.mp row.2 b.root (List.mem_range.mpr (hi.base_lt hrb))
      simp [different, hrb, ar, br, Heap.overlaps] at pair
      grind

/-- The distance between a pointer into a retained view and the start of a live view at the same
address, in the same allocation (after `offset_from_reexposed.spec` of
fournet/wip-memory-model). -/
theorem offset_from_reexposed {finish origin : RawPtr U8} {count : Nat} {s : Heap}
    {a b : Block} {Q : effectWP.Post Isize} (hi : s.Inv)
    (ha : s.allocations finish.provenance = some a)
    (hb : s.allocations origin.provenance = some b)
    (la : s.allocationAlive a = true) (lb : s.allocationAlive b = true)
    (originBase : origin.address = b.bptr) (sameBase : a.bptr = b.bptr)
    (nonemptyA : 0 < a.repr.length) (nonemptyB : 0 < b.repr.length)
    (cursor : finish.address.val = a.bptr.val + count)
    (within : count ≤ a.repr.length) (fits : (count : Int) ≤ IScalar.cMax .Isize)
    (hQ : ∀ r : Isize, r.val = count → Q r s) :
    DWP effectWP (MutRawPtr.offset_from finish origin) Q s := by
  have overlap : a.bptr.val < b.bptr.val + b.repr.length ∧
      b.bptr.val < a.bptr.val + a.repr.length := by
    rw [sameBase]; omega
  have root := hi.same_root_of_overlap ha hb la lb overlap
  have hsize : (Pointee.repr (T := U8)).size = 1 := rfl
  have distance : (finish.address.val : Int) - origin.address.val = count := by
    rw [cursor, originBase, sameBase]; push_cast; ring
  have lower : IScalar.cMin .Isize ≤ (count : Int) :=
    le_trans (by decide : IScalar.cMin .Isize ≤ 0) (Int.natCast_nonneg count)
  have countFit : IScalar.cMin .Isize ≤ ((finish.address.val : Int) - origin.address.val) /
      ((Pointee.repr (T := U8)).size : Int) ∧
      ((finish.address.val : Int) - origin.address.val) / ((Pointee.repr (T := U8)).size : Int) ≤
        IScalar.cMax .Isize := by
    rw [distance, hsize]; simp only [Nat.cast_one, Int.ediv_one]; exact ⟨lower, fits⟩
  let result := IScalar.ofInt (((finish.address.val : Int) - origin.address.val) /
    ((Pointee.repr (T := U8)).size : Int)) countFit
  have run : Heap.offsetFrom (Pointee.repr (T := U8)) finish origin s = some result := by
    have h1 : a.bptr.val ≤ finish.address.val := by omega
    have h2 : finish.address.val ≤ a.bptr.val + a.repr.length := by omega
    have h3 : b.bptr.val ≤ origin.address.val := by rw [originBase]
    have h4 : origin.address.val ≤ b.bptr.val + b.repr.length := by rw [originBase]; omega
    have hdist : (finish.address.val : Int) - origin.address.val = count := distance
    simp only [Heap.offsetFrom, Heap.distance, ha, hb, la, lb, root, hsize, h1, h2, h3, h4,
      hdist, Option.bind_eq_bind, Option.bind_some, beq_self_eq_true, Bool.true_and,
      Nat.cast_one, Int.emod_one, Int.ediv_one, decide_true, zero_lt_one]
    simp [lower, fits, result, hdist, hsize]
  unfold MutRawPtr.offset_from RawPtr.offset_from
  refine DWP.checkedModify_intro ⟨result, s, run, rfl⟩ ?_
  rintro r s' ⟨hr, rfl⟩
  have := Option.some.inj (hr.symm.trans run)
  subst this
  exact hQ _ (by simp [result, distance, hsize])


/-- Running a step whose separation-logic specification is known, in a heap which realizes its
precondition with the frame `F`. -/
theorem _root_.Aeneas.Data.Coinductive.DWP.bind_ispec {α : Type} {β : Type u} {P : IPre}
    {m : Result α} {Q : IPost α} {k : α → Result β}
    {F : IProp} {s : Heap} {Q₂ : effectWP.Post β}
    (hspec : ispec P m Q) (hR : Realizes (P ∗ F) s)
    (hk : ∀ x s', Realizes (Q x ∗ F) s' → DWP effectWP (k x) Q₂ s') :
    DWP effectWP (Aeneas.Std.bind m k) Q₂ s :=
  DWP.bind (ispec_iff.mp hspec F s hR) hk

/-- `DWP.bind_ispec` for a checked effect, whose results also come with a successor of its
relation. -/
theorem _root_.Aeneas.Data.Coinductive.DWP.bind_ispec_checked {α : Type} {β : Type u} {P : IPre}
    {R : Heap → α → Heap → Prop} {Q : IPost α}
    {k : α → Result β} {F : IProp} {s : Heap} {Q₂ : effectWP.Post β}
    (hspec : ispec P (Result.checkedModify R) Q) (hR : Realizes (P ∗ F) s)
    (hk : ∀ x s', Realizes (Q x ∗ F) s' → R s x s' → DWP effectWP (k x) Q₂ s') :
    DWP effectWP (Aeneas.Std.bind (Result.checkedModify R) k) Q₂ s :=
  DWP.bind (DWP.checkedModify_rel (ispec_iff.mp hspec F s hR)) fun x s' h => hk x s' h.1 h.2

/-- `DWP.bind_ispec` for an allocating effect, whose results also come with a successor of its
relation. -/
theorem _root_.Aeneas.Data.Coinductive.DWP.bind_ispec_allocating {α : Type} {β : Type u}
    {P : IPre} {R : Heap → α → Heap → Prop}
    {Q : IPost α} {k : α → Result β} {F : IProp} {s : Heap} {Q₂ : effectWP.Post β}
    (hspec : ispec P (Result.allocatingModify R) Q) (hR : Realizes (P ∗ F) s)
    (hk : ∀ x s', Realizes (Q x ∗ F) s' → R s x s' → DWP effectWP (k x) Q₂ s') :
    DWP effectWP (Aeneas.Std.bind (Result.allocatingModify R) k) Q₂ s :=
  DWP.bind (DWP.allocatingModify_rel (ispec_iff.mp hspec F s hR)) fun x s' h => hk x s' h.1 h.2


theorem WP.Realizes.pure_frame {P : Prop} {F : IProp} {s : Heap} (h : Realizes (⌜P⌝ ∗ F) s) :
    P ∧ Realizes F s := by
  rw [← sep_emp_r_eq ⌜P⌝, Realizes.pure_sep, sep_emp_l_eq] at h
  exact h

end HeapLevel

/-- Writes the first value of a range. -/
theorem MutRawPtr.write.spec_head {T : Type} [Pointee T] [Pointee.Sized T] [Pointee.NoPointers T]
    (p : MutRawPtr T) (values : List T) (value : T) (h : 0 < values.length) :
    ⦃ p ↦* values ⦄ MutRawPtr.write p value ⦃ p ↦* values.set 0 value ⦄ := by
  simpa using MutRawPtr.write.spec_range p values 0 value h

end Aeneas.Std
