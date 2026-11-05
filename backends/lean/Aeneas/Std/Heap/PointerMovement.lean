module

public import Aeneas.Std.Core.PtrMovement
public import Aeneas.Std.Heap.Effects
import all Aeneas.Std.Core.PtrMovement
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Separation

@[expose] public section

namespace Aeneas.Std.Heap

/-- Even retired views retain allocation identity. Overlapping ranges in live
    allocations must have the same root; no byte-access permission is needed. -/
theorem Inv.same_root_of_overlap {s : Heap} (hi : s.Inv)
    {i j : Nat} {a b : Block} (ha : s.allocations i = some a)
    (hb : s.allocations j = some b)
    (aliveA : s.allocationAlive a = true) (aliveB : s.allocationAlive b = true)
    (overlap : a.bptr.val < b.bptr.val + b.repr.length ∧
      b.bptr.val < a.bptr.val + a.repr.length) :
    a.root = b.root := by
  have va := hi.validBlock ha
  have vb := hi.validBlock hb
  cases hra : s.allocations a.root
  · simp [allocationAlive, hra] at aliveA
  · rename_i ra
    cases hrb : s.allocations b.root
    · simp [allocationAlive, hrb] at aliveB
    · rename_i rb
      have ar : ra.alive = true := by simpa [allocationAlive, hra] using aliveA
      have br : rb.alive = true := by simpa [allocationAlive, hrb] using aliveB
      simp only [Heap.validBlock, hra, hrb, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at va vb
      by_contra different
      have row := List.all_eq_true.mp hi.2 a.root (List.mem_range.mpr (hi.base_lt hra))
      simp only [hra, Bool.and_eq_true] at row
      have pair := List.all_eq_true.mp row.2 b.root (List.mem_range.mpr (hi.base_lt hrb))
      simp [different, hrb, ar, br, overlaps] at pair
      grind

end Aeneas.Std.Heap

namespace Aeneas.Std.SepLogic

theorem byteOffset.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (count : Int)
    (length : Nat) (own : Bool)
    (hstart : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * repr.size)
    (hlo : (bptr.val : Int) ≤ (p.address.val : Int) + count)
    (hhi : (p.address.val : Int) + count ≤ bptr.val + length * repr.size)
    (hfit : (p.address.val : Int) + count < (2 ^ UScalarTy.numBits .Usize : Nat)) :
    Triple (alloc repr (RawPtr.mk p.provenance bptr) bptr length own)
      (fun s result s' => Heap.byteOffset p count s = some result ∧ s' = s)
      (fun result h => result.provenance = p.provenance ∧
        (result.address.val : Int) = (p.address.val : Int) + count ∧
        alloc repr (RawPtr.mk p.provenance bptr) bptr length own h) := by
  rintro h F s ⟨_, rfl⟩ hd hm hi
  obtain ⟨blk, hl, hn, hlive, hbptr, _⟩ :=
    ((Fragment.matches_union _ _ _).mp hm).1 _ rfl
  let result : RawPtr T :=
    ⟨p.provenance, ⟨BitVec.ofNat _ ((p.address.val : Int) + count).toNat⟩⟩
  have hnonneg : 0 ≤ (p.address.val : Int) + count := by agrind
  have hrval : (result.address.val : Int) = (p.address.val : Int) + count := by
    have ht : ((p.address.val : Int) + count).toNat < 2 ^ UScalarTy.numBits .Usize := by
      have he : (((p.address.val : Int) + count).toNat : Int) <
          (2 ^ UScalarTy.numBits .Usize : Nat) := by
        rw [Int.toNat_of_nonneg hnonneg]
        exact hfit
      exact_mod_cast he
    change ((BitVec.ofNat (UScalarTy.numBits .Usize)
      ((p.address.val : Int) + count).toNat).toNat : Int) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]
    exact Int.toNat_of_nonneg hnonneg
  have hrun : Heap.byteOffset p count s = some result := by
    have hf : (p.address.val : Int) + count < (2 : Int) ^ System.Platform.numBits := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, UScalarTy.Usize_numBits_eq] using hfit
    simp [Heap.byteOffset, Heap.offset, Repr.byteStride, RawPtr.cast, hl, hn,
      hlive, hbptr, hstart.1, hstart.2, hlo, hhi, hf, result]
  refine ⟨⟨result, s, hrun, rfl⟩, ?_⟩
  rintro answer s' ⟨he, rfl⟩
  have he := Option.some.inj (he.symm.trans hrun)
  subst answer
  exact ⟨_, hd, hm, hi, rfl, hrval, rfl, rfl⟩

theorem offsetFrom.spec (repr : Repr T) (p origin : RawPtr T) (bptr : BasePtr)
    (length : Nat) (own : Bool)
    (hsize : 0 < repr.size) (hbase : p.provenance = origin.provenance)
    (hp : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * repr.size)
    (ho : bptr.val ≤ origin.address.val ∧ origin.address.val ≤ bptr.val + length * repr.size)
    (hdiv : ((p.address.val : Int) - origin.address.val) % repr.size = 0)
    (hbytes : IScalar.cMin .Isize ≤ (p.address.val : Int) - origin.address.val ∧
      (p.address.val : Int) - origin.address.val ≤ IScalar.cMax .Isize)
    (hcount : IScalar.cMin .Isize ≤ ((p.address.val : Int) - origin.address.val) / repr.size ∧
      ((p.address.val : Int) - origin.address.val) / repr.size ≤ IScalar.cMax .Isize) :
    Triple (alloc repr (RawPtr.mk p.provenance bptr) bptr length own)
      (fun s result s' => Heap.offsetFrom repr p origin s = some result ∧ s' = s)
      (fun result h => result.val = ((p.address.val : Int) - origin.address.val) / repr.size ∧
        result.val * repr.size = (p.address.val : Int) - origin.address.val ∧
        alloc repr (RawPtr.mk p.provenance bptr) bptr length own h) := by
  rintro h F s ⟨_, rfl⟩ hd hm hi
  obtain ⟨blk, hl, hn, hlive, hbptr, _⟩ :=
    ((Fragment.matches_union _ _ _).mp hm).1 _ rfl
  let result := IScalar.ofInt (((p.address.val : Int) - origin.address.val) / repr.size) hcount
  have hrval : result.val = ((p.address.val : Int) - origin.address.val) / repr.size := by
    simp [result]
  have hrun : Heap.offsetFrom repr p origin s = some result := by
    have hlorigin : s.allocations origin.provenance = some blk := hbase ▸ hl
    simp [Heap.offsetFrom, Heap.distance, hl, hlorigin, hlive, hbptr, hn,
      hsize, hp.1, hp.2, ho.1, ho.2, hdiv, hbytes, hcount, result]
  refine ⟨⟨result, s, hrun, rfl⟩, ?_⟩
  rintro answer s' ⟨he, rfl⟩
  have he := Option.some.inj (he.symm.trans hrun)
  subst answer
  refine ⟨_, hd, hm, hi, hrval, ?_, rfl, rfl⟩
  rw [hrval]
  exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hdiv)

end Aeneas.Std.SepLogic

namespace Aeneas.Std.HeapWP

open SepLogic

/-- A scoped distance contract needs a common live allocation root, not equal
    or active view IDs. Retired views retain their bounds and provenance. -/
theorem offset_from_same_root.spec (repr : Repr T) (p origin : RawPtr T)
    (s₀ : Heap) (a b : Block)
    (ha : s₀.allocations p.provenance = some a)
    (hb : s₀.allocations origin.provenance = some b)
    (la : s₀.allocationAlive a = true) (lb : s₀.allocationAlive b = true)
    (root : a.root = b.root)
    (positive : 0 < repr.size)
    (hp : a.bptr.val ≤ p.address.val ∧ p.address.val ≤ a.bptr.val + a.repr.length)
    (ho : b.bptr.val ≤ origin.address.val ∧ origin.address.val ≤ b.bptr.val + b.repr.length)
    (divisible : ((p.address.val : Int) - origin.address.val) % repr.size = 0)
    (bytesFit : IScalar.cMin .Isize ≤ (p.address.val : Int) - origin.address.val ∧
      (p.address.val : Int) - origin.address.val ≤ IScalar.cMax .Isize)
    (countFit : IScalar.cMin .Isize ≤ ((p.address.val : Int) - origin.address.val) / repr.size ∧
      ((p.address.val : Int) - origin.address.val) / repr.size ≤ IScalar.cMax .Isize) :
    Spec (RawPtr.offset_from repr p origin)
      (fun result s₁ =>
        result.val = ((p.address.val : Int) - origin.address.val) / repr.size ∧ s₁ = s₀) s₀ := by
  let result := IScalar.ofInt (((p.address.val : Int) - origin.address.val) / repr.size) countFit
  have run : Heap.offsetFrom repr p origin s₀ = some result := by
    simp [Heap.offsetFrom, Heap.distance, ha, hb, la, lb, root, positive,
      hp.1, hp.2, ho.1, ho.2, divisible, bytesFit, countFit, result]
  apply Spec.checkedModify.mpr
  refine ⟨⟨result, s₀, run, rfl⟩, ?_⟩
  rintro answer s₁ ⟨computed, rfl⟩
  have same := Option.some.inj (computed.symm.trans run)
  subst answer
  exact ⟨by simp [result], rfl⟩

/-- Re-exposure at the same start address suffices for byte-pointer subtraction
    in a nonempty live allocation. Common root identity is derived, not assumed.
    In particular, the original access view may already have been returned. -/
theorem offset_from_reexposed.spec (start finish origin : RawPtr U8) (count : Nat)
    (s₀ : Heap) (a b : Block) (hi : s₀.Inv)
    (ha : s₀.allocations start.provenance = some a)
    (hb : s₀.allocations origin.provenance = some b)
    (la : s₀.allocationAlive a = true) (lb : s₀.allocationAlive b = true)
    (startBase : start.address = a.bptr) (originBase : origin.address = b.bptr)
    (sameAddress : start.address = origin.address)
    (nonemptyA : 0 < a.repr.length) (nonemptyB : 0 < b.repr.length)
    (sameView : finish.provenance = start.provenance)
    (cursor : finish.address.val = start.address.val + count)
    (within : count ≤ a.repr.length) (fits : (count : Int) ≤ IScalar.cMax .Isize) :
    Spec (RawPtr.offset_from Repr.u8 finish origin)
      (fun result s₁ => result.val = count ∧ s₁ = s₀) s₀ := by
  have bases : a.bptr = b.bptr := startBase.symm.trans (sameAddress.trans originBase)
  have overlap : a.bptr.val < b.bptr.val + b.repr.length ∧
      b.bptr.val < a.bptr.val + a.repr.length := by
    simp only [bases]
    constructor
    · agrind
    · agrind
  have root := hi.same_root_of_overlap ha hb la lb overlap
  have distance : (finish.address.val : Int) - origin.address.val = count := by
    simp only [cursor, sameAddress, Nat.cast_add]
    ring
  have lower : IScalar.cMin .Isize ≤ (count : Int) :=
    le_trans (by decide : IScalar.cMin .Isize ≤ 0) (Int.natCast_nonneg count)
  have finishBounds :
      a.bptr.val ≤ finish.address.val ∧
      finish.address.val ≤ a.bptr.val + a.repr.length := by
    simp only [cursor, startBase]
    constructor
    · agrind
    · agrind
  have originBounds :
      b.bptr.val ≤ origin.address.val ∧
      origin.address.val ≤ b.bptr.val + b.repr.length := by
    simp [originBase]
  have lookup : s₀.allocations finish.provenance = some a := sameView ▸ ha
  have divisible : ((finish.address.val : Int) - origin.address.val) % Repr.u8.size = 0 := by
    simp [Repr.u8]
  have bytesFit : IScalar.cMin .Isize ≤ (finish.address.val : Int) - origin.address.val ∧
      (finish.address.val : Int) - origin.address.val ≤ IScalar.cMax .Isize := by
    rw [distance]
    exact ⟨lower, fits⟩
  have countFit :
      IScalar.cMin .Isize ≤ ((finish.address.val : Int) - origin.address.val) / Repr.u8.size ∧
      ((finish.address.val : Int) - origin.address.val) / Repr.u8.size ≤ IScalar.cMax .Isize := by
    simpa [Repr.u8] using bytesFit
  have result := offset_from_same_root.spec Repr.u8 finish origin s₀ a b
    lookup hb la lb root (by decide) finishBounds originBounds divisible bytesFit countFit
  simpa [Repr.u8, distance] using result

theorem byte_offset.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (count : Isize)
    (length : Nat) (own : Bool)
    (hstart : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * repr.size)
    (hlo : (bptr.val : Int) ≤ (p.address.val : Int) + count.val)
    (hhi : (p.address.val : Int) + count.val ≤ bptr.val + length * repr.size)
    (hfit : (p.address.val : Int) + count.val < (2 ^ UScalarTy.numBits .Usize : Nat)) :
    Triple (alloc repr (RawPtr.mk p.provenance bptr) bptr length own) (RawPtr.byte_offset p count)
      (fun result h => result.provenance = p.provenance ∧
        (result.address.val : Int) = (p.address.val : Int) + count.val ∧
        alloc repr (RawPtr.mk p.provenance bptr) bptr length own h) :=
  Triple.checkedModify (SepLogic.byteOffset.spec repr p bptr count.val length own hstart hlo hhi hfit)

theorem byte_add.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (count : Usize)
    (length : Nat) (own : Bool)
    (hstart : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * repr.size)
    (hhi : p.address.val + count.val ≤ bptr.val + length * repr.size)
    (hfit : p.address.val + count.val < 2 ^ UScalarTy.numBits .Usize)
    (hcount : (count.val : Int) ≤ IScalar.cMax .Isize) :
    Triple (alloc repr (RawPtr.mk p.provenance bptr) bptr length own) (RawPtr.byte_add p count)
      (fun result h => result.provenance = p.provenance ∧
        result.address.val = p.address.val + count.val ∧
        alloc repr (RawPtr.mk p.provenance bptr) bptr length own h) := by
  unfold RawPtr.byte_add
  rw [ite_eq_left hcount]
  have hlo : (bptr.val : Int) ≤ (p.address.val : Int) + count.val := by agrind
  have hhi' : (p.address.val : Int) + count.val ≤ bptr.val + length * repr.size := by
    exact_mod_cast hhi
  have hfit' : (p.address.val : Int) + count.val < (2 ^ UScalarTy.numBits .Usize : Nat) := by
    exact_mod_cast hfit
  have ht := Triple.checkedModify
    (SepLogic.byteOffset.spec repr p bptr count.val length own hstart hlo hhi' hfit')
  refine Triple.conseq (fun _ h => h) ?_ ht
  intro result h hp
  exact ⟨hp.1, by exact_mod_cast hp.2.1, hp.2.2⟩

theorem offset_from.spec (repr : Repr T) (p origin : RawPtr T) (bptr : BasePtr)
    (length : Nat) (own : Bool)
    (hsize : 0 < repr.size) (hbase : p.provenance = origin.provenance)
    (hp : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * repr.size)
    (ho : bptr.val ≤ origin.address.val ∧ origin.address.val ≤ bptr.val + length * repr.size)
    (hdiv : ((p.address.val : Int) - origin.address.val) % repr.size = 0)
    (hbytes : IScalar.cMin .Isize ≤ (p.address.val : Int) - origin.address.val ∧
      (p.address.val : Int) - origin.address.val ≤ IScalar.cMax .Isize)
    (hcount : IScalar.cMin .Isize ≤ ((p.address.val : Int) - origin.address.val) / repr.size ∧
      ((p.address.val : Int) - origin.address.val) / repr.size ≤ IScalar.cMax .Isize) :
    Triple (alloc repr (RawPtr.mk p.provenance bptr) bptr length own) (RawPtr.offset_from repr p origin)
      (fun result h => result.val = ((p.address.val : Int) - origin.address.val) / repr.size ∧
        result.val * repr.size = (p.address.val : Int) - origin.address.val ∧
        alloc repr (RawPtr.mk p.provenance bptr) bptr length own h) :=
  Triple.checkedModify
    (SepLogic.offsetFrom.spec repr p origin bptr length own hsize hbase hp ho hdiv hbytes hcount)

end Aeneas.Std.HeapWP
