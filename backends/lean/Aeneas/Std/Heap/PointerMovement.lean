module

public import Aeneas.Std.Core.PtrMovement
public import Aeneas.Std.Heap.Effects
import all Aeneas.Std.Core.PtrMovement
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Separation

@[expose] public section

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
