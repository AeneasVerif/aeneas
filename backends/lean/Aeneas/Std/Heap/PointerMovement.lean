module

public import Aeneas.Std.Core.PtrMovement
public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Core.PtrMovement
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Separation

@[expose] public section

namespace Aeneas.Std.SepLogic

theorem byteOffset.spec (repr : Repr T) (p : RawPtr T) (count : Int)
    (length : Nat) (own : Bool) (hstart : p.byteOffset.val ≤ length * repr.size)
    (hlo : 0 ≤ (p.byteOffset.val : Int) + count)
    (hhi : (p.byteOffset.val : Int) + count ≤ length * repr.size)
    (hfit : (p.byteOffset.val : Int) + count < (2 ^ UScalarTy.numBits .Usize : Nat)) :
    Triple (alloc repr ⟨p.base, ⟨0⟩⟩ length own)
      (fun s result s' => Heap.byteOffset p count s = some result ∧ s' = s)
      (fun result h => result.base = p.base ∧
        (result.byteOffset.val : Int) = (p.byteOffset.val : Int) + count ∧
        alloc repr ⟨p.base, ⟨0⟩⟩ length own h) := by
  rintro h F s ⟨_, rfl⟩ hd hm hi
  obtain ⟨blk, hl, hn, _, _⟩ := ((Fragment.matches_union _ _ _).mp hm).1 _ rfl
  let result : RawPtr T :=
    ⟨p.base, ⟨BitVec.ofNat _ ((p.byteOffset.val : Int) + count).toNat⟩⟩
  have hrval : (result.byteOffset.val : Int) = (p.byteOffset.val : Int) + count := by
    have ht : ((p.byteOffset.val : Int) + count).toNat < 2 ^ UScalarTy.numBits .Usize := by
      have he : (((p.byteOffset.val : Int) + count).toNat : Int) <
          (2 ^ UScalarTy.numBits .Usize : Nat) := by
        rw [Int.toNat_of_nonneg hlo]
        exact hfit
      exact_mod_cast he
    change ((BitVec.ofNat (UScalarTy.numBits .Usize)
      ((p.byteOffset.val : Int) + count).toNat).toNat : Int) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]
    exact Int.toNat_of_nonneg hlo
  have hrun : Heap.byteOffset p count s = some result := by
    have hf : (p.byteOffset.val : Int) + count < (2 : Int) ^ System.Platform.numBits := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, UScalarTy.Usize_numBits_eq] using hfit
    simp [Heap.byteOffset, Heap.offset, Repr.byteStride, RawPtr.cast, hl, hn,
      hstart, hlo, hhi, hf, result]
  refine ⟨⟨result, s, hrun, rfl⟩, ?_⟩
  rintro answer s' ⟨he, rfl⟩
  have he := Option.some.inj (he.symm.trans hrun)
  subst answer
  exact ⟨_, hd, hm, hi, rfl, hrval, rfl, rfl⟩

theorem offsetFrom.spec (repr : Repr T) (p origin : RawPtr T) (length : Nat) (own : Bool)
    (hsize : 0 < repr.size) (hbase : p.base = origin.base)
    (hp : p.byteOffset.val ≤ length * repr.size)
    (ho : origin.byteOffset.val ≤ length * repr.size)
    (hdiv : ((p.byteOffset.val : Int) - origin.byteOffset.val) % repr.size = 0)
    (hbytes : IScalar.cMin .Isize ≤ (p.byteOffset.val : Int) - origin.byteOffset.val ∧
      (p.byteOffset.val : Int) - origin.byteOffset.val ≤ IScalar.cMax .Isize)
    (hcount : IScalar.cMin .Isize ≤ ((p.byteOffset.val : Int) - origin.byteOffset.val) / repr.size ∧
      ((p.byteOffset.val : Int) - origin.byteOffset.val) / repr.size ≤ IScalar.cMax .Isize) :
    Triple (alloc repr ⟨p.base, ⟨0⟩⟩ length own)
      (fun s result s' => Heap.offsetFrom repr p origin s = some result ∧ s' = s)
      (fun result h => result.val = ((p.byteOffset.val : Int) - origin.byteOffset.val) / repr.size ∧
        result.val * repr.size = (p.byteOffset.val : Int) - origin.byteOffset.val ∧
        alloc repr ⟨p.base, ⟨0⟩⟩ length own h) := by
  rintro h F s ⟨_, rfl⟩ hd hm hi
  obtain ⟨blk, hl, hn, _, _⟩ := ((Fragment.matches_union _ _ _).mp hm).1 _ rfl
  let result := IScalar.ofInt (((p.byteOffset.val : Int) - origin.byteOffset.val) / repr.size) hcount
  have hrval : result.val = ((p.byteOffset.val : Int) - origin.byteOffset.val) / repr.size := by
    simp [result]
  have hrun : Heap.offsetFrom repr p origin s = some result := by
    have hlorigin : s.allocations origin.base = some blk := hbase ▸ hl
    simp [Heap.offsetFrom, hsize, hbase, hlorigin, hn, hp, ho, hdiv, hbytes, hcount, result]
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

theorem byte_offset.spec (repr : Repr T) (p : RawPtr T) (count : Isize)
    (length : Nat) (own : Bool) (hstart : p.byteOffset.val ≤ length * repr.size)
    (hlo : 0 ≤ (p.byteOffset.val : Int) + count.val)
    (hhi : (p.byteOffset.val : Int) + count.val ≤ length * repr.size)
    (hfit : (p.byteOffset.val : Int) + count.val < (2 ^ UScalarTy.numBits .Usize : Nat)) :
    Triple (alloc repr ⟨p.base, ⟨0⟩⟩ length own) (RawPtr.byte_offset p count)
      (fun result h => result.base = p.base ∧
        (result.byteOffset.val : Int) = (p.byteOffset.val : Int) + count.val ∧
        alloc repr ⟨p.base, ⟨0⟩⟩ length own h) :=
  Triple.checkedModify (SepLogic.byteOffset.spec repr p count.val length own hstart hlo hhi hfit)

theorem byte_add.spec (repr : Repr T) (p : RawPtr T) (count : Usize)
    (length : Nat) (own : Bool) (hstart : p.byteOffset.val ≤ length * repr.size)
    (hhi : p.byteOffset.val + count.val ≤ length * repr.size)
    (hfit : p.byteOffset.val + count.val < 2 ^ UScalarTy.numBits .Usize)
    (hcount : (count.val : Int) ≤ IScalar.cMax .Isize) :
    Triple (alloc repr ⟨p.base, ⟨0⟩⟩ length own) (RawPtr.byte_add p count)
      (fun result h => result.base = p.base ∧
        result.byteOffset.val = p.byteOffset.val + count.val ∧
        alloc repr ⟨p.base, ⟨0⟩⟩ length own h) := by
  unfold RawPtr.byte_add
  rw [ite_eq_left hcount]
  have hlo : 0 ≤ (p.byteOffset.val : Int) + count.val := by grind
  have hhi' : (p.byteOffset.val : Int) + count.val ≤ length * repr.size := by exact_mod_cast hhi
  have hfit' : (p.byteOffset.val : Int) + count.val < (2 ^ UScalarTy.numBits .Usize : Nat) := by
    exact_mod_cast hfit
  have ht := Triple.checkedModify
    (SepLogic.byteOffset.spec repr p count.val length own hstart hlo hhi' hfit')
  refine Triple.conseq (fun _ h => h) ?_ ht
  intro result h hp
  exact ⟨hp.1, by exact_mod_cast hp.2.1, hp.2.2⟩

theorem offset_from.spec (repr : Repr T) (p origin : RawPtr T) (length : Nat) (own : Bool)
    (hsize : 0 < repr.size) (hbase : p.base = origin.base)
    (hp : p.byteOffset.val ≤ length * repr.size)
    (ho : origin.byteOffset.val ≤ length * repr.size)
    (hdiv : ((p.byteOffset.val : Int) - origin.byteOffset.val) % repr.size = 0)
    (hbytes : IScalar.cMin .Isize ≤ (p.byteOffset.val : Int) - origin.byteOffset.val ∧
      (p.byteOffset.val : Int) - origin.byteOffset.val ≤ IScalar.cMax .Isize)
    (hcount : IScalar.cMin .Isize ≤ ((p.byteOffset.val : Int) - origin.byteOffset.val) / repr.size ∧
      ((p.byteOffset.val : Int) - origin.byteOffset.val) / repr.size ≤ IScalar.cMax .Isize) :
    Triple (alloc repr ⟨p.base, ⟨0⟩⟩ length own) (RawPtr.offset_from repr p origin)
      (fun result h => result.val = ((p.byteOffset.val : Int) - origin.byteOffset.val) / repr.size ∧
        result.val * repr.size = (p.byteOffset.val : Int) - origin.byteOffset.val ∧
        alloc repr ⟨p.base, ⟨0⟩⟩ length own h) :=
  Triple.checkedModify
    (SepLogic.offsetFrom.spec repr p origin length own hsize hbase hp ho hdiv hbytes hcount)

end Aeneas.Std.HeapWP
