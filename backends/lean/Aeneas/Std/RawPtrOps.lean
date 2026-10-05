module
public import Aeneas.Std.Buffer
@[expose] public section

open Aeneas Aeneas.SepLogic

namespace Aeneas.Std

open WP Result

variable {T : Type}

def RawPtr.offsetBy [ByteRepr T] {M} (p : RawPtr T M) (k : Int) : Result (RawPtr T M) :=
  if 0 ≤ (p.offset : Int) + k * ByteRepr.size T then
    ok ⟨p.base, ((p.offset : Int) + k * ByteRepr.size T).toNat⟩
  else fail .undef

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::add"]
def core.ptr.mut_ptr.RawPtrMutT.add [ByteRepr T] (p : MutRawPtr T) (n : Usize) : Result (MutRawPtr T) :=
  ok (p.add n.val)

@[rust_fun "core::ptr::const_ptr::{*const @T}::add"]
def core.ptr.const_ptr.RawPtrConstT.add [ByteRepr T] (p : ConstRawPtr T) (n : Usize) : Result (ConstRawPtr T) :=
  ok (p.add n.val)

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::sub"]
def core.ptr.mut_ptr.RawPtrMutT.sub [ByteRepr T] (p : MutRawPtr T) (n : Usize) : Result (MutRawPtr T) :=
  p.offsetBy (-(n.val : Int))

@[rust_fun "core::ptr::const_ptr::{*const @T}::sub"]
def core.ptr.const_ptr.RawPtrConstT.sub [ByteRepr T] (p : ConstRawPtr T) (n : Usize) : Result (ConstRawPtr T) :=
  p.offsetBy (-(n.val : Int))

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::offset"]
def core.ptr.mut_ptr.RawPtrMutT.offset [ByteRepr T] (p : MutRawPtr T) (k : Isize) : Result (MutRawPtr T) :=
  p.offsetBy k.val

@[rust_fun "core::ptr::const_ptr::{*const @T}::offset"]
def core.ptr.const_ptr.RawPtrConstT.offset [ByteRepr T] (p : ConstRawPtr T) (k : Isize) : Result (ConstRawPtr T) :=
  p.offsetBy k.val

@[rust_fun "core::ptr::copy_nonoverlapping"]
def core.ptr.copy_nonoverlapping [ByteRepr T] (src : ConstRawPtr T) (dst : MutRawPtr T) (n : Usize) : Result Unit :=
  MutRawPtr.copyRange dst src n.val

@[rust_fun "core::ptr::copy"]
def core.ptr.copy [ByteRepr T] (src : ConstRawPtr T) (dst : MutRawPtr T) (n : Usize) : Result Unit :=
  Aeneas.Std.bind (Buffer.readRange src n.val) fun values => Buffer.writeRange dst values

@[simp] theorem RawPtr.offsetBy_nonneg [ByteRepr T] {M} (p : RawPtr T M) (k : Int)
    (h : 0 ≤ (p.offset : Int) + k * ByteRepr.size T) :
    p.offsetBy k = ok ⟨p.base, ((p.offset : Int) + k * ByteRepr.size T).toNat⟩ := by
  simp [RawPtr.offsetBy, h]

@[step]
theorem core.ptr.mut_ptr.RawPtrMutT.add.spec [ByteRepr T] (p : MutRawPtr T) (n : Usize) :
    ⦃ emp ⦄ core.ptr.mut_ptr.RawPtrMutT.add p n ⦃⇓ r => ⌜r = p.add n.val⌝ ⦄ := by
  unfold core.ptr.mut_ptr.RawPtrMutT.add; apply (ispec_ok _).2; simp

@[step]
theorem core.ptr.const_ptr.RawPtrConstT.add.spec [ByteRepr T] (p : ConstRawPtr T) (n : Usize) :
    ⦃ emp ⦄ core.ptr.const_ptr.RawPtrConstT.add p n ⦃⇓ r => ⌜r = p.add n.val⌝ ⦄ := by
  unfold core.ptr.const_ptr.RawPtrConstT.add; apply (ispec_ok _).2; simp

theorem RawPtr.offsetBy.spec [ByteRepr T] {M} (p : RawPtr T M) (k : Int)
    (h : 0 ≤ (p.offset : Int) + k * ByteRepr.size T) :
    ⦃ emp ⦄ p.offsetBy k
      ⦃⇓ r => ⌜r.base = p.base ∧ (r.offset : Int) = p.offset + k * ByteRepr.size T⌝ ⦄ := by
  rw [RawPtr.offsetBy_nonneg p k h]
  apply (ispec_ok _).2
  simp; omega

theorem RawPtr.offsetBy_neg.spec [ByteRepr T] {M} (p : RawPtr T M) (n : Nat)
    (h : n * ByteRepr.size T ≤ p.offset) :
    ⦃ emp ⦄ p.offsetBy (-(n : Int)) ⦃⇓ r => ⌜r.add n = p⌝ ⦄ := by
  have h' : 0 ≤ (p.offset : Int) + -(n : Int) * ByteRepr.size T := by
    have : ((n * ByteRepr.size T : Nat) : Int) ≤ p.offset := by exact_mod_cast h
    push_cast at this; linarith
  rw [RawPtr.offsetBy_nonneg p _ h']
  apply (ispec_ok _).2
  cases p
  simp only [RawPtr.add, RawPtr.mk.injEq, true_and]
  iintro
  iframe

@[step]
theorem core.ptr.mut_ptr.RawPtrMutT.sub.spec [ByteRepr T] (p : MutRawPtr T) (n : Usize)
    (h : n.val * ByteRepr.size T ≤ p.offset) :
    ⦃ emp ⦄ core.ptr.mut_ptr.RawPtrMutT.sub p n ⦃⇓ r => ⌜r.add n.val = p⌝ ⦄ :=
  RawPtr.offsetBy_neg.spec p n.val h

@[step]
theorem core.ptr.const_ptr.RawPtrConstT.sub.spec [ByteRepr T] (p : ConstRawPtr T) (n : Usize)
    (h : n.val * ByteRepr.size T ≤ p.offset) :
    ⦃ emp ⦄ core.ptr.const_ptr.RawPtrConstT.sub p n ⦃⇓ r => ⌜r.add n.val = p⌝ ⦄ :=
  RawPtr.offsetBy_neg.spec p n.val h

@[step]
theorem core.ptr.mut_ptr.RawPtrMutT.offset.spec [ByteRepr T] (p : MutRawPtr T) (k : Isize)
    (h : 0 ≤ (p.offset : Int) + k.val * ByteRepr.size T) :
    ⦃ emp ⦄ core.ptr.mut_ptr.RawPtrMutT.offset p k
    ⦃⇓ r => ⌜r.base = p.base ∧ (r.offset : Int) = p.offset + k.val * ByteRepr.size T⌝ ⦄ :=
  RawPtr.offsetBy.spec p _ h

@[step]
theorem core.ptr.const_ptr.RawPtrConstT.offset.spec [ByteRepr T] (p : ConstRawPtr T) (k : Isize)
    (h : 0 ≤ (p.offset : Int) + k.val * ByteRepr.size T) :
    ⦃ emp ⦄ core.ptr.const_ptr.RawPtrConstT.offset p k
    ⦃⇓ r => ⌜r.base = p.base ∧ (r.offset : Int) = p.offset + k.val * ByteRepr.size T⌝ ⦄ :=
  RawPtr.offsetBy.spec p _ h

@[step]
theorem core.ptr.copy_nonoverlapping.spec [ByteRepr T] (src : ConstRawPtr T) (dst : MutRawPtr T) (n : Usize)
    (srcValues dstValues : List T) (hSrc : srcValues.length = n.val) (hDst : dstValues.length = n.val) :
    ⦃ dst ↦* dstValues ∗ src ↦* srcValues ⦄ core.ptr.copy_nonoverlapping src dst n
    ⦃⇓ dst ↦* srcValues ∗ src ↦* srcValues ⦄ := by
  unfold core.ptr.copy_nonoverlapping
  have := MutRawPtr.copyRange.spec dst src dstValues srcValues (by omega)
  rw [hSrc] at this
  exact this

/-! ## Pointer casts -/

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::cast"]
def core.ptr.mut_ptr.RawPtrMutT.cast (U : Type) (p : MutRawPtr T) : Result (MutRawPtr U) :=
  RawPtr.cast_scalar U .Mut p

@[rust_fun "core::ptr::const_ptr::{*const @T}::cast"]
def core.ptr.const_ptr.RawPtrConstT.cast (U : Type) (p : ConstRawPtr T) :
    Result (ConstRawPtr U) :=
  RawPtr.cast_scalar U .Const p

@[step]
theorem core.ptr.mut_ptr.RawPtrMutT.cast.spec (U : Type) (p : MutRawPtr T) :
    ⦃ emp ⦄ core.ptr.mut_ptr.RawPtrMutT.cast U p ⦃⇓ q => ⌜q = p.retype⌝⦄ :=
  RawPtr.cast_scalar.spec p

@[step]
theorem core.ptr.const_ptr.RawPtrConstT.cast.spec (U : Type) (p : ConstRawPtr T) :
    ⦃ emp ⦄ core.ptr.const_ptr.RawPtrConstT.cast U p ⦃⇓ q => ⌜q = p.retype⌝⦄ :=
  RawPtr.cast_scalar.spec p

/-! ## Unaligned accesses

They read and write the bytes of the address through a `u8` view, so they do
not require the address to be aligned for `T`. -/

/-- The bytes of `p`'s address, viewed as `u8`s. -/
abbrev RawPtr.bytesPtr {M} (p : RawPtr T M) : RawPtr U8 M := p.retype

/-- Read a `T` from any address: decode the `size T` bytes it starts. -/
def RawPtr.readUnaligned [ByteRepr T] {M} (p : RawPtr T M) : Result T :=
  Aeneas.Std.bind (Buffer.readRange p.bytesPtr (ByteRepr.size T)) fun bytes =>
    match ByteRepr.decode (bytes.map UScalar.bv) with
    | some v => ok v
    | none => fail .undef

/-- Write a `T` at any address: overwrite the `size T` bytes it starts. -/
def MutRawPtr.writeUnaligned [ByteRepr T] (p : MutRawPtr T) (v : T) : Result Unit :=
  Buffer.writeRange p.bytesPtr ((ByteRepr.encode v).map (UScalar.mk (ty := .U8)))

@[step]
theorem RawPtr.readUnaligned.spec [ByteRepr T] {M} (p : RawPtr T M) (v : T) :
    ⦃ p.bytesPtr ↦* (ByteRepr.encode v).map (UScalar.mk (ty := .U8)) ⦄ p.readUnaligned
      ⦃⇓ r => ⌜r = v⌝ ∗ p.bytesPtr ↦* (ByteRepr.encode v).map (UScalar.mk (ty := .U8)) ⦄ := by
  unfold RawPtr.readUnaligned
  have hLen : ((ByteRepr.encode v).map (UScalar.mk (ty := .U8))).length = ByteRepr.size T := by
    simp [ByteRepr.length_encode]
  have := Buffer.readRange.spec p.bytesPtr ((ByteRepr.encode v).map (UScalar.mk (ty := .U8)))
  rw [hLen] at this
  apply WP.ispec_bind this (sep_emp_r _).mpr
  intro bytes
  rw [sep_emp_r_eq]
  iintro hBytes
  subst bytes
  have hDec : ByteRepr.decode (((ByteRepr.encode v).map (UScalar.mk (ty := .U8))).map UScalar.bv) = some v := by
    rw [List.map_map]
    simp [ByteRepr.decode_encode]
  simp only [hDec]
  apply (ispec_ok _).2
  iframe

@[step]
theorem MutRawPtr.writeUnaligned.spec [ByteRepr T] (p : MutRawPtr T) (old : List U8) (v : T)
    (hLen : old.length = ByteRepr.size T) :
    ⦃ p.bytesPtr ↦* old ⦄ p.writeUnaligned v
      ⦃⇓ p.bytesPtr ↦* (ByteRepr.encode v).map (UScalar.mk (ty := .U8)) ⦄ :=
  Buffer.writeRange.spec p.bytesPtr old _ (by simp [hLen, ByteRepr.length_encode])

@[rust_fun "core::ptr::read_unaligned"]
def core.ptr.read_unaligned [ByteRepr T] (p : ConstRawPtr T) : Result T := p.readUnaligned

@[rust_fun "core::ptr::const_ptr::{*const @T}::read_unaligned"]
def core.ptr.const_ptr.RawPtrConstT.read_unaligned [ByteRepr T] (p : ConstRawPtr T) : Result T :=
  p.readUnaligned

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::read_unaligned"]
def core.ptr.mut_ptr.RawPtrMutT.read_unaligned [ByteRepr T] (p : MutRawPtr T) : Result T :=
  p.readUnaligned

@[rust_fun "core::ptr::write_unaligned"]
def core.ptr.write_unaligned [ByteRepr T] (p : MutRawPtr T) (v : T) : Result Unit :=
  p.writeUnaligned v

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write_unaligned"]
def core.ptr.mut_ptr.RawPtrMutT.write_unaligned [ByteRepr T] (p : MutRawPtr T) (v : T) :
    Result Unit :=
  p.writeUnaligned v

attribute [step_simps] core.ptr.read_unaligned core.ptr.const_ptr.RawPtrConstT.read_unaligned
  core.ptr.mut_ptr.RawPtrMutT.read_unaligned core.ptr.write_unaligned
  core.ptr.mut_ptr.RawPtrMutT.write_unaligned

/-! ## Distances between pointers -/

/-- The distance from `origin` to `p`, in elements: undefined if the pointers
are not in the same allocation, or if the distance in bytes is not a multiple of
the size of the elements. -/
def RawPtr.offsetFrom [ByteRepr T] {M M'} (p : RawPtr T M) (origin : RawPtr T M') :
    Result Isize :=
  let diff : Int := (p.offset : Int) - origin.offset
  if p.base = origin.base ∧ 0 < ByteRepr.size T ∧ (ByteRepr.size T : Int) ∣ diff then
    IScalar.tryMk .Isize (diff / ByteRepr.size T)
  else fail .undef

@[step]
theorem RawPtr.offsetFrom.spec [ByteRepr T] {M M'} (p : RawPtr T M) (origin : RawPtr T M')
    (k : Int) (hBase : p.base = origin.base) (hSize : 0 < ByteRepr.size T)
    (hOffset : (p.offset : Int) = origin.offset + k * ByteRepr.size T)
    (hk : IScalar.inBounds .Isize k) :
    ⦃ emp ⦄ p.offsetFrom origin ⦃⇓ r => ⌜r.val = k⌝⦄ := by
  unfold RawPtr.offsetFrom
  have hDiff : (p.offset : Int) - origin.offset = k * ByteRepr.size T := by omega
  have hDvd : (ByteRepr.size T : Int) ∣ (p.offset : Int) - origin.offset :=
    ⟨k, by rw [hDiff, Int.mul_comm]⟩
  have hDiv : ((p.offset : Int) - origin.offset) / ByteRepr.size T = k := by
    rw [hDiff]; exact Int.mul_ediv_cancel _ (by omega)
  simp only [hBase, hSize, hDvd, and_self, ↓reduceIte, hDiv]
  have h := IScalar.tryMkOpt_eq .Isize k
  unfold IScalar.tryMk
  split at h
  · rename_i y hy
    rw [hy]
    apply (ispec_ok _).2
    exact (entails_emp_ipure_iff _).mpr h.1
  · exact absurd hk h

@[rust_fun "core::ptr::const_ptr::{*const @T}::offset_from"]
def core.ptr.const_ptr.RawPtrConstT.offset_from [ByteRepr T] (p origin : ConstRawPtr T) :
    Result Isize :=
  p.offsetFrom origin

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::offset_from"]
def core.ptr.mut_ptr.RawPtrMutT.offset_from [ByteRepr T] (p : MutRawPtr T)
    (origin : ConstRawPtr T) : Result Isize :=
  p.offsetFrom origin

attribute [step_simps] core.ptr.const_ptr.RawPtrConstT.offset_from
  core.ptr.mut_ptr.RawPtrMutT.offset_from

/-! ## Filling memory -/

/-- Set `count * size_of::<T>()` bytes to `val`, from `p` on. -/
def RawPtr.writeBytes [ByteRepr T] (p : MutRawPtr T) (val : U8) (count : Usize) :
    Result Unit :=
  MutRawPtr.fillRange p.bytesPtr val (count.val * ByteRepr.size T)

@[step]
theorem RawPtr.writeBytes.spec [ByteRepr T] (p : MutRawPtr T) (val : U8) (count : Usize)
    (old : List U8) (hLen : old.length = count.val * ByteRepr.size T) :
    ⦃ p.bytesPtr ↦* old ⦄ RawPtr.writeBytes p val count
      ⦃⇓ p.bytesPtr ↦* List.replicate (count.val * ByteRepr.size T) val ⦄ := by
  unfold RawPtr.writeBytes
  rw [← hLen]
  exact MutRawPtr.fillRange.spec p.bytesPtr old val

@[rust_fun "core::ptr::write_bytes"]
def core.ptr.write_bytes [ByteRepr T] (p : MutRawPtr T) (val : U8) (count : Usize) :
    Result Unit :=
  RawPtr.writeBytes p val count

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write_bytes"]
def core.ptr.mut_ptr.RawPtrMutT.write_bytes [ByteRepr T] (p : MutRawPtr T) (val : U8)
    (count : Usize) : Result Unit :=
  RawPtr.writeBytes p val count

attribute [step_simps] core.ptr.write_bytes core.ptr.mut_ptr.RawPtrMutT.write_bytes

@[simp] theorem RawPtr.bytesPtr_retype {T U : Type} {M M'} (q : RawPtr T M) :
    ((q.retype : RawPtr U M').bytesPtr : RawPtr U8 M') = q.retype := rfl


/-! ## Raw pointers to values (`&raw const v`, `&raw mut v`) -/

/-- Convert a value to a raw pointer: the value is copied into fresh memory. -/
def RawPtr.addr_of [ByteRepr T] (v : T) : Result (ConstRawPtr T) :=
  RawPtr.materialize [v]

@[step]
theorem RawPtr.addr_of.spec [ByteRepr T] (v : T) :
    ⦃ emp ⦄ RawPtr.addr_of v ⦃⇓ p => p ↦ v⦄ := by
  unfold RawPtr.addr_of
  simp only [RawPtr.pointsTo_eq_range]
  exact RawPtr.materialize.spec [v]

def RawPtr.addr_of_mut [ByteRepr T] (v : T) : Result (MutRawPtr T) :=
  RawPtr.materialize [v]

@[step]
theorem RawPtr.addr_of_mut.spec [ByteRepr T] (v : T) :
    ⦃ emp ⦄ RawPtr.addr_of_mut v ⦃⇓ p => p ↦ v⦄ := by
  unfold RawPtr.addr_of_mut
  simp only [RawPtr.pointsTo_eq_range]
  exact RawPtr.materialize.spec [v]

/-- End a raw pointer created with `RawPtr.addr_of`: free its memory. -/
def RawPtr.end_addr_of [ByteRepr T] (_v : T) (p : ConstRawPtr T) : Result Unit :=
  MutRawPtr.free p.toMut

@[step]
theorem RawPtr.end_addr_of.spec [ByteRepr T] (v : T) (p : ConstRawPtr T) :
    ⦃ p ↦ v ⦄ RawPtr.end_addr_of v p ⦃⇓ emp⦄ := by
  unfold RawPtr.end_addr_of
  have := MutRawPtr.free.spec p.toMut v
  rwa [RawPtr.pointsTo_toMut] at this

/-- End a raw pointer created with `RawPtr.addr_of_mut`: read the value back
and free its memory. -/
def RawPtr.end_addr_of_mut [ByteRepr T] (_v : T) (p : MutRawPtr T) : Result T := do
  let v ← p.read
  MutRawPtr.free p
  ok v

@[step]
theorem RawPtr.end_addr_of_mut.spec [ByteRepr T] (v' v : T) (p : MutRawPtr T) :
    ⦃ p ↦ v ⦄ RawPtr.end_addr_of_mut v' p ⦃⇓ r => ⌜r = v⌝⦄ := by
  unfold RawPtr.end_addr_of_mut
  apply WP.ispec_bind (RawPtr.read.spec p v) (sep_emp_r _).mpr
  intro r
  rw [sep_emp_r_eq, sep_comm_eq]
  apply WP.ispec_bind (MutRawPtr.free.spec p v) (entails_refl _)
  intro _
  rw [sep_emp_l_eq]
  exact (ispec_ok _).2 (entails_refl _)

/-! ## `ptr::read` and `ptr::write` -/

@[rust_fun "core::ptr::read"]
def core.ptr.read [ByteRepr T] (p : ConstRawPtr T) : Result T :=
  p.read

@[rust_fun "core::ptr::write"]
def core.ptr.write [ByteRepr T] (p : MutRawPtr T) (v : T) : Result Unit :=
  MutRawPtr.write p v

attribute [step_simps] core.ptr.read core.ptr.write

end Aeneas.Std
