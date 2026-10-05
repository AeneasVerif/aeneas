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

end Aeneas.Std
