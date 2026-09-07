/-
  Properties/Aes/Axioms/InPlaceOrDisjointBuffer.lean — axioms about
  `InPlaceOrDisjointBuffer`:

  ```rust
  pub struct InPlaceOrDisjointBuffer<'a, T> {
      src: *const T,
      dst: *mut T,
      len: usize,
      _phantom: PhantomData<&'a mut [T]>,
  }
  ```

  The `src` and `dst` pointers must be equal or disjoint. They are created
  from either a shared and a mutable borrow of lifetime 'a, or from
  the same mutable borrow.
-/
import Aeneas.SLPoC.MutableData.Buffer
import Aeneas.Std.Array.Array

open Aeneas.Std (Result Slice)
open Aeneas.SepLogic.WP

namespace core.core_arch.x86

set_option linter.style.nameCheck false in
abbrev __m128i := Aeneas.Std.Array Aeneas.Std.U8 16#usize

end core.core_arch.x86

/-- High-level view of `common::InPlaceOrDisjointBuffer`: either one aliased
    slice (in-place mode) or two disjoint slices of equal length. -/
inductive InPlaceOrDisjointBuffer (T : Type) where
| equal (a : Slice T)
| disjoint (src dst : Slice T) (hEq : src.length = dst.length)

namespace InPlaceOrDisjointBuffer

variable {T : Type}

/-- The source side (what Rust's `src()` observes). -/
def src : InPlaceOrDisjointBuffer T → Slice T
| .equal a => a
| .disjoint src _ _ => src

/-- The destination side (what Rust's `dst()` observes). -/
def dst : InPlaceOrDisjointBuffer T → Slice T
| .equal a => a
| .disjoint _ dst _ => dst

/-- The common length of the two sides (Rust has a single `len` field). -/
def length (b : InPlaceOrDisjointBuffer T) : Nat := (src b).length

/-- Update the destination side. -/
def setDst (b : InPlaceOrDisjointBuffer T) (s : Slice T) :
    InPlaceOrDisjointBuffer T :=
  match b with
  | .equal _ => .equal s
  | .disjoint src _ _ => if h : src.length = s.length then .disjoint src s h else b

@[simp] theorem src_equal (a : Slice T) : src (.equal a) = a := rfl
@[simp] theorem dst_equal (a : Slice T) : dst (.equal a) = a := rfl

@[simp] theorem src_disjoint (s d : Slice T) (h : s.length = d.length) :
    src (.disjoint s d h) = s := rfl

@[simp] theorem dst_disjoint (s d : Slice T) (h : s.length = d.length) :
    dst (.disjoint s d h) = d := rfl

/-- The two sides always have the same length. -/
theorem length_eq (b : InPlaceOrDisjointBuffer T) :
    (src b).length = (dst b).length := by
  cases b <;> simp_all

@[simp] theorem length_eq_src (b : InPlaceOrDisjointBuffer T) :
    (src b).length = length b := rfl

@[simp] theorem length_eq_dst (b : InPlaceOrDisjointBuffer T) :
    (dst b).length = length b := (length_eq b).symm

@[simp] theorem dst_setDst (b : InPlaceOrDisjointBuffer T) (s : Slice T)
    (h : s.length = length b) : dst (setDst b s) = s := by
  cases b <;> simp_all [setDst, length]

@[simp] theorem setDst_dst (b : InPlaceOrDisjointBuffer T) :
    setDst b (dst b) = b := by
  cases b <;> simp_all [setDst]

@[simp] theorem length_setDst (b : InPlaceOrDisjointBuffer T) (s : Slice T)
    (h : s.length = length b) : length (setDst b s) = length b := by
  cases b <;> simp_all [setDst, length]

end InPlaceOrDisjointBuffer

/-! ## Standalone generated-code interface

The original file imports these declarations from VCR's generated `Symcrust`
modules.  Here the generated buffer is represented directly by its high-level
view, and the small fragment of generated code used below is executable.
-/

namespace common

private unsafe def transmuteSliceImpl {T U : Type} (s : Slice T) : Slice U :=
  unsafeCast s

private instance {T : Type} : Nonempty (Slice T) :=
  ⟨Slice.from [] (by simp)⟩

/-- Byte-level reinterpretation used by the unsafe SIMD operations. -/
@[implemented_by transmuteSliceImpl]
opaque transmuteSlice {T U : Type} : Slice T → Slice U

@[simp] axiom transmuteSlice_self {T : Type} (s : Slice T) :
    transmuteSlice (T := T) (U := T) s = s

abbrev InPlaceOrDisjointBuffer (T : Type) :=
  _root_.InPlaceOrDisjointBuffer T

namespace InPlaceOrDisjointBuffer

def len {T : Type} (b : common.InPlaceOrDisjointBuffer T) :
    Result Aeneas.Std.Usize :=
  pure (Aeneas.Std.Usize.ofNatCore
    (_root_.InPlaceOrDisjointBuffer.length b) (by
      have h := (_root_.InPlaceOrDisjointBuffer.src b).property
      simp only [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits] at h
      change
        (_root_.InPlaceOrDisjointBuffer.src b).val.length <
          2 ^ Aeneas.Std.UScalarTy.Usize.numBits
      have hp : 0 < 2 ^ Aeneas.Std.UScalarTy.Usize.numBits := by positivity
      omega))

def src {T : Type} (b : common.InPlaceOrDisjointBuffer T) :
    Result (Slice T) :=
  pure (_root_.InPlaceOrDisjointBuffer.src b)

def dst {T : Type} (b : common.InPlaceOrDisjointBuffer T) :
    Result (Slice T ×
      (Slice T → common.InPlaceOrDisjointBuffer T) ×
      (common.InPlaceOrDisjointBuffer T → common.InPlaceOrDisjointBuffer T)) :=
  pure (_root_.InPlaceOrDisjointBuffer.dst b,
    _root_.InPlaceOrDisjointBuffer.setDst b, id)

def new_disjoint_from_slices {T : Type} (src dst : Slice T) :
    Result (common.InPlaceOrDisjointBuffer T ×
      (common.InPlaceOrDisjointBuffer T → Slice T)) :=
  if h : src.length = dst.length then
    pure (.disjoint src dst h,
      fun b => _root_.InPlaceOrDisjointBuffer.dst b)
  else
    pure (.equal src, fun b => _root_.InPlaceOrDisjointBuffer.dst b)

private def getBlock
    (s : Slice Aeneas.Std.U8) (i : Aeneas.Std.Usize) :
    Aeneas.Std.Array Aeneas.Std.U8 16#usize :=
  if h : i.val + 16 ≤ s.length then
    Aeneas.Std.Array.from ((s.val.drop i.val).take 16) (by
      have hi : i.val + 16 ≤ s.val.length := h
      simp only [List.length_take, List.length_drop]
      change min 16 (s.val.length - i.val) = 16
      rw [Nat.min_eq_left]
      omega)
  else
    Aeneas.Std.Array.repeat 16#usize 0#u8

@[simp] private theorem getBlock_val
    (s : Slice Aeneas.Std.U8) (i : Aeneas.Std.Usize)
    (h : i.val + 16 ≤ s.length) :
    (getBlock s i).val = (s.val.drop i.val).take 16 := by
  simp [getBlock, h]

def loadu_si128_src {T : Type}
    (b : common.InPlaceOrDisjointBuffer T) (i : Aeneas.Std.Usize) :
    Result core.core_arch.x86.__m128i :=
  pure (getBlock
    (transmuteSlice (_root_.InPlaceOrDisjointBuffer.src b)) i)

def loadu_si128_dst {T : Type}
    (b : common.InPlaceOrDisjointBuffer T) (i : Aeneas.Std.Usize) :
    Result core.core_arch.x86.__m128i :=
  pure (getBlock
    (transmuteSlice (_root_.InPlaceOrDisjointBuffer.dst b)) i)

def storeu_si128 {T : Type}
    (b : common.InPlaceOrDisjointBuffer T) (i : Aeneas.Std.Usize)
    (v : core.core_arch.x86.__m128i) :
    Result (common.InPlaceOrDisjointBuffer T ×
      (common.InPlaceOrDisjointBuffer T →
        common.InPlaceOrDisjointBuffer T)) :=
  let dst : Slice Aeneas.Std.U8 :=
    transmuteSlice (_root_.InPlaceOrDisjointBuffer.dst b)
  let dst := dst.setSlice! i.val v.val
  pure (_root_.InPlaceOrDisjointBuffer.setDst b (transmuteSlice dst), id)

end InPlaceOrDisjointBuffer

end common

namespace aes.aes_xmm.InPlaceOrDisjointBufferAU8

def m128_loadu_src
    (b : common.InPlaceOrDisjointBuffer Aeneas.Std.U8)
    (i : Aeneas.Std.Usize) :
    Result (Aeneas.Std.Array Aeneas.Std.U8 16#usize) :=
  common.InPlaceOrDisjointBuffer.loadu_si128_src b i

def m128_loadu_dst
    (b : common.InPlaceOrDisjointBuffer Aeneas.Std.U8)
    (i : Aeneas.Std.Usize) :
    Result (Aeneas.Std.Array Aeneas.Std.U8 16#usize) :=
  common.InPlaceOrDisjointBuffer.loadu_si128_dst b i

def m128_storeu
    (b : common.InPlaceOrDisjointBuffer Aeneas.Std.U8)
    (i : Aeneas.Std.Usize)
    (v : Aeneas.Std.Array Aeneas.Std.U8 16#usize) :
    Result (common.InPlaceOrDisjointBuffer Aeneas.Std.U8 ×
      (common.InPlaceOrDisjointBuffer Aeneas.Std.U8 →
        common.InPlaceOrDisjointBuffer Aeneas.Std.U8)) :=
  common.InPlaceOrDisjointBuffer.storeu_si128 b i v

end aes.aes_xmm.InPlaceOrDisjointBufferAU8

/-- **Abstraction function.**  Maps the opaque Aeneas buffer to its high-level view. -/
def common.InPlaceOrDisjointBuffer.val {T : Type}
    (b : common.InPlaceOrDisjointBuffer T) :
    _root_.InPlaceOrDisjointBuffer T :=
  b

open InPlaceOrDisjointBuffer

namespace symcrust.aesgcm

/-! ## Accessors -/

/-- `len` returns the common length of the two sides. -/
@[step]
theorem InPlaceOrDisjointBuffer.len.spec {T : Type}
    (b : common.InPlaceOrDisjointBuffer T) :
    common.InPlaceOrDisjointBuffer.len b
    ⦃ n => n.val = b.val.length ⦄ := by
  unfold common.InPlaceOrDisjointBuffer.len
  step*
  simp [common.InPlaceOrDisjointBuffer.val]
  iframe

/-- `src` returns the source side. -/
@[step]
theorem InPlaceOrDisjointBuffer.src.spec {T : Type}
    (b : common.InPlaceOrDisjointBuffer T) :
    common.InPlaceOrDisjointBuffer.src b
    ⦃ s => s = b.val.src ⦄ := by
  unfold common.InPlaceOrDisjointBuffer.src
  step*
  simp [common.InPlaceOrDisjointBuffer.val]
  iframe

/-- `dst` returns the destination side plus two backward functions:
    - `back1` updates the destination buffer
    - `back2` propagates mutations of the enclosing `&mut self` (there are none,
      so this is the identity) -/
@[step]
theorem InPlaceOrDisjointBuffer.dst.spec {T : Type}
    (b : common.InPlaceOrDisjointBuffer T) :
    common.InPlaceOrDisjointBuffer.dst b
    ⦃ s back1 back2 =>
      s = b.val.dst ∧
      (∀ s' : Slice T, s'.length = b.val.length →
        (back1 s').val = b.val.setDst s') ∧
      (∀ b' : common.InPlaceOrDisjointBuffer T, (back2 b').val = b'.val) ⦄ := by
  unfold common.InPlaceOrDisjointBuffer.dst
  step*
  simp [common.InPlaceOrDisjointBuffer.val]
  iframe

/-- `new_disjoint_from_slices` builds a disjoint-mode buffer. -/
@[step]
theorem InPlaceOrDisjointBuffer.new_disjoint_from_slices.spec {T : Type}
    (src dst : Slice T) (h_len : src.length = dst.length) :
    common.InPlaceOrDisjointBuffer.new_disjoint_from_slices src dst
    ⦃ buf back =>
      buf.val = .disjoint src dst h_len ∧
      (∀ b' : common.InPlaceOrDisjointBuffer T, back b' = b'.val.dst) ⦄ := by
  unfold common.InPlaceOrDisjointBuffer.new_disjoint_from_slices
  simp only [h_len, ↓reduceDIte]
  step*
  simp [common.InPlaceOrDisjointBuffer.val]
  iframe

/-! ## SIMD accessors -/

/-- `loadu_si128_src b i` reads the 16 bytes of the source side at offset `i`. -/
@[step]
theorem InPlaceOrDisjointBuffer.loadu_si128_src.spec
    (b : common.InPlaceOrDisjointBuffer Aeneas.Std.U8) (i : Aeneas.Std.Usize)
    (h : i.val + 16 ≤ b.val.length) :
    common.InPlaceOrDisjointBuffer.loadu_si128_src b i
    ⦃ (r : core.core_arch.x86.__m128i) =>
      r.val = ((b.val.src).val.drop i.val).take 16 ⦄ := by
  have hsrc :
      i.val + 16 ≤ (_root_.InPlaceOrDisjointBuffer.src b).length := by
    simpa [common.InPlaceOrDisjointBuffer.val] using h
  unfold common.InPlaceOrDisjointBuffer.loadu_si128_src
  step*
  simp [common.InPlaceOrDisjointBuffer.val,
    common.InPlaceOrDisjointBuffer.getBlock_val _ _ hsrc]
  iframe

/-- `loadu_si128_dst b i` reads the 16 bytes of the destination side at offset `i`. -/
@[step]
theorem InPlaceOrDisjointBuffer.loadu_si128_dst.spec
    (b : common.InPlaceOrDisjointBuffer Aeneas.Std.U8) (i : Aeneas.Std.Usize)
    (h : i.val + 16 ≤ b.val.length) :
    common.InPlaceOrDisjointBuffer.loadu_si128_dst b i
    ⦃ (r : core.core_arch.x86.__m128i) =>
      r.val = ((b.val.dst).val.drop i.val).take 16 ⦄ := by
  have hdst :
      i.val + 16 ≤ (_root_.InPlaceOrDisjointBuffer.dst b).length := by
    simpa [common.InPlaceOrDisjointBuffer.val] using h
  unfold common.InPlaceOrDisjointBuffer.loadu_si128_dst
  step*
  simp [common.InPlaceOrDisjointBuffer.val,
    common.InPlaceOrDisjointBuffer.getBlock_val _ _ hdst]
  iframe

/-- `storeu_si128 b i v` splices the 16 bytes of `v` into the destination side. -/
@[step]
theorem InPlaceOrDisjointBuffer.storeu_si128.spec
    (b : common.InPlaceOrDisjointBuffer Aeneas.Std.U8) (i : Aeneas.Std.Usize)
    (v : core.core_arch.x86.__m128i) (h : i.val + 16 ≤ b.val.length) :
    common.InPlaceOrDisjointBuffer.storeu_si128 b i v
    ⦃ b' back =>
      (b'.val.dst).val = List.setSlice! (b.val.dst).val i.val v.val ∧
      b'.val = b.val.setDst b'.val.dst ∧
      (∀ b'' : common.InPlaceOrDisjointBuffer Aeneas.Std.U8,
        (back b'').val = b''.val) ⦄ := by
  have _hi : i.val ≤ b.val.length := by omega
  unfold common.InPlaceOrDisjointBuffer.storeu_si128
  step*
  simp [common.InPlaceOrDisjointBuffer.val]
  iframe

/-! ## The `aes_xmm` `u8` shims -/

@[step]
theorem InPlaceOrDisjointBuffer.m128_loadu_src.spec
    (b : common.InPlaceOrDisjointBuffer Aeneas.Std.U8) (i : Aeneas.Std.Usize)
    (h : i.val + 16 ≤ b.val.length) :
    aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_loadu_src b i
    ⦃ (r : Aeneas.Std.Array Aeneas.Std.U8 16#usize) =>
      r.val = ((b.val.src).val.drop i.val).take 16 ⦄ := by
  unfold aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_loadu_src
  exact InPlaceOrDisjointBuffer.loadu_si128_src.spec b i h

@[step]
theorem InPlaceOrDisjointBuffer.m128_loadu_dst.spec
    (b : common.InPlaceOrDisjointBuffer Aeneas.Std.U8) (i : Aeneas.Std.Usize)
    (h : i.val + 16 ≤ b.val.length) :
    aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_loadu_dst b i
    ⦃ (r : Aeneas.Std.Array Aeneas.Std.U8 16#usize) =>
      r.val = ((b.val.dst).val.drop i.val).take 16 ⦄ := by
  unfold aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_loadu_dst
  exact InPlaceOrDisjointBuffer.loadu_si128_dst.spec b i h

@[step]
theorem InPlaceOrDisjointBuffer.m128_storeu.spec
    (b : common.InPlaceOrDisjointBuffer Aeneas.Std.U8) (i : Aeneas.Std.Usize)
    (v : Aeneas.Std.Array Aeneas.Std.U8 16#usize)
    (h : i.val + 16 ≤ b.val.length) :
    aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_storeu b i v
    ⦃ b' back =>
      (b'.val.dst).val = List.setSlice! (b.val.dst).val i.val v.val ∧
      b'.val = b.val.setDst b'.val.dst ∧
      (∀ b'' : common.InPlaceOrDisjointBuffer Aeneas.Std.U8,
        (back b'').val = b''.val) ⦄ := by
  unfold aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_storeu
  exact InPlaceOrDisjointBuffer.storeu_si128.spec b i v h

end symcrust.aesgcm
