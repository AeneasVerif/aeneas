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
import Symcrust.Code.Funs
import Symcrust.Properties.Aes.Xmm.Bridge

open Aeneas Aeneas.Std Result

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

/-- **Abstraction function.**  Maps the opaque Aeneas buffer to its high-level view. -/
axiom common.InPlaceOrDisjointBuffer.val {T : Type} :
    common.InPlaceOrDisjointBuffer T → _root_.InPlaceOrDisjointBuffer T

open InPlaceOrDisjointBuffer

namespace symcrust.aesgcm

/-! ## Accessors -/

/-- `len` returns the common length of the two sides. -/
@[step]
axiom InPlaceOrDisjointBuffer.len.spec {T : Type}
    (b : common.InPlaceOrDisjointBuffer T) :
    common.InPlaceOrDisjointBuffer.len b
    ⦃ n => n.val = b.val.length ⦄

/-- `src` returns the source side. -/
@[step]
axiom InPlaceOrDisjointBuffer.src.spec {T : Type}
    (b : common.InPlaceOrDisjointBuffer T) :
    common.InPlaceOrDisjointBuffer.src b
    ⦃ s => s = b.val.src ⦄

/-- `dst` returns the destination side plus two backward functions:
    - `back1` updates the destination buffer
    - `back2` propagates mutations of the enclosing `&mut self` (there are none,
      so this is the identity) -/
@[step]
axiom InPlaceOrDisjointBuffer.dst.spec {T : Type}
    (b : common.InPlaceOrDisjointBuffer T) :
    common.InPlaceOrDisjointBuffer.dst b
    ⦃ s back1 back2 =>
      s = b.val.dst ∧
      (∀ s' : Slice T, s'.length = b.val.length →
        (back1 s').val = b.val.setDst s') ∧
      (∀ b' : common.InPlaceOrDisjointBuffer T, (back2 b').val = b'.val) ⦄

/-- `new_disjoint_from_slices` builds a disjoint-mode buffer. -/
@[step]
axiom InPlaceOrDisjointBuffer.new_disjoint_from_slices.spec {T : Type}
    (src dst : Slice T) (h_len : src.length = dst.length) :
    common.InPlaceOrDisjointBuffer.new_disjoint_from_slices src dst
    ⦃ buf back =>
      buf.val = .disjoint src dst h_len ∧
      (∀ b' : common.InPlaceOrDisjointBuffer T, back b' = b'.val.dst) ⦄

/-! ## SIMD accessors -/

/-- `loadu_si128_src b i` reads the 16 bytes of the source side at offset `i`. -/
@[step]
axiom InPlaceOrDisjointBuffer.loadu_si128_src.spec
    (b : common.InPlaceOrDisjointBuffer Std.U8) (i : Std.Usize)
    (h : i.val + 16 ≤ b.val.length) :
    common.InPlaceOrDisjointBuffer.loadu_si128_src b i
    ⦃ (r : core.core_arch.x86.__m128i) =>
      r.val = ((b.val.src).val.drop i.val).take 16 ⦄

/-- `loadu_si128_dst b i` reads the 16 bytes of the destination side at offset `i`. -/
@[step]
axiom InPlaceOrDisjointBuffer.loadu_si128_dst.spec
    (b : common.InPlaceOrDisjointBuffer Std.U8) (i : Std.Usize)
    (h : i.val + 16 ≤ b.val.length) :
    common.InPlaceOrDisjointBuffer.loadu_si128_dst b i
    ⦃ (r : core.core_arch.x86.__m128i) =>
      r.val = ((b.val.dst).val.drop i.val).take 16 ⦄

/-- `storeu_si128 b i v` splices the 16 bytes of `v` into the destination side. -/
@[step]
axiom InPlaceOrDisjointBuffer.storeu_si128.spec
    (b : common.InPlaceOrDisjointBuffer Std.U8) (i : Std.Usize)
    (v : core.core_arch.x86.__m128i) (h : i.val + 16 ≤ b.val.length) :
    common.InPlaceOrDisjointBuffer.storeu_si128 b i v
    ⦃ b' back =>
      (b'.val.dst).val = List.setSlice! (b.val.dst).val i.val v.val ∧
      b'.val = b.val.setDst b'.val.dst ∧
      (∀ b'' : common.InPlaceOrDisjointBuffer Std.U8, (back b'').val = b''.val) ⦄

/-! ## The `aes_xmm` `u8` shims -/

@[step]
axiom InPlaceOrDisjointBuffer.m128_loadu_src.spec
    (b : common.InPlaceOrDisjointBuffer Std.U8) (i : Std.Usize)
    (h : i.val + 16 ≤ b.val.length) :
    aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_loadu_src b i
    ⦃ (r : Std.Array Std.U8 16#usize) =>
      r.val = ((b.val.src).val.drop i.val).take 16 ⦄

@[step]
axiom InPlaceOrDisjointBuffer.m128_loadu_dst.spec
    (b : common.InPlaceOrDisjointBuffer Std.U8) (i : Std.Usize)
    (h : i.val + 16 ≤ b.val.length) :
    aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_loadu_dst b i
    ⦃ (r : Std.Array Std.U8 16#usize) =>
      r.val = ((b.val.dst).val.drop i.val).take 16 ⦄

@[step]
axiom InPlaceOrDisjointBuffer.m128_storeu.spec
    (b : common.InPlaceOrDisjointBuffer Std.U8) (i : Std.Usize)
    (v : Std.Array Std.U8 16#usize) (h : i.val + 16 ≤ b.val.length) :
    aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_storeu b i v
    ⦃ b' back =>
      (b'.val.dst).val = List.setSlice! (b.val.dst).val i.val v.val ∧
      b'.val = b.val.setDst b'.val.dst ∧
      (∀ b'' : common.InPlaceOrDisjointBuffer Std.U8, (back b'').val = b''.val) ⦄

end symcrust.aesgcm
