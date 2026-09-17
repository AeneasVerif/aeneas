import SepLogic.MutableData.Buffer
import SepLogic.MutableData.Ptr
import Aeneas.Std.Array.Array
import Aeneas.SepLogic.Semantics

/-!
# Buffer prototype with stateful backward functions

This is a hand-written simulation of the *future* extracted interface, not a
claim that today's Aeneas extractor emits these signatures. The carrier really
contains pointers: the first part defines its heap interpretation. Functional
slices enter through materialization and leave through stateful backward calls.
There is no heap-independent `common.InPlaceOrDisjointBuffer.val`.

Start with `Clients.replaceInPlace` for a mutable-slice borrow, or
`Clients.blockDisjoint` for the AES-style path. Both begin with functional
slices and finish by calling the constructor's stateful backward function.

| Boundary | Current backward result | Prototype backward result |
|---|---|---|
| Slice constructor | `B -> Slice T` | `B -> Result (Slice T)` |
| Array constructor | `B -> Array T N` | `B -> Result (Array T N)` |
| Mutable `dst()` view | `Slice T -> B` | `Slice T -> Result B` |
| Enclosing `&mut self` | `B -> B` | `B -> Result B` |

## Intended integration destinations

All paths below are relative to `SymCRust/lean/`.

* `SepLogic.Examples.InPlaceOrDisjointBuffer`: the low-level pointer carrier
  and operations, destined for `Symcrust/Models/InPlaceOrDisjointBuffer.lean`.
  Their ghost state, ownership assertions and proofs belong in the buffer
  properties file below.
* `Memory` helpers: upstream Aeneas `SepLogic/MutableData/`; until upstreamed,
  a leaf `Symcrust/Models/BufferMemory.lean` importing only the heap library.
* `BufferState`, its functions and ownership lemmas:
  `Symcrust/Properties/Common/InPlaceOrDisjointBuffer.lean` (new).
* The `common.InPlaceOrDisjointBuffer` carrier:
  `Symcrust/Code/TypesExternal.lean`, importing the leaf pointer model.
* `common.InPlaceOrDisjointBuffer` operations and `aes.aes_xmm` shims:
  `Symcrust/Code/FunsExternal.lean`. Their accompanying `.spec` theorems belong
  in the properties file above, replacing the old buffer axioms.
* `Clients`: examples of the future generated `Symcrust/Code/Funs.lean` call
  shape, with their proofs in `Symcrust/Properties/Aes/Gcm/`.

The sections are interleaved here to keep each implementation beside its proof;
the code/model layer must not import the properties layer.

Scope: the generic constructors and slice accessors, plus the actual 16-byte
`u8` SIMD accesses used by AES. Generic `T`-to-byte reinterpretation is NOT
modeled with `unsafeCast` or an axiom. A future integration must connect these
hand-written operations to Rust extraction and the hardware-intrinsic model.
Logical allocation materializes a borrow; it does not assert that a Rust
constructor calls an allocator, or validate arbitrary incoming FFI pointers.
-/

/-! ## Pointer model and equal-or-disjoint ownership

A port of `InPlaceOrDisjointBuffer<'a, T>` from `SymCRust/src/common.rs`:
a read view and a write view of the same length which are either the same
buffer (in-place) or two disjoint ones.

`EqOrDisj` is the ghost state. The in-place shape owns one range, so writes
are visible to the reader; the disjoint shape owns two separated ranges.
The element-wise operations in this part explain the aliasing behavior.
The generated-code layer below adds functional slices, stateful backward
functions, full 16-byte operations, and pointer-free client contracts.
-/

open Aeneas
open SepLogic
open Aeneas.SepLogic

namespace SepLogic

open Aeneas.Std (Heap Result)

namespace Examples

/-! ## The ghost state -/

/-- Two views of memory that are either the same or separated: the ghost state
of a `src`/`dst` pair. -/
inductive EqOrDisj (α : Type) where
  | equal (value : α)
  | disjoint (leftValue rightValue : α)

/-- What the read view holds. -/
def EqOrDisj.read {α : Type} (relation : EqOrDisj α) : α :=
  match relation with
  | .equal value => value
  | .disjoint leftValue _ => leftValue

/-- What the write view holds. -/
def EqOrDisj.written {α : Type} (relation : EqOrDisj α) : α :=
  match relation with
  | .equal value => value
  | .disjoint _ rightValue => rightValue

/-- Give the write view the contents `value`. -/
def EqOrDisj.write {α : Type} (relation : EqOrDisj α)
    (value : α) : EqOrDisj α :=
  match relation with
  | .equal _ => .equal value
  | .disjoint leftValue _ => .disjoint leftValue value

@[simp] theorem EqOrDisj.written_write {α : Type} (relation : EqOrDisj α)
    (value : α) : (relation.write value).written = value := by
  cases relation <;> rfl

/-- Writing is visible to the reader exactly when the two views are the same:
this single pair of equations is the whole pattern. -/
@[simp] theorem EqOrDisj.read_write_equal {α : Type} (old value : α) :
    ((EqOrDisj.equal old).write value).read = value := rfl

@[simp] theorem EqOrDisj.read_write_disjoint {α : Type}
    (leftValue rightValue value : α) :
    ((EqOrDisj.disjoint leftValue rightValue).write value).read =
      leftValue := rfl

/-! ## Lists

The two list identities a write through one slot of a range needs: it changes
neither what is before the slot nor what is after it. -/

theorem take_set {α : Type} (values : List α) (i : Nat) (value : α) :
    (values.set i value).take i = values.take i := by
  apply List.ext_getElem (by simp)
  intro n h₁ _
  have hn : n < i := by simp at h₁; omega
  simp only [List.getElem_take, List.getElem_set, if_neg (show ¬ i = n by omega)]

theorem drop_set {α : Type} (values : List α) (i : Nat) (value : α) :
    (values.set i value).drop (i + 1) = values.drop (i + 1) := by
  apply List.ext_getElem (by simp)
  intro n _ _
  simp only [List.getElem_drop, List.getElem_set,
    if_neg (show ¬ i = i + 1 + n by omega)]

/-! ## The type -/

/-- `InPlaceOrDisjointBuffer<'a, T>`: a read view, a write view, and the number
of elements both span.  The `PhantomData` lifetime field is erased; a `Ptr`
carries neither a length nor a permission, so `len` and the ownership are
exactly what the Rust pointers leave implicit.

```rust
pub struct InPlaceOrDisjointBuffer<'a, T> {
    src: *const T,
    dst: *mut T,
    len: usize,
    _phantom: PhantomData<&'a mut [T]>,
}
```
-/
structure InPlaceOrDisjointBuffer (α : Type) where
  src : Ptr α
  dst : Ptr α
  len : Nat
  deriving Inhabited

namespace InPlaceOrDisjointBuffer

variable {α : Type}

/-- What the pair owns, in each of its two shapes.  In place, the two views
*are* one buffer and one range is owned; disjoint, two ranges are owned
separately — and `∗` is what makes them non-overlapping, so nothing has to
assume it. -/
def pointsTo (b : InPlaceOrDisjointBuffer α) (state : EqOrDisj (List α)) :
    IProp :=
  match state with
  | .equal values =>
      iprop(⌜b.src = b.dst ∧ values.length = b.len⌝ ∗ b.dst ↦* values)
  | .disjoint srcValues dstValues =>
      iprop(⌜srcValues.length = b.len ∧ dstValues.length = b.len⌝ ∗
        (b.src ↦* srcValues ∗ b.dst ↦* dstValues))

/-! ## Constructors

Building the pair touches no memory: the Rust constructors only reshape what
the caller already owns, and `from_raw_parts` does not even do that.  They are
`Result` actions all the same — in Rust they are calls, so a `do` block mirrors the
Rust and `step` applies their ispecs — and each rests on an entailment, which
is what to use in a proof with no program in it. -/

/-- The value `new_in_place` returns. -/
def mkInPlace (buffer : Buffer α) : InPlaceOrDisjointBuffer α :=
  ⟨buffer.ptr, buffer.ptr, buffer.length⟩

/-- Owning a buffer is owning it in place. -/
theorem mkInPlace_entails (buffer : Buffer α) (values : List α) :
    buffer ↦ values ⊢ (mkInPlace buffer).pointsTo (.equal values) := by
  intro h hPointsTo
  obtain ⟨hLength, hRange⟩ := (sep_pure_l _ _ h).mp hPointsTo
  exact (sep_pure_l _ _ h).mpr ⟨⟨rfl, hLength⟩, hRange⟩

/-- `InPlaceOrDisjointBuffer::new_in_place`.

```rust
pub fn new_in_place(buffer: &'a mut [T]) -> Self {
    let ptr = buffer.as_mut_ptr();
    Self {
        src: ptr as *const T,
        dst: ptr,
        len: buffer.len(),
        _phantom: PhantomData,
    }
}
```
-/
def newInPlace (buffer : Buffer α) : Result (InPlaceOrDisjointBuffer α) :=
  pure (mkInPlace buffer)

@[step]
theorem newInPlace.spec (buffer : Buffer α) (values : List α) :
    ⦃ buffer ↦ values ⦄ newInPlace buffer
      ⦃⇓ b => ⌜b = mkInPlace buffer⌝ ∗ b.pointsTo (.equal values)⦄ :=
  by
  simp only [newInPlace, mkInPlace, pointsTo, Buffer.pointsTo_def]
  step*

/-- The value `new_disjoint` and `new_disjoint_from_slices` return. -/
def mkDisjoint (src dst : Buffer α) : InPlaceOrDisjointBuffer α :=
  ⟨src.ptr, dst.ptr, src.length⟩

/-- Owning two buffers separately is owning them as a disjoint pair.  The
const-generic constructor gets the two lengths equal from its type and the
slice one from an `assert_eq!`; here that equality is a hypothesis, and the
*disjointness* both Rust constructors get from the borrow checker is what `∗`
supplies. -/
theorem mkDisjoint_entails (src dst : Buffer α) (srcValues dstValues : List α)
    (hLength : src.length = dst.length) :
    src ↦ srcValues ∗ dst ↦ dstValues ⊢
      (mkDisjoint src dst).pointsTo (.disjoint srcValues dstValues) := by
  rintro h ⟨h₁, h₂, hCompatible, rfl, hSrc, hDst⟩
  obtain ⟨hSrcLength, hSrcRange⟩ := (sep_pure_l _ _ h₁).mp hSrc
  obtain ⟨hDstLength, hDstRange⟩ := (sep_pure_l _ _ h₂).mp hDst
  exact (sep_pure_l _ _ _).mpr
    ⟨⟨hSrcLength, by simp only [mkDisjoint]; omega⟩,
      h₁, h₂, hCompatible, rfl, hSrcRange, hDstRange⟩

/-- `InPlaceOrDisjointBuffer::new_disjoint` and `new_disjoint_from_slices`.
The first gets the two lengths equal from its type, the second from an
`assert_eq!`; here both are `newDisjoint`, with the equality a hypothesis.

```rust
pub fn new_disjoint<const N: usize>(src: &'a [T; N], dst: &'a mut [T; N]) -> Self {
    Self { src: src.as_ptr(), dst: dst.as_mut_ptr(), len: N, _phantom: PhantomData }
}

pub fn new_disjoint_from_slices(src: &'a [T], dst: &'a mut [T]) -> Self {
    assert_eq!(src.len(), dst.len());
    Self {
        src: src.as_ptr(),
        dst: dst.as_mut_ptr(),
        len: src.len(),
        _phantom: PhantomData,
    }
}
```
-/
def newDisjoint (src dst : Buffer α) : Result (InPlaceOrDisjointBuffer α) :=
  pure (mkDisjoint src dst)

@[step]
theorem newDisjoint.spec (src dst : Buffer α) (srcValues dstValues : List α)
    (hLength : src.length = dst.length) :
    ⦃ src ↦ srcValues ∗ dst ↦ dstValues ⦄ newDisjoint src dst
      ⦃⇓ b => ⌜b = mkDisjoint src dst⌝ ∗
        b.pointsTo (.disjoint srcValues dstValues)⦄ :=
  by
  simp only [newDisjoint, mkDisjoint, pointsTo, Buffer.pointsTo_def, hLength]
  step*

/-- The value `from_raw_parts` returns. -/
def mkFromRawParts (src dst : Ptr α) (len : Nat) : InPlaceOrDisjointBuffer α :=
  ⟨src, dst, len⟩

/-- `InPlaceOrDisjointBuffer::from_raw_parts`.  It is `unsafe` in Rust because
nothing checks its contract; here it owns nothing and promises nothing, so its
ispec starts from `emp`.  The contract *is* the `pointsTo` a caller has to
produce, and the frame rule is what carries that across the call.

```rust
/// # Safety
/// - `src` must be valid for accesses of `len` elements
/// - `dst` must be valid for accesses of `len` elements
/// - `src` and `dst` must be either equal or completely disjoint
/// - When `src` and `dst` are disjoint, they must have the same length
/// - Both `src` and `dst` must be valid for the lifetime of the returned buffer
pub unsafe fn from_raw_parts(src: *const T, dst: *mut T, len: usize) -> Self {
    Self { src, dst, len, _phantom: PhantomData }
}
```
-/
def fromRawParts (src dst : Ptr α) (len : Nat) :
    Result (InPlaceOrDisjointBuffer α) :=
  pure (mkFromRawParts src dst len)

@[step]
theorem fromRawParts.spec (src dst : Ptr α) (len : Nat) :
    ⦃ emp ⦄ fromRawParts src dst len
      ⦃⇓ b => ⌜b = mkFromRawParts src dst len⌝⦄ :=
  by
  simp only [fromRawParts, mkFromRawParts]
  step*

/-- The usable raw-parts interface transports ownership supplied by the
caller. Constructing a record from arbitrary pointers never creates a valid
range or establishes disjointness. This belongs in the buffer properties file,
not a new FFI axiom. -/
theorem fromRawParts.spec_owned (src dst : Ptr α) (len : Nat)
    (state : EqOrDisj (List α)) :
    ⦃ (mkFromRawParts src dst len).pointsTo state ⦄ fromRawParts src dst len
      ⦃⇓ b => ⌜b = mkFromRawParts src dst len⌝ ∗ b.pointsTo state⦄ := by
  unfold fromRawParts
  step*

/-! ## Views -/

/-- `len`.

```rust
pub fn len(&self) -> usize {
    self.len
}
```
-/
def length (b : InPlaceOrDisjointBuffer α) : Result Nat :=
  pure b.len

@[step]
theorem length.spec (b : InPlaceOrDisjointBuffer α) :
    ⦃ emp ⦄ b.length ⦃⇓ result => ⌜result = b.len⌝⦄ := by
  unfold length
  step*

/-- The value `srcSlice` returns. -/
def mkSrcSlice (b : InPlaceOrDisjointBuffer α) : Buffer α :=
  ⟨b.src.base, b.src.offset, b.len⟩

/-- `src`: the read view as a slice.

```rust
pub fn src(&self) -> &[T] {
    unsafe { core::slice::from_raw_parts(self.src, self.len) }
}
```
-/
def srcSlice (b : InPlaceOrDisjointBuffer α) : Result (Buffer α) :=
  pure (mkSrcSlice b)

@[step]
theorem srcSlice.spec (b : InPlaceOrDisjointBuffer α) :
    ⦃ emp ⦄ b.srcSlice
      ⦃⇓ result => ⌜result = mkSrcSlice b⌝⦄ := by
  unfold srcSlice
  step*

/-- The value `dstSlice` returns. -/
def mkDstSlice (b : InPlaceOrDisjointBuffer α) : Buffer α :=
  ⟨b.dst.base, b.dst.offset, b.len⟩

/-- `dst`: the write view as a mutable slice.

```rust
pub fn dst(&mut self) -> &mut [T] {
    unsafe { core::slice::from_raw_parts_mut(self.dst, self.len) }
}
```
-/
def dstSlice (b : InPlaceOrDisjointBuffer α) : Result (Buffer α) :=
  pure (mkDstSlice b)

@[step]
theorem dstSlice.spec (b : InPlaceOrDisjointBuffer α) :
    ⦃ emp ⦄ b.dstSlice
      ⦃⇓ result => ⌜result = mkDstSlice b⌝⦄ := by
  unfold dstSlice
  step*

@[simp] theorem ptr_srcSlice (b : InPlaceOrDisjointBuffer α) :
    (mkSrcSlice b).ptr = b.src := rfl

@[simp] theorem ptr_dstSlice (b : InPlaceOrDisjointBuffer α) :
    (mkDstSlice b).ptr = b.dst := rfl

/-- In place the two views are literally the same slice: this is why `dst`
takes `&mut self` in Rust, and why one range is all the pair owns. -/
theorem srcSlice_eq_dstSlice (b : InPlaceOrDisjointBuffer α)
    (hSame : b.src = b.dst) : mkSrcSlice b = mkDstSlice b := by
  simp [mkSrcSlice, mkDstSlice, hSame]

/-- In place, that one slice is what the pair owns. -/
theorem pointsTo_dstSlice_equal (b : InPlaceOrDisjointBuffer α)
    (values : List α) :
    b.pointsTo (.equal values) ⊢ mkDstSlice b ↦ values := by
  intro h hPointsTo
  obtain ⟨⟨-, hLength⟩, hRange⟩ := (sep_pure_l _ _ h).mp hPointsTo
  exact (sep_pure_l _ _ h).mpr ⟨hLength, hRange⟩

/-- `src()` hands back the read view. -/
theorem pointsTo_srcSlice_disjoint (b : InPlaceOrDisjointBuffer α)
    (srcValues dstValues : List α) :
    b.pointsTo (.disjoint srcValues dstValues) ⊢
      mkSrcSlice b ↦ srcValues := by
  intro h hPointsTo
  obtain ⟨⟨hLength, -⟩, hRanges⟩ := (sep_pure_l _ _ h).mp hPointsTo
  obtain ⟨h₁, h₂, hCompatible, rfl, hSrc, -⟩ := hRanges
  exact (sep_pure_l _ _ _).mpr
    ⟨hLength, ((mkSrcSlice b).ptr ↦* srcValues).up_closed hSrc
      (Heap.Sub.union_left hCompatible)⟩

/-- `dst()` hands back the write view, and the range it owns is the one the
pair owned. -/
theorem pointsTo_dstSlice_disjoint (b : InPlaceOrDisjointBuffer α)
    (srcValues dstValues : List α) :
    b.pointsTo (.disjoint srcValues dstValues) ⊢
      mkDstSlice b ↦ dstValues := by
  intro h hPointsTo
  obtain ⟨⟨-, hLength⟩, hRanges⟩ := (sep_pure_l _ _ h).mp hPointsTo
  obtain ⟨h₁, h₂, hCompatible, rfl, -, hDst⟩ := hRanges
  exact (sep_pure_l _ _ _).mpr
    ⟨hLength, ((mkDstSlice b).ptr ↦* dstValues).up_closed hDst
      (Heap.Sub.union_right hCompatible)⟩

/-! ## Element access

`loadu_si128_src`, `loadu_si128_dst` and `storeu_si128`, one element at a time.
None of them has a precondition: an offset out of the range the caller owns
simply has no provable ispec.

Each has two specifications: the slot-level one here, which is the primitive,
and the `spec_state` further down, which is what the interface means.  Only the
latter is registered with `step`, because that is what a client of the type
owns; the slot-level ones are reached by unfolding to `read` and `update`,
whose own specifications the automation then uses.  Registering both would make
`step` ambiguous. -/

/-- `loadu_si128_src`, one element wide.

```rust
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "sse2")]
pub unsafe fn loadu_si128_src(&self, offset: usize) -> __m128i {
    debug_assert!(offset * size_of::<T>() + 16 <= self.len() * size_of::<T>());
    _mm_loadu_si128(self.src.add(offset) as *const __m128i)
}
```
-/
def loadSrc (b : InPlaceOrDisjointBuffer α) (i : Nat) : Result α :=
  read (b.src.add i)

theorem loadSrc.spec (b : InPlaceOrDisjointBuffer α) (i : Nat) (value : α) :
    ⦃ (b.src.add i) ↦ value ⦄ b.loadSrc i
      ⦃⇓ result => ⌜result = value⌝ ∗ (b.src.add i) ↦ value⦄ :=
  read.spec (b.src.add i) value

/-- `loadu_si128_dst`, one element wide.  Reading back from the destination
breaks the read-once/write-once rule on purpose: AES-GCM needs it.

```rust
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "sse2")]
pub unsafe fn loadu_si128_dst(&self, offset: usize) -> __m128i {
    debug_assert!(offset * size_of::<T>() + 16 <= self.len() * size_of::<T>());
    _mm_loadu_si128(self.dst.add(offset) as *const __m128i)
}
```
-/
def loadDst (b : InPlaceOrDisjointBuffer α) (i : Nat) : Result α :=
  read (b.dst.add i)

theorem loadDst.spec (b : InPlaceOrDisjointBuffer α) (i : Nat) (value : α) :
    ⦃ (b.dst.add i) ↦ value ⦄ b.loadDst i
      ⦃⇓ result => ⌜result = value⌝ ∗ (b.dst.add i) ↦ value⦄ :=
  read.spec (b.dst.add i) value

/-- `storeu_si128`, one element wide.

```rust
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "sse2")]
pub unsafe fn storeu_si128(&mut self, offset: usize, value: __m128i) {
    debug_assert!(offset * size_of::<T>() + 16 <= self.len() * size_of::<T>());
    _mm_storeu_si128(self.dst.add(offset) as *mut __m128i, value)
}
```
-/
def store (b : InPlaceOrDisjointBuffer α) (i : Nat) (value : α) : Result Unit :=
  update (b.dst.add i) value

theorem store.spec (b : InPlaceOrDisjointBuffer α) (i : Nat)
    (oldValue value : α) :
    ⦃ (b.dst.add i) ↦ oldValue ⦄ b.store i value
      ⦃⇓ (b.dst.add i) ↦ value⦄ :=
  update.spec (b.dst.add i) oldValue value

/-! ## The interface against its ghost state -/

/-- Reading through the *read* view returns what `EqOrDisj.read` says: in
place, the value last written; disjoint, the untouched source value. -/
@[step]
theorem loadSrc.spec_state (b : InPlaceOrDisjointBuffer α)
    (state : EqOrDisj (List α)) (i : Nat) (value : α)
    (hIndex : state.read[i]? = some value) :
    ⦃ b.pointsTo state ⦄ b.loadSrc i
      ⦃⇓ result => ⌜result = value⌝ ∗ b.pointsTo state⦄ := by
  cases state with
  | equal values =>
      obtain ⟨hLt, hGet⟩ :=
        List.getElem?_eq_some_iff.mp (show values[i]? = some value from hIndex)
      simp only [pointsTo]
      iintro ⟨hSame, hLength⟩
      unfold loadSrc
      rw [hSame, Ptr.pointsToRange_eq_take_get_drop hLt, hGet]
      step*
  | disjoint srcValues dstValues =>
      obtain ⟨hLt, hGet⟩ :=
        List.getElem?_eq_some_iff.mp
          (show srcValues[i]? = some value from hIndex)
      simp only [pointsTo]
      unfold loadSrc
      rw [Ptr.pointsToRange_eq_take_get_drop hLt, hGet]
      step*

/-- Reading through the write view returns what was written there. -/
@[step]
theorem loadDst.spec_state (b : InPlaceOrDisjointBuffer α)
    (state : EqOrDisj (List α)) (i : Nat) (value : α)
    (hIndex : state.written[i]? = some value) :
    ⦃ b.pointsTo state ⦄ b.loadDst i
      ⦃⇓ result => ⌜result = value⌝ ∗ b.pointsTo state⦄ := by
  cases state with
  | equal values =>
      obtain ⟨hLt, hGet⟩ :=
        List.getElem?_eq_some_iff.mp (show values[i]? = some value from hIndex)
      simp only [pointsTo]
      unfold loadDst
      rw [Ptr.pointsToRange_eq_take_get_drop hLt, hGet]
      step*
  | disjoint srcValues dstValues =>
      obtain ⟨hLt, hGet⟩ :=
        List.getElem?_eq_some_iff.mp
          (show dstValues[i]? = some value from hIndex)
      simp only [pointsTo]
      unfold loadDst
      rw [Ptr.pointsToRange_eq_take_get_drop hLt, hGet]
      step*

/-- Writing through the write view.  Whether the reader sees it is exactly what
`EqOrDisj.write` says. -/
@[step]
theorem store.spec_state (b : InPlaceOrDisjointBuffer α)
    (state : EqOrDisj (List α)) (i : Nat) (value : α)
    (hIndex : i < state.written.length) :
    ⦃ b.pointsTo state ⦄ b.store i value
      ⦃⇓ b.pointsTo (state.write (state.written.set i value))⦄ := by
  cases state with
  | equal values =>
      have hLt : i < values.length := hIndex
      simp only [EqOrDisj.write, EqOrDisj.written, pointsTo, List.length_set]
      unfold store
      rw [Ptr.pointsToRange_eq_take_get_drop hLt,
        Ptr.pointsToRange_eq_take_get_drop
          (show i < (values.set i value).length by simpa using hLt),
        take_set, drop_set, List.getElem_set_self]
      step*
  | disjoint srcValues dstValues =>
      have hLt : i < dstValues.length := hIndex
      simp only [EqOrDisj.write, EqOrDisj.written, pointsTo, List.length_set]
      unfold store
      rw [Ptr.pointsToRange_eq_take_get_drop hLt,
        Ptr.pointsToRange_eq_take_get_drop
          (show i < (dstValues.set i value).length by simpa using hLt),
        take_set, drop_set, List.getElem_set_self]
      step*

/-! ## What the type is for

Writing and then reading back through the *read* view: in place the write is
seen, disjoint it is not.  The disjoint case is proved by the frame rule alone
— separation is what says the two views do not overlap. -/

def storeThenLoadSrc (b : InPlaceOrDisjointBuffer α) (i : Nat) (value : α) :
    Result α := do
  b.store i value
  b.loadSrc i

theorem storeThenLoadSrc.spec_inPlace (b : InPlaceOrDisjointBuffer α)
    (i : Nat) (oldValue value : α) (hSame : b.src = b.dst) :
    ⦃ (b.dst.add i) ↦ oldValue ⦄ b.storeThenLoadSrc i value
      ⦃⇓ result => ⌜result = value⌝ ∗ (b.dst.add i) ↦ value⦄ := by
  unfold storeThenLoadSrc store loadSrc
  rw [hSame]
  step*

theorem storeThenLoadSrc.spec_disjoint (b : InPlaceOrDisjointBuffer α)
    (i : Nat) (srcValue dstValue value : α) :
    ⦃ (b.src.add i) ↦ srcValue ∗ (b.dst.add i) ↦ dstValue ⦄
      b.storeThenLoadSrc i value
      ⦃⇓ result => ⌜result = srcValue⌝ ∗
        ((b.src.add i) ↦ srcValue ∗ (b.dst.add i) ↦ value)⦄ := by
  unfold storeThenLoadSrc store loadSrc
  step*

/-- A client that mirrors the Rust: build the pair in place, then write through
it.  The constructor is a call like any other, so `step` goes through its
ispec and hands the ownership on. -/
def inPlaceWrite (buffer : Buffer α) (i : Nat) (value : α) : Result Unit := do
  let b ← newInPlace buffer
  b.store i value

theorem inPlaceWrite.spec (buffer : Buffer α) (values : List α) (i : Nat)
    (value : α) (hIndex : i < values.length) :
    ⦃ buffer ↦ values ⦄ inPlaceWrite buffer i value
      ⦃⇓ (mkInPlace buffer).pointsTo (.equal (values.set i value))⦄ := by
  unfold inPlaceWrite
  step*
  · exact hIndex

end InPlaceOrDisjointBuffer

end Examples

end SepLogic

/-! ## Stateful backward functions -/

open Aeneas
open Aeneas.Std (Result Slice Usize U8)
open SepLogic
open Aeneas.SepLogic

namespace BufferModel

/-! Runtime aliases and view functions: leaf
`Symcrust/Models/InPlaceOrDisjointBuffer.lean`, imported by the external code.
Keep these separate from `BufferState` and its properties when porting. -/

abbrev RawBuffer := SepLogic.Examples.InPlaceOrDisjointBuffer
abbrev EqOrDisj := SepLogic.Examples.EqOrDisj

abbrev srcView (b : RawBuffer α) := SepLogic.Examples.InPlaceOrDisjointBuffer.mkSrcSlice b
abbrev dstView (b : RawBuffer α) := SepLogic.Examples.InPlaceOrDisjointBuffer.mkDstSlice b
abbrev srcPtr (b : RawBuffer α) := (srcView b).ptr
abbrev dstPtr (b : RawBuffer α) := (dstView b).ptr

/-! ## Heap helpers

Destination: the upstream heap library, or the leaf
`Symcrust/Models/BufferMemory.lean`. These manipulate the same pointers;
they never replace an existing range with a fresh allocation.
-/

namespace Memory

def readRange (p : Ptr α) : Nat → Result (List α)
  | 0 => pure []
  | n + 1 => do
    let value ← read p
    let rest ← readRange (p.add 1) n
    pure (value :: rest)

@[step]
theorem readRange.spec (p : Ptr α) (values : List α) :
    ⦃ p ↦* values ⦄ readRange p values.length
      ⦃⇓ result => ⌜result = values⌝ ∗ p ↦* values⦄ := by
  induction values generalizing p
  · simp only [List.length_nil, readRange, Ptr.pointsToRange_nil]
    step*
  · rename_i value rest ih
    simp only [List.length_cons, readRange, Ptr.pointsToRange_cons]
    step*

def writeRange (p : Ptr α) : List α → Result Unit
  | [] => pure ()
  | value :: rest => do
    update p value
    writeRange (p.add 1) rest

@[step]
theorem writeRange.spec (p : Ptr α) (old values : List α)
    (hLength : old.length = values.length) :
    ⦃ p ↦* old ⦄ writeRange p values ⦃⇓ p ↦* values⦄ := by
  induction values generalizing p old
  · obtain rfl : old = [] := by simpa using hLength
    simp only [writeRange, Ptr.pointsToRange_nil]
    step*
  · rename_i value rest ih
    obtain ⟨previous, oldRest, rfl⟩ : ∃ x xs, old = x :: xs := by
      cases old
      · simp at hLength
      · exact ⟨_, _, rfl⟩
    have hRest : oldRest.length = rest.length := by simpa using hLength
    simp only [writeRange, Ptr.pointsToRange_cons]
    step*

def toSlice (values : List α) : Result (Slice α) :=
  if h : values.length ≤ Usize.max then
    pure (Slice.from values h)
  else
    Result.fail .maximumSizeExceeded

@[step]
theorem toSlice.spec (s : Slice α) :
    ⦃ emp ⦄ toSlice s.val ⦃⇓ result => ⌜result = s⌝⦄ := by
  simp only [toSlice, s.property, ↓reduceDIte]
  step*

def readSlice (b : Buffer α) : Result (Slice α) := do
  let values ← readRange b.ptr b.length
  toSlice values

@[step]
theorem readSlice.spec (b : Buffer α) (s : Slice α) :
    ⦃ b ↦ s.val ⦄ readSlice b ⦃⇓ result => ⌜result = s⌝ ∗ b ↦ s.val⦄ := by
  simp only [Buffer.pointsTo_def]
  iintro hLength
  unfold readSlice
  rw [← hLength]
  step with readRange.spec b.ptr s.val as ⟨values, hValues⟩
  subst values
  step*

def writeSlice (b : Buffer α) (s : Slice α) : Result Unit :=
  if s.length = b.length then writeRange b.ptr s.val
  else Result.fail .assertionFailure

@[step]
theorem writeSlice.spec (b : Buffer α) (old s : Slice α)
    (hLength : s.length = old.length) :
    ⦃ b ↦ old.val ⦄ writeSlice b s ⦃⇓ b ↦ s.val⦄ := by
  simp only [Buffer.pointsTo_def]
  iintro hOld
  have hNew : s.length = b.length := hLength.trans hOld
  simp only [writeSlice, hNew, ↓reduceIte]
  step*
  · exact hLength.symm

@[step]
theorem end_mut_to_raw.spec (original s : Slice α) (b : Buffer α)
    (hLength : s.length = original.length) :
    ⦃ b ↦ s.val ⦄ Buffer.end_mut_to_raw original b
      ⦃⇓ result => ⌜result = s⌝⦄ := by
  apply Aeneas.Std.WP.ispec_conseq (Buffer.end_mut_to_raw.spec original b s.val)
    (entails_refl _)
  intro result
  iintro hResult
  apply (entails_emp_ipure_iff _).mpr
  apply Slice.ext
  have hVal : s.val.length = original.val.length := hLength
  simpa [List.setSlice!, ← hVal] using hResult

end Memory

/-! ## Functional specification vocabulary

Destination: `Symcrust/Properties/Common/InPlaceOrDisjointBuffer.lean`.
`BufferState` is ghost data, NOT the representation of the runtime buffer.
Unlike the former `.val` axiom, `owns b state` explicitly depends on the heap.
-/

inductive BufferState (α : Type) where
  | equal (value : Slice α)
  | disjoint (src dst : Slice α) (hLength : src.length = dst.length)

namespace BufferState

@[simp, agrind =]
def src : BufferState α → Slice α
  | .equal s => s
  | .disjoint s _ _ => s

@[simp, agrind =]
def dst : BufferState α → Slice α
  | .equal s => s
  | .disjoint _ d _ => d

def toLists : BufferState α → EqOrDisj (List α)
  | .equal s => .equal s.val
  | .disjoint s d _ => .disjoint s.val d.val

@[simp, agrind =]
def setDst (state : BufferState α) (dst : Slice α)
    (hLength : dst.length = state.dst.length) : BufferState α :=
  match state with
  | .equal _ => .equal dst
  | .disjoint src _ h => .disjoint src dst (h.trans hLength.symm)

@[simp]
theorem src_length (state : BufferState α) : state.src.length = state.dst.length := by
  cases state
  · rfl
  · assumption

@[simp]
theorem dst_setDst (state : BufferState α) (s : Slice α) (hLength) :
    (state.setDst s hLength).dst = s := by
  cases state <;> rfl

end BufferState

def owns (b : RawBuffer α) (state : BufferState α) : IProp :=
  b.pointsTo state.toLists

theorem owns_equal (b : RawBuffer α) (s : Slice α) :
    owns b (.equal s) =
      iprop(⌜b.src = b.dst⌝ ∗ dstView b ↦ s.val) := by
  simp only [owns, SepLogic.Examples.InPlaceOrDisjointBuffer.pointsTo, BufferState.toLists, dstView,
    Buffer.pointsTo_def]
  apply bientails_eq
  constructor
  · intro heap h
    obtain ⟨⟨hs, hl⟩, hr⟩ := (sep_pure_l _ _ heap).mp h
    exact (sep_pure_l _ _ heap).mpr ⟨hs, (sep_pure_l _ _ heap).mpr ⟨hl, hr⟩⟩
  · intro heap h
    obtain ⟨hs, h⟩ := (sep_pure_l _ _ heap).mp h
    obtain ⟨hl, hr⟩ := (sep_pure_l _ _ heap).mp h
    exact (sep_pure_l _ _ heap).mpr ⟨⟨hs, hl⟩, hr⟩

theorem owns_disjoint (b : RawBuffer α) (s d : Slice α) (hLength) :
    owns b (.disjoint s d hLength) =
      iprop(srcView b ↦ s.val ∗ dstView b ↦ d.val) := by
  simp only [owns, SepLogic.Examples.InPlaceOrDisjointBuffer.pointsTo, BufferState.toLists,
    srcView, dstView, Buffer.pointsTo_def]
  apply bientails_eq
  constructor
  · intro heap h
    obtain ⟨⟨hs, hd⟩, hRanges⟩ := (sep_pure_l _ _ heap).mp h
    obtain ⟨h₁, h₂, hc, rfl, hSrc, hDst⟩ := hRanges
    exact ⟨h₁, h₂, hc, rfl,
      (sep_pure_l _ _ _).mpr ⟨hs, hSrc⟩,
      (sep_pure_l _ _ _).mpr ⟨hd, hDst⟩⟩
  · rintro heap ⟨h₁, h₂, hc, rfl, hSrc, hDst⟩
    obtain ⟨hs, hSrc⟩ := (sep_pure_l _ _ _).mp hSrc
    obtain ⟨hd, hDst⟩ := (sep_pure_l _ _ _).mp hDst
    exact (sep_pure_l _ _ _).mpr ⟨⟨hs, hd⟩, h₁, h₂, hc, rfl, hSrc, hDst⟩

end BufferModel

/-! ## Runtime carrier

Destination: `Symcrust/Code/TypesExternal.lean`. The alias exposes the pointer
record defined above, NOT `BufferState`. No contents are stored here.
-/

namespace common

abbrev InPlaceOrDisjointBuffer := SepLogic.Examples.InPlaceOrDisjointBuffer

end common

open BufferModel

namespace common.InPlaceOrDisjointBuffer

/-! ## Constructors and lifetime-ending backward functions

Definitions: `Symcrust/Code/FunsExternal.lean`.
Proofs: `Symcrust/Properties/Common/InPlaceOrDisjointBuffer.lean`.

The constructor chooses the aliasing mode. Finishing an in-place lifetime
consumes ONE range. Finishing a disjoint lifetime consumes the destination
and releases the separate logical source allocation. It never frees either
range twice, and does not return a pointer that outlives the materialization.
-/

def finish_in_place (original : Slice T) (b : common.InPlaceOrDisjointBuffer T) :
    Result (Slice T) :=
  Buffer.end_mut_to_raw original (dstView b)

@[step]
theorem finish_in_place.spec (original current : Slice T)
    (b : common.InPlaceOrDisjointBuffer T)
    (hLength : current.length = original.length) :
    ⦃ owns b (.equal current) ⦄ finish_in_place original b
      ⦃⇓ result => ⌜result = current⌝⦄ := by
  rw [owns_equal]
  iintro hSame
  exact Memory.end_mut_to_raw.spec original current (dstView b) hLength

def finish_disjoint (original : Slice T) (b : common.InPlaceOrDisjointBuffer T) :
    Result (Slice T) := do
  let result ← Buffer.end_mut_to_raw original (dstView b)
  Buffer.free (srcView b)
  pure result

@[step]
theorem finish_disjoint.spec (original src current : Slice T)
    (b : common.InPlaceOrDisjointBuffer T)
    (hPair : src.length = current.length)
    (hLength : current.length = original.length) :
    ⦃ owns b (.disjoint src current hPair) ⦄ finish_disjoint original b
      ⦃⇓ result => ⌜result = current⌝⦄ := by
  rw [owns_disjoint]
  unfold finish_disjoint
  step with Memory.end_mut_to_raw.spec original current (dstView b) hLength
  step*

def new_in_place (s : Slice T) :
    Result (common.InPlaceOrDisjointBuffer T ×
      (common.InPlaceOrDisjointBuffer T → Result (Slice T))) :=
  Aeneas.Std.bind (Buffer.mut_to_raw s) fun memory =>
  Aeneas.Std.bind (SepLogic.Examples.InPlaceOrDisjointBuffer.newInPlace memory) fun b =>
  pure (b, finish_in_place s)

@[step]
theorem new_in_place.spec (s : Slice T) :
    ⦃ emp ⦄ new_in_place s
      ⦃⇓ b back =>
        owns b (.equal s) ∗
        ⌜∀ current : Slice T, current.length = s.length →
          ⦃ owns b (.equal current) ⦄ back b
            ⦃⇓ result => ⌜result = current⌝⦄⌝⦄ := by
  unfold new_in_place
  simp only [BufferModel.owns, BufferState.toLists]
  step*
  · rw [sep_comm_eq]
    apply pure_sep_intro
    intro current hLength
    exact finish_in_place.spec s current _ hLength

def new_disjoint_from_slices (src dst : Slice T) :
    Result (common.InPlaceOrDisjointBuffer T ×
      (common.InPlaceOrDisjointBuffer T → Result (Slice T))) :=
  if src.length = dst.length then
    Aeneas.Std.bind (Buffer.mut_to_raw src) fun srcMemory =>
    Aeneas.Std.bind (Buffer.mut_to_raw dst) fun dstMemory =>
    Aeneas.Std.bind
      (SepLogic.Examples.InPlaceOrDisjointBuffer.newDisjoint srcMemory dstMemory) fun b =>
    pure (b, finish_disjoint dst)
  else
    Result.fail .assertionFailure

@[step]
theorem new_disjoint_from_slices.spec (src dst : Slice T)
    (hLength : src.length = dst.length) :
    ⦃ emp ⦄ new_disjoint_from_slices src dst
      ⦃⇓ b back =>
        owns b (.disjoint src dst hLength) ∗
        ⌜∀ current : Slice T, ∀ hPair : src.length = current.length,
          ⦃ owns b (.disjoint src current hPair) ⦄ back b
            ⦃⇓ result => ⌜result = current⌝⦄⌝⦄ := by
  simp only [new_disjoint_from_slices, hLength, ↓reduceIte, BufferModel.owns, BufferState.toLists]
  step with Buffer.mut_to_raw.spec src as ⟨srcMemory⟩
  step with Buffer.mut_to_raw.spec dst as ⟨dstMemory⟩
  simp only [Buffer.pointsTo_def]
  iintro hDst hSrc
  have hMemory : srcMemory.length = dstMemory.length :=
    hSrc.symm.trans (hLength.trans hDst)
  step with SepLogic.Examples.InPlaceOrDisjointBuffer.newDisjoint.spec
    srcMemory dstMemory src.val dst.val hMemory
  · simp only [Buffer.pointsTo_def]
    iframe
  step*
  · rw [sep_comm_eq]
    apply pure_sep_intro
    intro current hCurrent
    exact finish_disjoint.spec dst src current _ (hLength.trans hCurrent) hCurrent.symm

theorem new_disjoint_from_slices.length_mismatch (src dst : Slice T)
    (hLength : src.length ≠ dst.length) :
    new_disjoint_from_slices src dst = Result.fail .assertionFailure := by
  simp [new_disjoint_from_slices, hLength]

/-! ## Slice access and stateful write-back

Definitions: `Symcrust/Code/FunsExternal.lean`.
Proofs: `Symcrust/Properties/Common/InPlaceOrDisjointBuffer.lean`.

`dst` returns a functional snapshot and a stateful closure which writes its
replacement back to the SAME destination pointer. Ownership is retained as
the closure's precondition; the extracted borrow discipline determines when
it may be called. The second backward function returns the unchanged pointer
record; changes to contents reside in the heap, not in that record.
-/

def src (b : common.InPlaceOrDisjointBuffer T) : Result (Slice T) :=
  Memory.readSlice (srcView b)

@[step]
theorem src.spec (b : common.InPlaceOrDisjointBuffer T) (state : BufferState T) :
    ⦃ owns b state ⦄ src b
      ⦃⇓ result => ⌜result = state.src⌝ ∗ owns b state⦄ := by
  cases state
  · rename_i s
    rw [owns_equal]
    iintro hSame
    have hViews : srcView b = dstView b :=
      SepLogic.Examples.InPlaceOrDisjointBuffer.srcSlice_eq_dstSlice b hSame
    simp only [src, hViews, BufferState.src]
    step*
  · rename_i s d hLength
    rw [owns_disjoint]
    simp only [src, BufferState.src]
    step*

def dst_back (b : common.InPlaceOrDisjointBuffer T) (s : Slice T) :
    Result (common.InPlaceOrDisjointBuffer T) := do
  Memory.writeSlice (dstView b) s
  pure b

@[step]
theorem dst_back.spec (b : common.InPlaceOrDisjointBuffer T)
    (state : BufferState T) (s : Slice T) (hLength : s.length = state.dst.length) :
    ⦃ owns b state ⦄ dst_back b s
      ⦃⇓ result => ⌜result = b⌝ ∗ owns b (state.setDst s hLength)⦄ := by
  cases state
  · rename_i old
    simp only [BufferState.setDst, owns_equal]
    iintro hSame
    unfold dst_back
    step*
  · rename_i source old hPair
    simp only [BufferState.setDst, owns_disjoint]
    unfold dst_back
    step*

def self_back (b : common.InPlaceOrDisjointBuffer T) :
    Result (common.InPlaceOrDisjointBuffer T) :=
  pure b

@[step]
theorem self_back.spec (b : common.InPlaceOrDisjointBuffer T) :
    ⦃ emp ⦄ self_back b ⦃⇓ result => ⌜result = b⌝⦄ := by
  unfold self_back
  step*

def read_dst (b : common.InPlaceOrDisjointBuffer T) : Result (Slice T) :=
  Memory.readSlice (dstView b)

@[step]
theorem read_dst.spec (b : common.InPlaceOrDisjointBuffer T) (state : BufferState T) :
    ⦃ owns b state ⦄ read_dst b
      ⦃⇓ result => ⌜result = state.dst⌝ ∗ owns b state⦄ := by
  cases state
  · rename_i s
    rw [owns_equal]
    iintro hSame
    simp only [read_dst, BufferState.dst]
    step*
  · rename_i s d hLength
    rw [owns_disjoint]
    simp only [read_dst, BufferState.dst]
    step*

def dst (b : common.InPlaceOrDisjointBuffer T) :
    Result (Slice T ×
      (Slice T → Result (common.InPlaceOrDisjointBuffer T)) ×
      (common.InPlaceOrDisjointBuffer T → Result (common.InPlaceOrDisjointBuffer T))) :=
  Aeneas.Std.bind (read_dst b) fun s =>
  pure (s, dst_back b, self_back)

@[step]
theorem dst.spec (b : common.InPlaceOrDisjointBuffer T) (state : BufferState T) :
    ⦃ owns b state ⦄ dst b
      ⦃⇓ s back1 back2 =>
        owns b state ∗
        ⌜s = state.dst ∧
          (∀ s', ∀ hLength : s'.length = state.dst.length,
            ⦃ owns b state ⦄ back1 s'
              ⦃⇓ result => ⌜result = b⌝ ∗ owns b (state.setDst s' hLength)⦄) ∧
          (∀ b', ⦃ emp ⦄ back2 b' ⦃⇓ result => ⌜result = b'⌝⦄)⌝⦄ := by
  have hBack := dst_back.spec b state
  have hSelf := @self_back.spec T
  unfold dst
  step*

end common.InPlaceOrDisjointBuffer

/-! ## Bounded range operations

Destination: the heap helper library. The range specifications frame both the
prefix and suffix. This links the element-wise pointer operations above to
the 16-byte accesses; a block is not one abstract slot.
-/

namespace BufferModel.Memory

theorem readRange_sub.spec (p : Ptr α) (values : List α) (i n : Nat)
    (hBounds : i + n ≤ values.length) :
    ⦃ p ↦* values ⦄ readRange (p.add i) n
      ⦃⇓ result => ⌜result = (values.drop i).take n⌝ ∗ p ↦* values⦄ := by
  have hi : i ≤ values.length := by agrind
  have hRest : n ≤ (values.drop i).length := by simp only [List.length_drop]; agrind
  have hTake : (values.take i).length = i := List.length_take_of_le hi
  have hBlock : ((values.drop i).take n).length = n := List.length_take_of_le hRest
  rw [bientails_eq (Ptr.pointsToRange_split p values i), hTake,
    bientails_eq (Ptr.pointsToRange_split (p.add i) (values.drop i) n)]
  have hRead := readRange.spec (p.add i) ((values.drop i).take n)
  rw [hBlock] at hRead
  step with hRead
  iframe

theorem writeRange_sub.spec (p : Ptr α) (old : List α) (i : Nat) (values : List α)
    (hBounds : i + values.length ≤ old.length) :
    ⦃ p ↦* old ⦄ writeRange (p.add i) values
      ⦃⇓ p ↦* old.setSlice! i values⦄ := by
  have hi : i ≤ old.length := by agrind
  have hRest : values.length ≤ (old.drop i).length := by simp only [List.length_drop]; agrind
  have hTake : (old.take i).length = i := List.length_take_of_le hi
  have hBlock : ((old.drop i).take values.length).length = values.length :=
    List.length_take_of_le hRest
  have hReplace : old.setSlice! i values =
      old.take i ++ values ++ old.drop (i + values.length) := by
    simp only [List.setSlice!, Nat.min_eq_left (show values.length ≤ old.length - i by
      simpa only [List.length_drop] using hRest),
      List.take_length]
  rw [bientails_eq (Ptr.pointsToRange_split p old i), hTake,
    bientails_eq (Ptr.pointsToRange_split (p.add i) (old.drop i) values.length),
    hReplace]
  simp only [bientails_eq (Ptr.pointsToRange_append _ _ _), List.length_append,
    hTake, hBlock, Ptr.add_add, List.drop_drop]
  step with writeRange.spec (p.add i) ((old.drop i).take values.length) values hBlock
  iframe

abbrev Block := Aeneas.Std.Array U8 16#usize

def toBlock (values : List U8) : Result Block :=
  if h : values.length = 16 then
    pure (Aeneas.Std.Array.from values h)
  else
    Result.fail .arrayOutOfBounds

@[step]
theorem toBlock.spec (values : List U8) (hLength : values.length = 16) :
    ⦃ emp ⦄ toBlock values ⦃⇓ result => ⌜result.val = values⌝⦄ := by
  simp only [toBlock, hLength, ↓reduceDIte]
  step*

def readBlock (p : Ptr U8) (i : Usize) : Result Block := do
  let values ← readRange (p.add i.val) 16
  toBlock values

@[step]
theorem readBlock.spec (p : Ptr U8) (s : Slice U8) (i : Usize)
    (hBounds : i.val + 16 ≤ s.length) :
    ⦃ p ↦* s.val ⦄ readBlock p i
      ⦃⇓ result => ⌜result.val = (s.val.drop i.val).take 16⌝ ∗ p ↦* s.val⦄ := by
  unfold readBlock
  step with readRange_sub.spec p s.val i.val 16 hBounds as ⟨values, hValues⟩
  subst values
  step with toBlock.spec ((s.val.drop i.val).take 16) (by
    apply List.length_take_of_le
    simp only [List.length_drop]
    agrind)
  iframe

def writeBlock (p : Ptr U8) (i : Usize) (value : Block) : Result Unit :=
  writeRange (p.add i.val) value.val

@[step]
theorem writeBlock.spec (p : Ptr U8) (s : Slice U8) (i : Usize) (value : Block)
    (hBounds : i.val + 16 ≤ s.length) :
    ⦃ p ↦* s.val ⦄ writeBlock p i value
      ⦃⇓ p ↦* s.val.setSlice! i.val value.val⦄ := by
  exact writeRange_sub.spec p s.val i.val value.val (by simpa using hBounds)

end BufferModel.Memory

/-! ## SIMD interface: exactly sixteen bytes

Definitions: `Symcrust/Code/FunsExternal.lean`; the `Block` carrier should use
the existing `Intrinsics.M128`/`__m128i` definition rather than introduce a
second one. Proofs: `Symcrust/Properties/Common/InPlaceOrDisjointBuffer.lean`.

These definitions intentionally specialize the old generic SIMD signature to
`U8`. Extending them to arbitrary `T` requires a layout/serialization model,
not an unconstrained cast between slices.
-/

namespace common.InPlaceOrDisjointBuffer

def loadu_si128_src (b : common.InPlaceOrDisjointBuffer U8) (i : Usize) :
    Result Memory.Block :=
  Memory.readBlock (srcPtr b) i

def loadu_si128_dst (b : common.InPlaceOrDisjointBuffer U8) (i : Usize) :
    Result Memory.Block :=
  Memory.readBlock (dstPtr b) i

def storeu_si128 (b : common.InPlaceOrDisjointBuffer U8) (i : Usize)
    (value : Memory.Block) :
    Result (common.InPlaceOrDisjointBuffer U8 ×
      (common.InPlaceOrDisjointBuffer U8 → Result (common.InPlaceOrDisjointBuffer U8))) :=
  Aeneas.Std.bind (Memory.writeBlock (dstPtr b) i value) fun _ =>
  pure (b, self_back)

@[step]
theorem loadu_si128_src.spec (b : common.InPlaceOrDisjointBuffer U8)
    (state : BufferState U8) (i : Usize) (hBounds : i.val + 16 ≤ state.src.length) :
    ⦃ owns b state ⦄ loadu_si128_src b i
      ⦃⇓ result => ⌜result.val = (state.src.val.drop i.val).take 16⌝ ∗ owns b state⦄ := by
  cases state
  · rename_i s
    simp only [BufferModel.owns, BufferState.toLists,
      SepLogic.Examples.InPlaceOrDisjointBuffer.pointsTo]
    iintro ⟨hSame, hLength⟩
    have hPointers : srcPtr b = dstPtr b :=
      congrArg Buffer.ptr
        (SepLogic.Examples.InPlaceOrDisjointBuffer.srcSlice_eq_dstSlice b hSame)
    simp only [loadu_si128_src, hPointers, BufferState.src]
    step with Memory.readBlock.spec (dstPtr b) s i hBounds
    iframe
  · rename_i s d hPair
    simp only [BufferModel.owns, BufferState.toLists,
      SepLogic.Examples.InPlaceOrDisjointBuffer.pointsTo]
    iintro ⟨hSrc, hDst⟩
    simp only [loadu_si128_src, BufferState.src]
    step with Memory.readBlock.spec (srcPtr b) s i hBounds
    iframe

@[step]
theorem loadu_si128_dst.spec (b : common.InPlaceOrDisjointBuffer U8)
    (state : BufferState U8) (i : Usize) (hBounds : i.val + 16 ≤ state.dst.length) :
    ⦃ owns b state ⦄ loadu_si128_dst b i
      ⦃⇓ result => ⌜result.val = (state.dst.val.drop i.val).take 16⌝ ∗ owns b state⦄ := by
  cases state
  · rename_i s
    simp only [BufferModel.owns, BufferState.toLists,
      SepLogic.Examples.InPlaceOrDisjointBuffer.pointsTo]
    iintro ⟨hSame, hLength⟩
    simp only [loadu_si128_dst, BufferState.dst]
    step with Memory.readBlock.spec (dstPtr b) s i hBounds
    iframe
  · rename_i s d hPair
    simp only [BufferModel.owns, BufferState.toLists,
      SepLogic.Examples.InPlaceOrDisjointBuffer.pointsTo]
    iintro ⟨hSrc, hDst⟩
    simp only [loadu_si128_dst, BufferState.dst]
    step with Memory.readBlock.spec (dstPtr b) d i hBounds
    iframe

@[step]
theorem storeu_si128.spec (b : common.InPlaceOrDisjointBuffer U8)
    (state : BufferState U8) (i : Usize) (value : Memory.Block)
    (hBounds : i.val + 16 ≤ state.dst.length) :
    ⦃ owns b state ⦄ storeu_si128 b i value
      ⦃⇓ result back =>
        ⌜result = b⌝ ∗
        owns b (state.setDst (state.dst.setSlice! i.val value.val) (by simp)) ∗
        ⌜∀ b', ⦃ emp ⦄ back b' ⦃⇓ result => ⌜result = b'⌝⦄⌝⦄ := by
  have hSelf := @self_back.spec U8
  cases state
  · rename_i s
    simp only [BufferModel.owns, BufferState.toLists, BufferState.setDst, BufferState.dst,
      SepLogic.Examples.InPlaceOrDisjointBuffer.pointsTo, Slice.setSlice!_val,
      List.length_setSlice!]
    iintro ⟨hSame, hLength⟩
    unfold storeu_si128
    step with Memory.writeBlock.spec (dstPtr b) s i value hBounds
    step*
  · rename_i s d hPair
    simp only [BufferModel.owns, BufferState.toLists, BufferState.setDst, BufferState.dst,
      SepLogic.Examples.InPlaceOrDisjointBuffer.pointsTo, Slice.setSlice!_val,
      List.length_setSlice!]
    iintro ⟨hSrc, hDst⟩
    unfold storeu_si128
    step with Memory.writeBlock.spec (dstPtr b) d i value hBounds
    step*

end common.InPlaceOrDisjointBuffer

namespace aes.aes_xmm.InPlaceOrDisjointBufferAU8

/-! Destination: `Symcrust/Code/FunsExternal.lean`. These are the byte-carrier
shims actually called by the extracted AES kernels. Their contracts reuse the
proved generic buffer operation, not a new SIMD axiom. -/

abbrev m128_loadu_src := common.InPlaceOrDisjointBuffer.loadu_si128_src
abbrev m128_loadu_dst := common.InPlaceOrDisjointBuffer.loadu_si128_dst
abbrev m128_storeu := common.InPlaceOrDisjointBuffer.storeu_si128

end aes.aes_xmm.InPlaceOrDisjointBufferAU8

/-! ## Remaining constructors and length

Definitions: `Symcrust/Code/FunsExternal.lean`.
Proofs: `Symcrust/Properties/Common/InPlaceOrDisjointBuffer.lean`.
The raw-parts constructor does not invent ownership: its usable contract
requires the caller to supply the equal/disjoint range assertion.
-/

namespace common.InPlaceOrDisjointBuffer

def len (b : common.InPlaceOrDisjointBuffer T) : Result Usize :=
  if h : (dstView b).length < 2 ^ Aeneas.Std.UScalarTy.Usize.numBits then
    pure (Usize.ofNatCore (dstView b).length h)
  else
    Result.fail .integerOverflow

@[step]
theorem len.spec (b : common.InPlaceOrDisjointBuffer T) (state : BufferState T) :
    ⦃ owns b state ⦄ len b
      ⦃⇓ result => ⌜result.val = state.dst.length⌝ ∗ owns b state⦄ := by
  have hBound (s : Slice T) : s.length < 2 ^ Aeneas.Std.UScalarTy.Usize.numBits := by
    have h := s.len.bv.isLt
    change s.len.val < 2 ^ Aeneas.Std.UScalarTy.Usize.numBits at h
    simpa only [Slice.len_val] using h
  cases state
  · rename_i s
    simp only [BufferModel.owns, BufferState.toLists,
      SepLogic.Examples.InPlaceOrDisjointBuffer.pointsTo]
    iintro ⟨hSame, hLength⟩
    have hLen : (dstView b).length = s.length := hLength.symm
    have hFits : (dstView b).length < 2 ^ Aeneas.Std.UScalarTy.Usize.numBits := hLen ▸ hBound s
    simp only [len, hFits, ↓reduceDIte]
    step*
  · rename_i s d hPair
    simp only [BufferModel.owns, BufferState.toLists,
      SepLogic.Examples.InPlaceOrDisjointBuffer.pointsTo]
    iintro ⟨hSrc, hDst⟩
    have hLen : (dstView b).length = d.length := hDst.symm
    have hFits : (dstView b).length < 2 ^ Aeneas.Std.UScalarTy.Usize.numBits := hLen ▸ hBound d
    simp only [len, hFits, ↓reduceDIte]
    step*

def from_raw_parts (src dst : Ptr T) (length : Usize) :
    Result (common.InPlaceOrDisjointBuffer T) :=
  SepLogic.Examples.InPlaceOrDisjointBuffer.fromRawParts src dst length.val

@[step]
theorem from_raw_parts.spec (src dst : Ptr T) (length : Usize) (state : BufferState T) :
    ⦃ owns ⟨src, dst, length.val⟩ state ⦄ from_raw_parts src dst length
      ⦃⇓ result => ⌜result = ⟨src, dst, length.val⟩⌝ ∗ owns result state⦄ := by
  unfold from_raw_parts
  step*
  · simp only [SepLogic.Examples.InPlaceOrDisjointBuffer.mkFromRawParts]
    iframe

def finish_array {N : Usize} (original : Aeneas.Std.Array T N)
    (b : common.InPlaceOrDisjointBuffer T) : Result (Aeneas.Std.Array T N) :=
  Aeneas.Std.bind (finish_disjoint original.to_slice b) fun s =>
  if h : s.val.length = N.val then
    pure (Aeneas.Std.Array.from s.val h)
  else
    Result.fail .assertionFailure

@[step]
theorem finish_array.spec {N : Usize} (original current : Aeneas.Std.Array T N)
    (source : Slice T) (b : common.InPlaceOrDisjointBuffer T)
    (hPair : source.length = current.to_slice.length) :
    ⦃ owns b (.disjoint source current.to_slice hPair) ⦄ finish_array original b
      ⦃⇓ result => ⌜result = current⌝⦄ := by
  unfold finish_array
  step with finish_disjoint.spec original.to_slice source current.to_slice b hPair
    (by simp) as ⟨s, hs⟩
  subst s
  simp only [Aeneas.Std.Array.val_to_slice, Aeneas.Std.Array.property, ↓reduceDIte]
  step*

def new_disjoint {N : Usize} (src dst : Aeneas.Std.Array T N) :
    Result (common.InPlaceOrDisjointBuffer T ×
      (common.InPlaceOrDisjointBuffer T → Result (Aeneas.Std.Array T N))) :=
  Aeneas.Std.bind (new_disjoint_from_slices src.to_slice dst.to_slice) fun (b, _) =>
  pure (b, finish_array dst)

@[step]
theorem new_disjoint.spec {N : Usize} (src dst : Aeneas.Std.Array T N) :
    ⦃ emp ⦄ new_disjoint src dst
      ⦃⇓ b back =>
        owns b (.disjoint src.to_slice dst.to_slice (by simp)) ∗
        ⌜∀ current : Aeneas.Std.Array T N,
          ⦃ owns b (.disjoint src.to_slice current.to_slice (by simp)) ⦄ back b
            ⦃⇓ result => ⌜result = current⌝⦄⌝⦄ := by
  unfold new_disjoint
  step*
  · rw [sep_comm_eq]
    apply pure_sep_intro
    intro current
    exact finish_array.spec dst current src.to_slice _ (by simp)

end common.InPlaceOrDisjointBuffer

/-! ## Clients: the future generated call shape

Definitions: examples for `Symcrust/Code/Funs.lean`, not hand-edits to today's
generated file. Proofs: `Symcrust/Properties/Aes/Gcm/`.

The important changes are the stateful calls to `writeBack`, `endSelf` and
`finish`. `Aeneas.Std.bind` is the heterogeneous-universe bind: returning a
callback into the heap-effect `Result` raises the tuple's universe, so ordinary
`do` notation cannot cross all of these boundaries in the current prototype.

The public signatures still take and return slices/arrays. They neither take
pointers nor expose an ownership precondition. Each proof starts with `emp`,
establishes the internal ownership, and finishes with a full value equality.
-/

namespace BufferModel.Clients

open common.InPlaceOrDisjointBuffer

def replaceInPlace (s replacement : Slice T) : Result (Slice T × Slice T) :=
  Aeneas.Std.bind (new_in_place s) fun (b, finish) =>
  Aeneas.Std.bind (dst b) fun (_, writeBack, endSelf) => do
    let b ← writeBack replacement
    let b ← endSelf b
    let observed ← src b
    let output ← finish b
    pure (observed, output)

theorem replaceInPlace.spec (s replacement : Slice T)
    (hLength : replacement.length = s.length) :
    ⦃ emp ⦄ replaceInPlace s replacement
      ⦃⇓ observed output => ⌜observed = replacement ∧ output = replacement⌝⦄ := by
  unfold replaceInPlace
  step*
  · subst_vars
    simp only [BufferState.setDst, BufferState.src, BufferState.dst] at *
    step*

def replaceDisjoint (source target replacement : Slice T) : Result (Slice T × Slice T) :=
  Aeneas.Std.bind (new_disjoint_from_slices source target) fun (b, finish) =>
  Aeneas.Std.bind (dst b) fun (_, writeBack, endSelf) => do
    let b ← writeBack replacement
    let b ← endSelf b
    let observed ← src b
    let output ← finish b
    pure (observed, output)

theorem replaceDisjoint.spec (source target replacement : Slice T)
    (hPair : source.length = target.length)
    (hLength : replacement.length = target.length) :
    ⦃ emp ⦄ replaceDisjoint source target replacement
      ⦃⇓ observed output => ⌜observed = source ∧ output = replacement⌝⦄ := by
  unfold replaceDisjoint
  step*
  · subst_vars
    simp only [BufferState.setDst, BufferState.src, BufferState.dst] at *
    step*

def storeBlock (b : common.InPlaceOrDisjointBuffer U8) (i : Usize) (value : Memory.Block) :
    Result (common.InPlaceOrDisjointBuffer U8) :=
  Aeneas.Std.bind (aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_storeu b i value)
    fun (b, back) => back b

@[step]
theorem storeBlock.spec (b : common.InPlaceOrDisjointBuffer U8)
    (state : BufferState U8) (i : Usize) (value : Memory.Block)
    (hBounds : i.val + 16 ≤ state.dst.length) :
    ⦃ owns b state ⦄ storeBlock b i value
      ⦃⇓ result =>
        ⌜result = b⌝ ∗
        owns b (state.setDst (state.dst.setSlice! i.val value.val) (by simp))⦄ := by
  unfold storeBlock aes.aes_xmm.InPlaceOrDisjointBufferAU8.m128_storeu
  step*

def blockInPlace (s : Slice U8) (i : Usize) (value : Memory.Block) :
    Result (Memory.Block × Memory.Block × Slice U8) :=
  Aeneas.Std.bind (new_in_place s) fun (b, finish) => do
    let b ← storeBlock b i value
    let observedSrc ← loadu_si128_src b i
    let observedDst ← loadu_si128_dst b i
    let output ← finish b
    pure (observedSrc, observedDst, output)

theorem blockInPlace.spec (s : Slice U8) (i : Usize) (value : Memory.Block)
    (hBounds : i.val + 16 ≤ s.length) :
    ⦃ emp ⦄ blockInPlace s i value
      ⦃⇓ observedSrc observedDst output =>
        ⌜output = s.setSlice! i.val value.val ∧
          observedSrc.val = (output.val.drop i.val).take 16 ∧
          observedDst.val = (output.val.drop i.val).take 16⌝⦄ := by
  unfold blockInPlace
  step*
  · subst_vars
    simp only [BufferState.setDst, BufferState.src, BufferState.dst] at *
    step*

def blockDisjoint (source target : Slice U8) (i : Usize) (value : Memory.Block) :
    Result (Memory.Block × Memory.Block × Slice U8) :=
  Aeneas.Std.bind (new_disjoint_from_slices source target) fun (b, finish) => do
    let b ← storeBlock b i value
    let observedSrc ← loadu_si128_src b i
    let observedDst ← loadu_si128_dst b i
    let output ← finish b
    pure (observedSrc, observedDst, output)

theorem blockDisjoint.spec (source target : Slice U8) (i : Usize) (value : Memory.Block)
    (hPair : source.length = target.length) (hBounds : i.val + 16 ≤ target.length) :
    ⦃ emp ⦄ blockDisjoint source target i value
      ⦃⇓ observedSrc observedDst output =>
        ⌜output = target.setSlice! i.val value.val ∧
          observedSrc.val = (source.val.drop i.val).take 16 ∧
          observedDst.val = (output.val.drop i.val).take 16⌝⦄ := by
  unfold blockDisjoint
  step*
  · subst_vars
    simp only [BufferState.setDst, BufferState.src, BufferState.dst] at *
    step*

end BufferModel.Clients

/-! ## Executable regression examples and trusted-base audit

Destination: a dedicated buffer-model test module.
The full-width cases specialize the proved contracts without interpreting
the large heap trace during every elaboration. Small cases run the modeled
heap, including the stateful backward functions.
An `emp` postcondition alone does not imply an empty final heap in an affine
logic, so the executions check the final heap size separately.
-/

namespace BufferModel.Regression

def initial : Slice U8 := (Aeneas.Std.Array.repeat 32#usize 1#u8).to_slice
def block : Memory.Block := Aeneas.Std.Array.repeat 16#usize 7#u8
def empty : Slice U8 := Slice.new U8
def expected : List U8 :=
  List.replicate 8 1#u8 ++ List.replicate 16 7#u8 ++ List.replicate 8 1#u8

-- An unaligned block write preserves the eight-byte prefix and suffix.
theorem blockInPlace :
    ⦃ emp ⦄ Clients.blockInPlace initial 8#usize block
      ⦃⇓ observedSrc observedDst output =>
        ⌜observedSrc.val = block.val ∧ observedDst.val = block.val ∧ output.val = expected⌝⦄ := by
  apply Aeneas.Std.WP.ispec_conseq
    (Clients.blockInPlace.spec initial 8#usize block (by simp [initial])) (entails_refl _)
  rintro ⟨observedSrc, observedDst, output⟩
  simp only [Aeneas.Std.WP.uncurry']
  iintro ⟨hOutput, hSrc, hDst⟩
  subst output
  have hBlock : (((initial.setSlice! 8 block.val).val).drop 8).take 16 = block.val := by decide
  apply (entails_emp_ipure_iff _).mpr
  exact ⟨hSrc.trans hBlock, hDst.trans hBlock, by decide⟩

-- Equal *initial contents* do not select in-place mode.
theorem blockDisjoint :
    ⦃ emp ⦄ Clients.blockDisjoint initial initial 8#usize block
      ⦃⇓ observedSrc observedDst output =>
        ⌜observedSrc.val = List.replicate 16 1#u8 ∧
          observedDst.val = block.val ∧ output.val = expected⌝⦄ := by
  apply Aeneas.Std.WP.ispec_conseq
    (Clients.blockDisjoint.spec initial initial 8#usize block rfl (by simp [initial]))
    (entails_refl _)
  rintro ⟨observedSrc, observedDst, output⟩
  simp only [Aeneas.Std.WP.uncurry']
  iintro ⟨hOutput, hSrc, hDst⟩
  subst output
  have hRead : (initial.val.drop 8).take 16 = List.replicate 16 1#u8 := by decide
  have hBlock : (((initial.setSlice! 8 block.val).val).drop 8).take 16 = block.val := by decide
  apply (entails_emp_ipure_iff _).mpr
  exact ⟨hSrc.trans hRead, hDst.trans hBlock, by decide⟩

def tinyInitial : Slice U8 := (Aeneas.Std.Array.repeat 2#usize 1#u8).to_slice
def replacement : Slice U8 := (Aeneas.Std.Array.repeat 2#usize 9#u8).to_slice

def borrowInPlaceRun :=
  execClosed (Clients.replaceInPlace tinyInitial replacement)
    (Clients.replaceInPlace.spec tinyInitial replacement (by simp [tinyInitial, replacement]))

/-- info: true -/
#guard_msgs in
#eval
  let r := borrowInPlaceRun
  r.1 == (replacement, replacement) && r.2.size == 0

def borrowDisjointRun :=
  execClosed (Clients.replaceDisjoint tinyInitial tinyInitial replacement)
    (Clients.replaceDisjoint.spec tinyInitial tinyInitial replacement rfl
      (by simp [tinyInitial, replacement]))

/-- info: true -/
#guard_msgs in
#eval
  let r := borrowDisjointRun
  r.1 == (tinyInitial, replacement) && r.2.size == 0

def emptyInPlaceRun :=
  execClosed (Clients.replaceInPlace empty empty)
    (Clients.replaceInPlace.spec empty empty rfl)

def emptyDisjointRun :=
  execClosed (Clients.replaceDisjoint empty empty empty)
    (Clients.replaceDisjoint.spec empty empty empty rfl rfl)

/-- info: true -/
#guard_msgs in
#eval
  let r := emptyInPlaceRun
  r.1 == (empty, empty) && r.2.size == 0

/-- info: true -/
#guard_msgs in
#eval
  let r := emptyDisjointRun
  r.1 == (empty, empty) && r.2.size == 0

example :
    common.InPlaceOrDisjointBuffer.new_disjoint_from_slices empty initial =
      Result.fail .assertionFailure :=
  common.InPlaceOrDisjointBuffer.new_disjoint_from_slices.length_mismatch empty initial
    (by simp [empty, initial])

end BufferModel.Regression

/- No buffer, pointer-to-slice, transmutation, or `sorryAx` assumptions may
enter these completed client proofs. Only Lean's standard logical axioms
remain. These assertions deliberately make a future regression visible. -/

/-- info: 'BufferModel.Clients.replaceInPlace.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BufferModel.Clients.replaceInPlace.spec

/-- info: 'BufferModel.Clients.replaceDisjoint.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BufferModel.Clients.replaceDisjoint.spec

/-- info: 'BufferModel.Clients.blockInPlace.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BufferModel.Clients.blockInPlace.spec

/-- info: 'BufferModel.Clients.blockDisjoint.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BufferModel.Clients.blockDisjoint.spec
