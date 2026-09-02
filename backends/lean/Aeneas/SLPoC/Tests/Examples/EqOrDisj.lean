import Aeneas.SLPoC.MutableData.Buffer

/-!
# `InPlaceOrDisjointBuffer`

A port of the `InPlaceOrDisjointBuffer<'a, T>` of
[SymCRust](https://github.com/microsoft/VCR) (`SymCRust/src/common.rs`): a read
view and a write view of the same length which are either the *same* buffer
(in-place) or two disjoint ones.  Cryptographic code wants one API for both, so
the type is a pair of raw pointers plus a length, and its `unsafe` constructor
asks the caller for exactly the property this file makes a *ghost state*:

> `src` and `dst` must be either equal or completely disjoint

`EqOrDisj` is that ghost state, and `pointsTo` below is what the pair owns in
each of its two shapes.  The in-place shape owns one range, so a write is
visible to the reader; the disjoint shape owns two, and the separating
conjunction alone rules out the overlap the Rust contract has to ask for.

The x86 block accessors (`loadu_si128_src`, `loadu_si128_dst`,
`storeu_si128`) are ported element-wise: their 128-bit width is an instruction
detail, and what the interface says about aliasing is the same one element at a
time.
-/

namespace Aeneas.SLPoC

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
`St` actions all the same — in Rust they are calls, so a `do` block mirrors the
Rust and `step` applies their triples — and each rests on an entailment, which
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
def newInPlace (buffer : Buffer α) : St (InPlaceOrDisjointBuffer α) :=
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
def newDisjoint (src dst : Buffer α) : St (InPlaceOrDisjointBuffer α) :=
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
triple starts from `emp`.  The contract *is* the `pointsTo` a caller has to
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
    St (InPlaceOrDisjointBuffer α) :=
  pure (mkFromRawParts src dst len)

@[step]
theorem fromRawParts.spec (src dst : Ptr α) (len : Nat) :
    ⦃ emp ⦄ fromRawParts src dst len
      ⦃⇓ b => ⌜b = mkFromRawParts src dst len⌝⦄ := -- TODO: strengthen
  by
  simp only [fromRawParts, mkFromRawParts]
  step*

/-! ## Views -/

/-- `len`.

```rust
pub fn len(&self) -> usize {
    self.len
}
```
-/
def length (b : InPlaceOrDisjointBuffer α) : Nat := b.len

/-- `src`: the read view as a slice.

```rust
pub fn src(&self) -> &[T] {
    unsafe { core::slice::from_raw_parts(self.src, self.len) }
}
```
-/
def srcSlice (b : InPlaceOrDisjointBuffer α) : Buffer α :=
  ⟨b.src.base, b.src.offset, b.len⟩

/-- `dst`: the write view as a mutable slice.

```rust
pub fn dst(&mut self) -> &mut [T] {
    unsafe { core::slice::from_raw_parts_mut(self.dst, self.len) }
}
```
-/
def dstSlice (b : InPlaceOrDisjointBuffer α) : Buffer α :=
  ⟨b.dst.base, b.dst.offset, b.len⟩

@[simp] theorem ptr_srcSlice (b : InPlaceOrDisjointBuffer α) :
    b.srcSlice.ptr = b.src := rfl

@[simp] theorem ptr_dstSlice (b : InPlaceOrDisjointBuffer α) :
    b.dstSlice.ptr = b.dst := rfl

/-- In place the two views are literally the same slice: this is why `dst`
takes `&mut self` in Rust, and why one range is all the pair owns. -/
theorem srcSlice_eq_dstSlice (b : InPlaceOrDisjointBuffer α)
    (hSame : b.src = b.dst) : b.srcSlice = b.dstSlice := by
  simp [srcSlice, dstSlice, hSame]

/-- In place, that one slice is what the pair owns. -/
theorem pointsTo_dstSlice_equal (b : InPlaceOrDisjointBuffer α)
    (values : List α) :
    b.pointsTo (.equal values) ⊢ b.dstSlice ↦ values := by
  intro h hPointsTo
  obtain ⟨⟨-, hLength⟩, hRange⟩ := (sep_pure_l _ _ h).mp hPointsTo
  exact (sep_pure_l _ _ h).mpr ⟨hLength, hRange⟩

/-- `src()` hands back the read view. -/
theorem pointsTo_srcSlice_disjoint (b : InPlaceOrDisjointBuffer α)
    (srcValues dstValues : List α) :
    b.pointsTo (.disjoint srcValues dstValues) ⊢ b.srcSlice ↦ srcValues := by
  intro h hPointsTo
  obtain ⟨⟨hLength, -⟩, hRanges⟩ := (sep_pure_l _ _ h).mp hPointsTo
  obtain ⟨h₁, h₂, hCompatible, rfl, hSrc, -⟩ := hRanges
  exact (sep_pure_l _ _ _).mpr
    ⟨hLength, (b.srcSlice.ptr ↦* srcValues).up_closed hSrc
      (Heap.Sub.union_left hCompatible)⟩

/-- `dst()` hands back the write view, and the range it owns is the one the
pair owned. -/
theorem pointsTo_dstSlice_disjoint (b : InPlaceOrDisjointBuffer α)
    (srcValues dstValues : List α) :
    b.pointsTo (.disjoint srcValues dstValues) ⊢ b.dstSlice ↦ dstValues := by
  intro h hPointsTo
  obtain ⟨⟨-, hLength⟩, hRanges⟩ := (sep_pure_l _ _ h).mp hPointsTo
  obtain ⟨h₁, h₂, hCompatible, rfl, -, hDst⟩ := hRanges
  exact (sep_pure_l _ _ _).mpr
    ⟨hLength, (b.dstSlice.ptr ↦* dstValues).up_closed hDst
      (Heap.Sub.union_right hCompatible)⟩

/-! ## Element access

`loadu_si128_src`, `loadu_si128_dst` and `storeu_si128`, one element at a time.
None of them has a precondition: an offset out of the range the caller owns
simply has no provable triple.

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
def loadSrc (b : InPlaceOrDisjointBuffer α) (i : Nat) : St α :=
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
def loadDst (b : InPlaceOrDisjointBuffer α) (i : Nat) : St α :=
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
def store (b : InPlaceOrDisjointBuffer α) (i : Nat) (value : α) : St Unit :=
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
      apply triple_ipure_keep
      rintro ⟨hSame, -⟩
      simp only [pointsTo]
      unfold loadSrc
      rw [hSame, Ptr.pointsToRange_eq_take_get_drop hLt, hGet]
      step*
  | disjoint srcValues dstValues =>
      obtain ⟨hLt, hGet⟩ :=
        List.getElem?_eq_some_iff.mp
          (show srcValues[i]? = some value from hIndex)
      apply triple_ipure_keep
      rintro -
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
      apply triple_ipure_keep
      rintro -
      simp only [pointsTo]
      unfold loadDst
      rw [Ptr.pointsToRange_eq_take_get_drop hLt, hGet]
      step*
  | disjoint srcValues dstValues =>
      obtain ⟨hLt, hGet⟩ :=
        List.getElem?_eq_some_iff.mp
          (show dstValues[i]? = some value from hIndex)
      apply triple_ipure_keep
      rintro -
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
      apply triple_ipure_keep
      rintro -
      simp only [EqOrDisj.write, EqOrDisj.written, pointsTo, List.length_set]
      unfold store
      rw [Ptr.pointsToRange_eq_take_get_drop hLt,
        Ptr.pointsToRange_eq_take_get_drop
          (show i < (values.set i value).length by simpa using hLt),
        take_set, drop_set, List.getElem_set_self]
      step*
  | disjoint srcValues dstValues =>
      have hLt : i < dstValues.length := hIndex
      apply triple_ipure_keep
      rintro -
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
    St α := do
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
triple and hands the ownership on. -/
def inPlaceWrite (buffer : Buffer α) (i : Nat) (value : α) : St Unit := do
  let b ← newInPlace buffer
  b.store i value

theorem inPlaceWrite.spec (buffer : Buffer α) (values : List α) (i : Nat)
    (value : α) (hIndex : i < values.length) :
    ⦃ buffer ↦ values ⦄ inPlaceWrite buffer i value
      ⦃⇓ (mkInPlace buffer).pointsTo (.equal (values.set i value))⦄ := by
  unfold inPlaceWrite
  step*
  case hIndex => exact hIndex

end InPlaceOrDisjointBuffer

end Examples

end Aeneas.SLPoC
