module
public import Aeneas.Std.RawPtr
public import Aeneas.Std.Slice
public import Aeneas.Tactic.SepLogic.IFrame
public import Aeneas.Tactic.SepLogic.IIntro
public import Aeneas.Tactic.SepLogic.ISimp
public import Aeneas.Tactic.Step.Init
@[expose] public section

/-!
# Buffers

`Buffer T` models a mutable Rust slice `&mut [T]`: a bounded view into an
allocation, represented by a base address, a byte offset, and a length in
elements. The value itself carries no permission; `b ↦ values` owns the slots
it spans.

Views and pointer arithmetic are total. Invalid reads or writes have no
provable specification because their guarded heap operations are stuck.
-/

open Aeneas
open Aeneas.SepLogic

namespace Aeneas.Std

open WP

variable {T : Type}

/-- A bounded mutable view into a heap allocation. -/
structure Buffer (T : Type) where
  base : AllocId
  offset : Nat
  length : Nat
  deriving Inhabited, DecidableEq

namespace Buffer

/-- The mutable pointer to the first slot of the view. -/
def ptr (b : Buffer T) : MutRawPtr T :=
  ⟨b.base, b.offset⟩

/-- The mutable pointer to slot `i` of the view. -/
def ptrAt [ByteRepr T] (b : Buffer T) (i : Nat) : MutRawPtr T :=
  b.ptr.add i

/-- The sub-view of `n` slots starting at index `i`. -/
def sub [ByteRepr T] (b : Buffer T) (i n : Nat) : Buffer T :=
  ⟨b.base, b.offset + i * ByteRepr.size T, n⟩

/-- Split a view at index `i`. -/
def split [ByteRepr T] (b : Buffer T) (i : Nat) : Buffer T × Buffer T :=
  (b.sub 0 i, b.sub i (b.length - i))

/-- Join adjacent views. Ownership lemmas establish when the join is valid. -/
def join (b₁ b₂ : Buffer T) : Buffer T :=
  ⟨b₁.base, b₁.offset, b₁.length + b₂.length⟩

/-- `b` owns its slots, holding `values`. -/
def pointsTo [ByteRepr T] (b : Buffer T) (values : List T) : IProp :=
  iprop(⌜values.length = b.length⌝ ∗ b.ptr ↦* values)

end Buffer

instance instPointsToBuffer {T : Type} [ByteRepr T] :
    PointsTo (Buffer T) (List T) := ⟨Buffer.pointsTo⟩

namespace Buffer

/-- Allocate `n` slots holding `value`. -/
def alloc [ByteRepr T] (n : Nat) (value : T) : Result (Buffer T) :=
  RawPtr.allocArray (List.replicate n value) fun q =>
    ⟨q.base, q.offset, n⟩

@[step]
theorem alloc.spec [ByteRepr T] (n : Nat) (value : T) :
    ⦃ emp ⦄ Buffer.alloc n value
      ⦃⇓ b => b ↦ List.replicate n value⦄ := by
  refine RawPtr.allocArray.spec _ _ _ fun q h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨by simp, hOwns⟩

/-- A buffer owns exactly the range addressed by its pointer. -/
@[iris_simps]
theorem pointsTo_def [ByteRepr T] (b : Buffer T) (values : List T) :
    (b ↦ values) =
      iprop(⌜values.length = b.length⌝ ∗ b.ptr ↦* values) := rfl

/-- Read slot `i`. -/
def read [ByteRepr T] (b : Buffer T) (i : Nat) : Result T :=
  RawPtr.read (b.ptrAt i)

@[step]
theorem read.spec [ByteRepr T] (b : Buffer T) (i : Nat) (value : T) :
    ⦃ b.ptrAt i ↦ value ⦄ b.read i
      ⦃⇓ result => ⌜result = value⌝ ∗ b.ptrAt i ↦ value⦄ :=
  RawPtr.read.spec (b.ptrAt i) value

/-- Write slot `i`. -/
def write [ByteRepr T] (b : Buffer T) (i : Nat) (value : T) : Result Unit :=
  MutRawPtr.write (b.ptrAt i) value

@[step]
theorem write.spec [ByteRepr T] (b : Buffer T) (i : Nat) (oldValue newValue : T) :
    ⦃ b.ptrAt i ↦ oldValue ⦄ b.write i newValue
      ⦃⇓ b.ptrAt i ↦ newValue⦄ :=
  MutRawPtr.write.spec (b.ptrAt i) oldValue newValue

/-- Release every slot spanned by the view. -/
def free [ByteRepr T] (b : Buffer T) : Result Unit :=
  MutRawPtr.freeRange b.ptr b.length

@[step]
theorem free.spec [ByteRepr T] (b : Buffer T) (values : List T) :
    ⦃ b ↦ values ⦄ b.free ⦃⇓ emp⦄ := by
  unfold Buffer.free
  simp only [pointsTo_def]
  iintro hLength
  rw [← hLength]
  exact MutRawPtr.freeRange.spec b.ptr values

/-- A view spans as many slots as the values it owns. -/
theorem length_of_pointsTo [ByteRepr T] {b : Buffer T} {values : List T} {h : Heap}
    (hPointsTo : (b ↦ values) h) : values.length = b.length :=
  ((sep_pure_l _ _ h).mp hPointsTo).1

theorem read.spec_buffer [ByteRepr T] (b : Buffer T) (values : List T) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ b ↦ values ⦄ b.read i
      ⦃⇓ result => ⌜result = values[i]⌝ ∗ b ↦ values⦄ := by
  change ispec _ (RawPtr.read (b.ptr.add i)) _
  simp only [pointsTo_def]
  iintro hLength
  apply WP.ispec_mono (RawPtr.read.spec_range b.ptr values i hIndex)
  iframe

theorem write.spec_buffer [ByteRepr T] (b : Buffer T) (values : List T) (i : Nat)
    (value : T) (hIndex : i < values.length) :
    ⦃ b ↦ values ⦄ b.write i value
      ⦃⇓ b ↦ values.set i value⦄ := by
  change ispec _ (MutRawPtr.write (b.ptr.add i) value) _
  simp only [pointsTo_def]
  iintro hLength
  apply WP.ispec_mono
    (MutRawPtr.write.spec_range b.ptr values i value hIndex)
  iframe

/-- Snapshot `n` consecutive slots without consuming their ownership. -/
def readRange [ByteRepr T] (p : RawPtr T M) : Nat → Result (List T)
  | 0 => pure []
  | n + 1 => do
      let value ← p.read
      let rest ← readRange (p.add 1) n
      pure (value :: rest)

@[step]
theorem readRange.spec [ByteRepr T] (p : RawPtr T M) (values : List T) :
    ⦃ p ↦* values ⦄ readRange p values.length
      ⦃⇓ result => ⌜result = values⌝ ∗ p ↦* values⦄ := by
  induction values generalizing p with
  | nil =>
      simp only [List.length_nil, readRange, RawPtr.pointsToRange_nil]
      apply (ispec_ok _).2
      iframe
  | cons value rest ih =>
      simp only [List.length_cons, readRange, RawPtr.pointsToRange_cons]
      apply WP.ispec_bind
        (F := (p.add 1) ↦* rest)
        (RawPtr.read.spec p value)
      · iframe
      · intro readValue
        iintro hRead
        subst readValue
        apply WP.ispec_bind
          (F := p ↦ value)
          (ih (p := p.add 1))
        · iframe
        · intro readRest
          iintro hRest
          subst readRest
          apply (ispec_ok _).2
          iframe

/-- Overwrite consecutive mutable slots with the supplied values. -/
def writeRange [ByteRepr T] (p : MutRawPtr T) : List T → Result Unit
  | [] => pure ()
  | value :: rest => do
      p.write value
      writeRange (p.add 1) rest

@[step]
theorem writeRange.spec [ByteRepr T] (p : MutRawPtr T) (old values : List T)
    (hLength : old.length = values.length) :
    ⦃ p ↦* old ⦄ writeRange p values ⦃⇓ p ↦* values⦄ := by
  induction values generalizing p old with
  | nil =>
      obtain rfl : old = [] := by simpa using hLength
      simp only [writeRange, RawPtr.pointsToRange_nil]
      apply (ispec_ok _).2
      iframe
  | cons value rest ih =>
      obtain ⟨previous, oldRest, rfl⟩ : ∃ x xs, old = x :: xs := by
        cases old
        · simp at hLength
        · exact ⟨_, _, rfl⟩
      have hRest : oldRest.length = rest.length := by simpa using hLength
      simp only [writeRange, RawPtr.pointsToRange_cons]
      apply WP.ispec_bind
        (F := (p.add 1) ↦* oldRest)
        (MutRawPtr.write.spec p previous value)
      · iframe
      · intro _
        apply WP.ispec_mono
          (WP.ispec_frame
            (ih (p := p.add 1) (old := oldRest) hRest)
            (p ↦ value))
        exact entails_trans (by iframe)
          (entails_sep_postWand _ (by intro _; iframe))

/-- Turn a list whose length fits in `Usize` into a functional slice. -/
def toSlice (values : List T) : Result (Slice T) :=
  if h : values.length ≤ Usize.max then
    pure (Slice.from values h)
  else
    Result.fail .maximumSizeExceeded

@[step]
theorem toSlice.spec (s : Slice T) :
    ⦃ emp ⦄ toSlice s.val ⦃⇓ result => ⌜result = s⌝⦄ := by
  simp only [toSlice, s.property, ↓reduceDIte]
  apply (ispec_ok _).2
  simp

/-- Snapshot the complete buffer as a functional slice. -/
def readSlice [ByteRepr T] (b : Buffer T) : Result (Slice T) := do
  let values ← readRange b.ptr b.length
  toSlice values

@[step]
theorem readSlice.spec [ByteRepr T] (b : Buffer T) (s : Slice T) :
    ⦃ b ↦ s.val ⦄ readSlice b
      ⦃⇓ result => ⌜result = s⌝ ∗ b ↦ s.val⦄ := by
  simp only [pointsTo_def]
  iintro hLength
  unfold readSlice
  rw [← hLength]
  apply WP.ispec_bind (readRange.spec b.ptr s.val) (sep_emp_r _).mpr
  intro values
  rw [sep_emp_r_eq]
  iintro hValues
  subst values
  apply WP.ispec_mono
    (WP.ispec_frame (toSlice.spec s) (b.ptr ↦* s.val))
  exact entails_trans (by iframe)
    (entails_sep_postWand _ (by intro result; iframe))

/-- Write a functional slice into the existing buffer allocation. -/
def writeSlice [ByteRepr T] (b : Buffer T) (s : Slice T) : Result Unit :=
  if s.length = b.length then
    writeRange b.ptr s.val
  else
    Result.fail .assertionFailure

@[step]
theorem writeSlice.spec [ByteRepr T] (b : Buffer T) (old s : Slice T)
    (hLength : s.length = old.length) :
    ⦃ b ↦ old.val ⦄ writeSlice b s ⦃⇓ b ↦ s.val⦄ := by
  simp only [pointsTo_def]
  iintro hOld
  have hNew : s.length = b.length := hLength.trans hOld
  simp only [writeSlice, hNew, ↓reduceIte]
  apply WP.ispec_mono
    (writeRange.spec b.ptr old.val s.val hLength.symm)
  iframe

/-- Allocate a view containing exactly `values`. -/
def ofList [ByteRepr T] (values : List T) : Result (Buffer T) :=
  RawPtr.allocArray values fun q =>
    ⟨q.base, q.offset, values.length⟩

@[step]
theorem ofList.spec [ByteRepr T] (values : List T) :
    ⦃ emp ⦄ Buffer.ofList values ⦃⇓ b => b ↦ values⦄ := by
  refine RawPtr.allocArray.spec _ _ _ fun q h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨rfl, hOwns⟩

/-- Overwrite every slot with `value`. -/
def fill [ByteRepr T] (b : Buffer T) (value : T) : Result Unit :=
  MutRawPtr.fillRange b.ptr value b.length

@[step]
theorem fill.spec [ByteRepr T] (b : Buffer T) (values : List T) (value : T) :
    ⦃ b ↦ values ⦄ b.fill value
      ⦃⇓ b ↦ List.replicate b.length value⦄ := by
  unfold Buffer.fill
  simp only [pointsTo_def]
  iintro hLength
  rw [← hLength]
  apply WP.ispec_mono (MutRawPtr.fillRange.spec b.ptr values value)
  iframe

/-- Extract the length facts and underlying ranges of two owned buffers. -/
theorem pointsTo_pair_entails [ByteRepr T] (b₁ b₂ : Buffer T)
    (values₁ values₂ : List T) :
    b₁ ↦ values₁ ∗ b₂ ↦ values₂ ⊢
      iprop(⌜values₁.length = b₁.length ∧
          values₂.length = b₂.length⌝ ∗
        (b₁.ptr ↦* values₁ ∗ b₂.ptr ↦* values₂)) := by
  isimp

/-- Reassemble two buffer ownership assertions from their ranges. -/
theorem pair_entails_pointsTo [ByteRepr T] {b₁ b₂ : Buffer T}
    {values₁ values₂ : List T}
    (hLength₁ : values₁.length = b₁.length)
    (hLength₂ : values₂.length = b₂.length) :
    b₁.ptr ↦* values₁ ∗ b₂.ptr ↦* values₂ ⊢
      b₁ ↦ values₁ ∗ b₂ ↦ values₂ := by
  isimp

/-- Copy every slot of `src` into `dst`. -/
def copy [ByteRepr T] (dst src : Buffer T) : Result Unit :=
  MutRawPtr.copyRange dst.ptr src.ptr src.length

@[step]
theorem copy.spec [ByteRepr T] (dst src : Buffer T) (dstValues srcValues : List T)
    (hLength : dst.length = src.length) :
    ⦃ dst ↦ dstValues ∗ src ↦ srcValues ⦄ dst.copy src
      ⦃⇓ dst ↦ srcValues ∗ src ↦ srcValues⦄ := by
  unfold Buffer.copy
  simp only [pointsTo_def]
  iintro hDst hSrc
  have hValues : dstValues.length = srcValues.length := by omega
  rw [← hSrc]
  apply WP.ispec_mono
    (MutRawPtr.copyRange.spec dst.ptr src.ptr dstValues srcValues hValues)
  iframe

/-- Whether two views hold equal values. -/
def compare [ByteRepr T] [DecidableEq T] (left right : Buffer T) : Result Bool :=
  RawPtr.compareRange left.ptr right.ptr left.length

@[step]
theorem compare.spec [ByteRepr T] [DecidableEq T] (left right : Buffer T)
    (leftValues rightValues : List T)
    (hLength : left.length = right.length) :
    ⦃ left ↦ leftValues ∗ right ↦ rightValues ⦄
      Buffer.compare left right
      ⦃⇓ result => ⌜result = decide (leftValues = rightValues)⌝ ∗
        (left ↦ leftValues ∗ right ↦ rightValues)⦄ := by
  unfold Buffer.compare
  simp only [pointsTo_def]
  iintro hLeft hRight
  have hValues : leftValues.length = rightValues.length := by omega
  rw [← hLeft]
  apply WP.ispec_mono
    (RawPtr.compareRange.spec left.ptr right.ptr
      leftValues rightValues hValues)
  iframe

/-- Exchange the values at indices `i` and `j`. -/
def swap [ByteRepr T] (b : Buffer T) (i j : Nat) : Result Unit := do
  let x ← b.read i
  let y ← b.read j
  b.write i y
  b.write j x

@[step]
theorem swap.spec [ByteRepr T] (b : Buffer T) (values : List T) (i j : Nat)
    (hi : i < values.length) (hj : j < values.length) :
    ⦃ b ↦ values ⦄ b.swap i j
      ⦃⇓ b ↦ (values.set i values[j]).set j values[i]⦄ := by
  unfold Buffer.swap
  apply WP.ispec_bind (read.spec_buffer b values i hi) (sep_emp_r _).mpr
  intro x
  rw [sep_emp_r_eq]
  iintro hx
  subst x
  apply WP.ispec_bind (read.spec_buffer b values j hj) (sep_emp_r _).mpr
  intro y
  rw [sep_emp_r_eq]
  iintro hy
  subst y
  apply WP.ispec_bind (write.spec_buffer b values i values[j] hi)
    (sep_emp_r _).mpr
  intro _
  rw [sep_emp_r_eq]
  exact write.spec_buffer b (values.set i values[j]) j values[i]
    (by simpa using hj)

/-- Forget the recorded length and retain ownership of the underlying range. -/
theorem pointsTo_entails_range [ByteRepr T] (b : Buffer T) (values : List T) :
    b ↦ values ⊢ b.ptr ↦* values := by
  isimp

/-- Package ownership of a range as ownership of a buffer of matching length. -/
theorem range_entails_pointsTo [ByteRepr T] {b : Buffer T} {values : List T}
    (hLength : values.length = b.length) :
    b.ptr ↦* values ⊢ b ↦ values := by
  isimp

theorem pointsTo_split [ByteRepr T] (b : Buffer T) (values : List T) (i : Nat) :
    b.ptr ↦* values ⊣⊢
      (b.split i).1.ptr ↦* values.take i ∗
        (b.sub (values.take i).length (values.length - i)).ptr ↦*
          values.drop i := by
  rw [show (b.split i).1.ptr = b.ptr by simp [split, sub, ptr]]
  exact RawPtr.pointsToRange_split b.ptr values i

theorem pointsTo_join [ByteRepr T] (b₁ b₂ : Buffer T) (xs ys : List T)
    (hAdjacent : b₂.ptr = b₁.ptr.add xs.length) :
    b₁.ptr ↦* xs ∗ b₂.ptr ↦* ys ⊣⊢
      (b₁.join b₂).ptr ↦* (xs ++ ys) := by
  rw [hAdjacent]
  exact ⟨(RawPtr.pointsToRange_append b₁.ptr xs ys).mpr,
    (RawPtr.pointsToRange_append b₁.ptr xs ys).mp⟩

theorem pointsTo_sub [ByteRepr T] (b : Buffer T) (values : List T) (i : Nat) :
    b.ptr ↦* values ⊣⊢
      b.ptr ↦* values.take i ∗
        (b.sub (values.take i).length (values.length - i)).ptr ↦*
          values.drop i :=
  RawPtr.pointsToRange_split b.ptr values i

/-- Read a bounded subrange while framing the untouched prefix and suffix. -/
theorem readRange_sub.spec [ByteRepr T] (p : RawPtr T M) (values : List T) (i n : Nat)
    (hBounds : i + n ≤ values.length) :
    ⦃ p ↦* values ⦄ readRange (p.add i) n
      ⦃⇓ result =>
        ⌜result = (values.drop i).take n⌝ ∗ p ↦* values⦄ := by
  have hi : i ≤ values.length := by omega
  have hRest : n ≤ (values.drop i).length := by
    simp only [List.length_drop]
    omega
  have hTake : (values.take i).length = i := List.length_take_of_le hi
  have hBlock : ((values.drop i).take n).length = n :=
    List.length_take_of_le hRest
  rw [bientails_eq (RawPtr.pointsToRange_split p values i), hTake,
    bientails_eq
      (RawPtr.pointsToRange_split (p.add i) (values.drop i) n)]
  have hRead := readRange.spec (p.add i) ((values.drop i).take n)
  rw [hBlock] at hRead
  apply WP.ispec_mono hRead
  iframe

/-- Write a bounded subrange while framing the untouched prefix and suffix. -/
theorem writeRange_sub.spec [ByteRepr T] (p : MutRawPtr T) (old : List T) (i : Nat)
    (values : List T) (hBounds : i + values.length ≤ old.length) :
    ⦃ p ↦* old ⦄ writeRange (p.add i) values
      ⦃⇓ p ↦* old.setSlice! i values⦄ := by
  have hi : i ≤ old.length := by omega
  have hRest : values.length ≤ (old.drop i).length := by
    simp only [List.length_drop]
    omega
  have hTake : (old.take i).length = i := List.length_take_of_le hi
  have hBlock : ((old.drop i).take values.length).length = values.length :=
    List.length_take_of_le hRest
  have hReplace : old.setSlice! i values =
      old.take i ++ values ++ old.drop (i + values.length) := by
    have hSize : values.length ≤ old.length - i := by simpa using hRest
    simp only [List.setSlice!, Nat.min_eq_left hSize, List.take_length]
  rw [bientails_eq (RawPtr.pointsToRange_split p old i), hTake,
    bientails_eq
      (RawPtr.pointsToRange_split (p.add i) (old.drop i) values.length),
    hReplace]
  simp only [bientails_eq (RawPtr.pointsToRange_append _ _ _),
    List.length_append, hTake, hBlock, RawPtr.add_add, List.drop_drop]
  apply WP.ispec_mono
    (writeRange.spec (p.add i) ((old.drop i).take values.length)
      values hBlock)
  iframe

/-- Materialize a functional slice as fresh mutable memory. -/
def mut_to_raw [ByteRepr T] (slice : Slice T) : Result (Buffer T) :=
  RawPtr.allocArray slice.val fun q =>
    ⟨q.base, q.offset, slice.val.length⟩

@[step]
theorem mut_to_raw.spec [ByteRepr T] (slice : Slice T) :
    ⦃ emp ⦄ mut_to_raw slice ⦃⇓ b => b ↦ slice.val⦄ := by
  refine RawPtr.allocArray.spec _ _ _ fun q h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨rfl, hOwns⟩

/-- Refunctionalize a buffer and consume all of its memory ownership. -/
def end_mut_to_raw [ByteRepr T] (original : Slice T) (b : Buffer T) :
    Result (Slice T) := do
  let values ← MutRawPtr.takeRange b.ptr b.length
  pure (original.setSlice! 0 values)

@[step]
theorem end_mut_to_raw.spec [ByteRepr T] (original : Slice T) (b : Buffer T)
    (values : List T) :
    ⦃ b ↦ values ⦄ end_mut_to_raw original b
      ⦃⇓ result =>
        ⌜result.val = original.val.setSlice! 0 values⌝⦄ := by
  simp only [end_mut_to_raw, pointsTo_def]
  iintro hLength
  apply WP.ispec_bind
    (MutRawPtr.takeRange.spec_of_length b.ptr values b.length hLength)
    (sep_emp_r _).mpr
  intro result
  rw [sep_emp_r_eq]
  iintro hResult
  subst result
  apply (ispec_ok _).2
  simp [Slice.setSlice!_val]

end Buffer

def RawPtr.toBuffer {M} (p : RawPtr T M) (n : Nat) : Buffer T := ⟨p.base, p.offset, n⟩

@[simp] theorem RawPtr.toBuffer_ptr (p : MutRawPtr T) (n : Nat) :
    (p.toBuffer n).ptr = p := rfl

@[simp] theorem RawPtr.toBuffer_ptr_const (p : ConstRawPtr T) (n : Nat) :
    (p.toBuffer n).ptr = p.toMut := rfl

@[simp] theorem RawPtr.toBuffer_length {M} (p : RawPtr T M) (n : Nat) :
    (p.toBuffer n).length = n := rfl

def Slice.end_as_mut_ptr [ByteRepr T] (s : Slice T) (p : MutRawPtr T) : Result (Slice T) :=
  Buffer.end_mut_to_raw s (p.toBuffer s.length)

@[step]
theorem Slice.end_as_mut_ptr.spec [ByteRepr T] (s : Slice T) (p : MutRawPtr T) (values : List T)
    (hLength : values.length = s.length) :
    ⦃ p ↦* values ⦄ Slice.end_as_mut_ptr s p ⦃⇓ result => ⌜result.val = values⌝⦄ := by
  unfold Slice.end_as_mut_ptr
  apply WP.ispec_mono (Buffer.end_mut_to_raw.spec s (p.toBuffer s.length) values)
  have hSet : s.val.setSlice! 0 values = values := by
    apply List.ext_getElem <;> simp_all [List.setSlice!]
  simp only [Buffer.pointsTo_def, hSet, RawPtr.toBuffer_ptr, RawPtr.toBuffer_length, hLength]
  iframe

def Slice.end_as_ptr [ByteRepr T] (s : Slice T) (p : ConstRawPtr T) : Result Unit :=
  Buffer.free (p.toBuffer s.length)

@[step]
theorem Slice.end_as_ptr.spec [ByteRepr T] (s : Slice T) (p : ConstRawPtr T) :
    ⦃ p ↦* s.val ⦄ Slice.end_as_ptr s p ⦃⇓ emp⦄ := by
  unfold Slice.end_as_ptr
  apply WP.ispec_mono (Buffer.free.spec (p.toBuffer s.length) s.val)
  simp only [Buffer.pointsTo_def, RawPtr.toBuffer_length]
  iframe

@[rust_fun "core::slice::raw::from_raw_parts"]
def core.slice.raw.from_raw_parts [ByteRepr T] (p : ConstRawPtr T) (len : Usize) : Result (Slice T) :=
  Buffer.readSlice (p.toBuffer len.val)

@[step]
theorem core.slice.raw.from_raw_parts.spec [ByteRepr T] (p : ConstRawPtr T) (len : Usize) (s : Slice T)
    (hLength : s.length = len.val) :
    ⦃ p ↦* s.val ⦄ core.slice.raw.from_raw_parts p len
      ⦃⇓ result => ⌜result = s⌝ ∗ p ↦* s.val⦄ := by
  unfold core.slice.raw.from_raw_parts
  apply WP.ispec_mono (Buffer.readSlice.spec (p.toBuffer len.val) s)
  simp only [Buffer.pointsTo_def, RawPtr.toBuffer_ptr_const, RawPtr.toBuffer_length, hLength,
    RawPtr.pointsToRange_toMut]
  iframe

@[rust_fun "core::slice::raw::from_raw_parts_mut"]
def core.slice.raw.from_raw_parts_mut [ByteRepr T] (p : MutRawPtr T) (len : Usize) :
    Result (Slice T × (Slice T → Result Unit)) :=
  Aeneas.Std.bind (Buffer.readSlice (p.toBuffer len.val)) fun s =>
    Result.ok (s, Buffer.writeSlice (p.toBuffer len.val))

@[step]
theorem core.slice.raw.from_raw_parts_mut.spec [ByteRepr T] (p : MutRawPtr T) (len : Usize) (s : Slice T)
    (hLength : s.length = len.val) :
    ⦃ p ↦* s.val ⦄ core.slice.raw.from_raw_parts_mut p len
      ⦃⇓ result => ⌜result.1 = s ∧
        ∀ (old s' : Slice T), s'.length = old.length → old.length = len.val →
          ⦃ p ↦* old.val ⦄ result.2 s' ⦃⇓ p ↦* s'.val ⦄⌝ ∗ p ↦* s.val⦄ := by
  have hBack : ∀ (old s' : Slice T), s'.length = old.length → old.length = len.val →
      ⦃ p ↦* old.val ⦄ Buffer.writeSlice (p.toBuffer len.val) s' ⦃⇓ p ↦* s'.val ⦄ := by
    intro old s' h1 h2
    apply WP.ispec_mono (Buffer.writeSlice.spec (p.toBuffer len.val) old s' h1)
    simp only [Buffer.pointsTo_def, RawPtr.toBuffer_ptr, RawPtr.toBuffer_length, h2,
      Slice.length, h1]
    iframe
  have hPre : p ↦* s.val ⊢ (p.toBuffer len.val) ↦ s.val ∗ emp := by
    simp only [Buffer.pointsTo_def, RawPtr.toBuffer_ptr, RawPtr.toBuffer_length, ← hLength]
    iframe
  unfold core.slice.raw.from_raw_parts_mut
  apply WP.ispec_bind (Buffer.readSlice.spec (p.toBuffer len.val) s) hPre
  intro r
  rw [sep_emp_r_eq]
  iintro hr
  subst r
  rw [ispec_ok]
  simp only [Buffer.pointsTo_def, RawPtr.toBuffer_ptr, RawPtr.toBuffer_length]
  iintro hl
  have hPure : (s, Buffer.writeSlice (p.toBuffer len.val)).1 = s ∧
      ∀ (old s' : Slice T), s'.length = old.length → old.length = len.val →
        ⦃ p ↦* old.val ⦄ (s, Buffer.writeSlice (p.toBuffer len.val)).2 s' ⦃⇓ p ↦* s'.val ⦄ :=
    ⟨rfl, hBack⟩
  iframe
end Aeneas.Std
