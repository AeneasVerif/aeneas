import Aeneas.Std.RawPtr
import Aeneas.Std.Slice
import Aeneas.Tactic.SepLogic.Frame
import Aeneas.Tactic.SepLogic.Intro
import Aeneas.Tactic.Step.Init

/-!
# Buffers

`Buffer T` models a mutable Rust slice `&mut [T]`: a bounded view into an
allocation, represented by a base address, an offset, and a length. The value
itself carries no permission; `b ↦ values` owns the slots it spans.

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
def ptrAt (b : Buffer T) (i : Nat) : MutRawPtr T :=
  ⟨b.base, b.offset + i⟩

/-- The sub-view of `n` slots starting at index `i`. -/
def sub (b : Buffer T) (i n : Nat) : Buffer T :=
  ⟨b.base, b.offset + i, n⟩

/-- Split a view at index `i`. -/
def split (b : Buffer T) (i : Nat) : Buffer T × Buffer T :=
  (b.sub 0 i, b.sub i (b.length - i))

/-- Join adjacent views. Ownership lemmas establish when the join is valid. -/
def join (b₁ b₂ : Buffer T) : Buffer T :=
  ⟨b₁.base, b₁.offset, b₁.length + b₂.length⟩

/-- `b` owns its slots, holding `values`. -/
def pointsTo (b : Buffer T) (values : List T) : IProp :=
  iprop(⌜values.length = b.length⌝ ∗ b.ptr ↦* values)

end Buffer

instance instPointsToBuffer {T : Type} :
    PointsTo (Buffer T) (List T) := ⟨Buffer.pointsTo⟩

namespace Buffer

/-- Allocate `n` slots holding `value`. -/
def alloc (n : Nat) (value : T) : Result (Buffer T) :=
  RawPtr.allocArray (List.replicate n value) fun r =>
    ⟨r.base, r.offset, n⟩

@[step]
theorem alloc.spec (n : Nat) (value : T) :
    ⦃ emp ⦄ Buffer.alloc n value
      ⦃⇓ b => b ↦ List.replicate n value⦄ := by
  refine RawPtr.allocArray.spec _ _ _ fun r h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨by simp, hOwns⟩

/-- A buffer owns exactly the range addressed by its pointer. -/
theorem pointsTo_def (b : Buffer T) (values : List T) :
    (b ↦ values) =
      iprop(⌜values.length = b.length⌝ ∗ b.ptr ↦* values) := rfl

/-- Read slot `i`. -/
def read (b : Buffer T) (i : Nat) : Result T :=
  RawPtr.read (b.ptrAt i)

@[step]
theorem read.spec (b : Buffer T) (i : Nat) (value : T) :
    ⦃ b.ptrAt i ↦ value ⦄ b.read i
      ⦃⇓ result => ⌜result = value⌝ ∗ b.ptrAt i ↦ value⦄ :=
  RawPtr.read.spec (b.ptrAt i) value

/-- Write slot `i`. -/
def write (b : Buffer T) (i : Nat) (value : T) : Result Unit :=
  MutRawPtr.write (b.ptrAt i) value

@[step]
theorem write.spec (b : Buffer T) (i : Nat) (oldValue newValue : T) :
    ⦃ b.ptrAt i ↦ oldValue ⦄ b.write i newValue
      ⦃⇓ b.ptrAt i ↦ newValue⦄ :=
  MutRawPtr.write.spec (b.ptrAt i) oldValue newValue

/-- Release every slot spanned by the view. -/
def free (b : Buffer T) : Result Unit :=
  MutRawPtr.freeRange b.ptr b.length

@[step]
theorem free.spec (b : Buffer T) (values : List T) :
    ⦃ b ↦ values ⦄ b.free ⦃⇓ emp⦄ := by
  unfold Buffer.free
  simp only [pointsTo_def]
  iintro hLength
  rw [← hLength]
  exact MutRawPtr.freeRange.spec b.ptr values

/-- A view spans as many slots as the values it owns. -/
theorem length_of_pointsTo {b : Buffer T} {values : List T} {h : Heap}
    (hPointsTo : (b ↦ values) h) : values.length = b.length :=
  ((sep_pure_l _ _ h).mp hPointsTo).1

theorem read.spec_buffer (b : Buffer T) (values : List T) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ b ↦ values ⦄ b.read i
      ⦃⇓ result => ⌜result = values[i]⌝ ∗ b ↦ values⦄ := by
  change ispec _ (RawPtr.read (b.ptr.add i)) _
  simp only [pointsTo_def]
  iintro hLength
  apply WP.ispec_mono (RawPtr.read.spec_range b.ptr values i hIndex)
  iframe

theorem write.spec_buffer (b : Buffer T) (values : List T) (i : Nat)
    (value : T) (hIndex : i < values.length) :
    ⦃ b ↦ values ⦄ b.write i value
      ⦃⇓ b ↦ values.set i value⦄ := by
  change ispec _ (MutRawPtr.write (b.ptr.add i) value) _
  simp only [pointsTo_def]
  iintro hLength
  apply WP.ispec_mono
    (MutRawPtr.write.spec_range b.ptr values i value hIndex)
  iframe

/-- Allocate a view containing exactly `values`. -/
def ofList (values : List T) : Result (Buffer T) :=
  RawPtr.allocArray values fun r =>
    ⟨r.base, r.offset, values.length⟩

@[step]
theorem ofList.spec (values : List T) :
    ⦃ emp ⦄ Buffer.ofList values ⦃⇓ b => b ↦ values⦄ := by
  refine RawPtr.allocArray.spec _ _ _ fun r h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨rfl, hOwns⟩

/-- Overwrite every slot with `value`. -/
def fill (b : Buffer T) (value : T) : Result Unit :=
  MutRawPtr.fillRange b.ptr value b.length

@[step]
theorem fill.spec (b : Buffer T) (values : List T) (value : T) :
    ⦃ b ↦ values ⦄ b.fill value
      ⦃⇓ b ↦ List.replicate b.length value⦄ := by
  unfold Buffer.fill
  simp only [pointsTo_def]
  iintro hLength
  rw [← hLength]
  apply WP.ispec_mono (MutRawPtr.fillRange.spec b.ptr values value)
  iframe

/-- Extract the length facts and underlying ranges of two owned buffers. -/
theorem pointsTo_pair_entails (b₁ b₂ : Buffer T)
    (values₁ values₂ : List T) :
    b₁ ↦ values₁ ∗ b₂ ↦ values₂ ⊢
      iprop(⌜values₁.length = b₁.length ∧
          values₂.length = b₂.length⌝ ∗
        (b₁.ptr ↦* values₁ ∗ b₂.ptr ↦* values₂)) := by
  rintro heap ⟨h₁, h₂, hCompatible, rfl, hOne, hTwo⟩
  obtain ⟨hLength₁, hRange₁⟩ := (sep_pure_l _ _ h₁).mp hOne
  obtain ⟨hLength₂, hRange₂⟩ := (sep_pure_l _ _ h₂).mp hTwo
  exact (sep_pure_l _ _ _).mpr
    ⟨⟨hLength₁, hLength₂⟩, h₁, h₂, hCompatible, rfl, hRange₁, hRange₂⟩

/-- Reassemble two buffer ownership assertions from their ranges. -/
theorem pair_entails_pointsTo {b₁ b₂ : Buffer T}
    {values₁ values₂ : List T}
    (hLength₁ : values₁.length = b₁.length)
    (hLength₂ : values₂.length = b₂.length) :
    b₁.ptr ↦* values₁ ∗ b₂.ptr ↦* values₂ ⊢
      b₁ ↦ values₁ ∗ b₂ ↦ values₂ := by
  rintro heap ⟨h₁, h₂, hCompatible, rfl, hRange₁, hRange₂⟩
  exact ⟨h₁, h₂, hCompatible, rfl,
    (sep_pure_l _ _ h₁).mpr ⟨hLength₁, hRange₁⟩,
    (sep_pure_l _ _ h₂).mpr ⟨hLength₂, hRange₂⟩⟩

/-- Copy every slot of `src` into `dst`. -/
def copy (dst src : Buffer T) : Result Unit :=
  MutRawPtr.copyRange dst.ptr src.ptr src.length

@[step]
theorem copy.spec (dst src : Buffer T) (dstValues srcValues : List T)
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
def compare [DecidableEq T] (left right : Buffer T) : Result Bool :=
  RawPtr.compareRange left.ptr right.ptr left.length

@[step]
theorem compare.spec [DecidableEq T] (left right : Buffer T)
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
def swap (b : Buffer T) (i j : Nat) : Result Unit := do
  let x ← b.read i
  let y ← b.read j
  b.write i y
  b.write j x

theorem swap.spec (b : Buffer T) (values : List T) (i j : Nat)
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
theorem pointsTo_entails_range (b : Buffer T) (values : List T) :
    b ↦ values ⊢ b.ptr ↦* values :=
  fun h hPointsTo => ((sep_pure_l _ _ h).mp hPointsTo).2

/-- Package ownership of a range as ownership of a buffer of matching length. -/
theorem range_entails_pointsTo {b : Buffer T} {values : List T}
    (hLength : values.length = b.length) :
    b.ptr ↦* values ⊢ b ↦ values :=
  fun h hRange => (sep_pure_l _ _ h).mpr ⟨hLength, hRange⟩

theorem pointsTo_split (b : Buffer T) (values : List T) (i : Nat) :
    b.ptr ↦* values ⊣⊢
      (b.split i).1.ptr ↦* values.take i ∗
        (b.sub (values.take i).length (values.length - i)).ptr ↦*
          values.drop i :=
  RawPtr.pointsToRange_split b.ptr values i

theorem pointsTo_join (b₁ b₂ : Buffer T) (xs ys : List T)
    (hAdjacent : b₂.ptr = b₁.ptr.add xs.length) :
    b₁.ptr ↦* xs ∗ b₂.ptr ↦* ys ⊣⊢
      (b₁.join b₂).ptr ↦* (xs ++ ys) := by
  rw [hAdjacent]
  exact ⟨(RawPtr.pointsToRange_append b₁.ptr xs ys).mpr,
    (RawPtr.pointsToRange_append b₁.ptr xs ys).mp⟩

theorem pointsTo_sub (b : Buffer T) (values : List T) (i : Nat) :
    b.ptr ↦* values ⊣⊢
      b.ptr ↦* values.take i ∗
        (b.sub (values.take i).length (values.length - i)).ptr ↦*
          values.drop i :=
  RawPtr.pointsToRange_split b.ptr values i

/-- Materialize a functional slice as fresh mutable memory. -/
def mut_to_raw (slice : Slice T) : Result (Buffer T) :=
  RawPtr.allocArray slice.val fun r =>
    ⟨r.base, r.offset, slice.val.length⟩

@[step]
theorem mut_to_raw.spec (slice : Slice T) :
    ⦃ emp ⦄ mut_to_raw slice ⦃⇓ b => b ↦ slice.val⦄ := by
  refine RawPtr.allocArray.spec _ _ _ fun r h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨rfl, hOwns⟩

/-- Refunctionalize a buffer and consume all of its memory ownership. -/
def end_mut_to_raw (original : Slice T) (b : Buffer T) :
    Result (Slice T) := do
  let values ← MutRawPtr.takeRange b.ptr b.length
  pure (original.setSlice! 0 values)

@[step]
theorem end_mut_to_raw.spec (original : Slice T) (b : Buffer T)
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

end Aeneas.Std
