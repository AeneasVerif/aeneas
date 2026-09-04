import Aeneas.SLPoC.MutableData.Buffer
import Aeneas.Std.Array.Array

/-!
# Arrays

`Array α n` is the Rust array `[α; n]`: `n` consecutive slots of the allocation
of [`Ptr.lean`](Ptr.lean), reached through one pointer.  What distinguishes it
from the `Buffer α` of [`Buffer.lean`](Buffer.lean) is where the length lives —
in the *type* of an array, in a *field* of a buffer — which is exactly the
difference between `[T; N]` and `&mut [T]`.

`Array.toBuffer` is that coercion, and it costs nothing: `a ↦ values` and
`a.toBuffer ↦ values` are the same assertion.  Operations reuse the
corresponding buffer implementation, with cell-local primitive specifications
and whole-array derived specifications where appropriate.
-/

namespace Aeneas.SLPoC

open Aeneas.Std (Heap Result)

variable {α : Type} {n : Nat}

/-- A Rust array `[α; n]`: `n` consecutive slots reached through `ptr`. -/
structure Array (α : Type) (n : Nat) where
  ptr : Ptr α
  /- As for `Ptr` and `Buffer`, being inhabited is what makes the `unwrap`s of
     a translated Rust program expressible as `Option.get!`. -/
  deriving Inhabited, DecidableEq

namespace Array

/-- The pointer to the slot at index `i`. -/
def ptrAt (a : Array α n) (i : Nat) : Ptr α := a.ptr.add i

/-- The slice spanning the whole array: `[T; N]` seen as `&mut [T]`. -/
def toBuffer (a : Array α n) : Buffer α := ⟨a.ptr.base, a.ptr.offset, n⟩

/-- How many slots the array spans.  It is a fact about the type, not a read
from memory. -/
def length (_ : Array α n) : Nat := n

/-- `a` owns its `n` slots, holding `values`. -/
def pointsTo (a : Array α n) (values : List α) : IProp :=
  iprop(⌜values.length = n⌝ ∗ a.ptr ↦* values)

end Array

instance instPointsToArray {α : Type} {n : Nat} :
    PointsTo (Array α n) (List α) := ⟨Array.pointsTo⟩

namespace Array

@[simp] theorem length_toBuffer (a : Array α n) : a.toBuffer.length = n := rfl

@[simp] theorem ptr_toBuffer (a : Array α n) : a.toBuffer.ptr = a.ptr := rfl

/-- Owning an array is owning the slice that spans it.  The two assertions are
literally the same, so ownership crosses the coercion for free. -/
theorem pointsTo_eq_buffer (a : Array α n) (values : List α) :
    (a ↦ values) = (a.toBuffer ↦ values) := rfl

/-- An array holds exactly `n` values. -/
theorem length_of_pointsTo {a : Array α n} {values : List α} {h : Heap}
    (hPointsTo : (a ↦ values) h) : values.length = n :=
  Buffer.length_of_pointsTo (b := a.toBuffer) hPointsTo

/-- Forget the length the type records and keep the range the array owns. -/
theorem pointsTo_entails_range (a : Array α n) (values : List α) :
    a ↦ values ⊢ a.ptr ↦* values :=
  Buffer.pointsTo_entails_range a.toBuffer values

/-- Own an array of a range of the right length. -/
theorem range_entails_pointsTo {a : Array α n} {values : List α}
    (hLength : values.length = n) : a.ptr ↦* values ⊢ a ↦ values :=
  Buffer.range_entails_pointsTo (b := a.toBuffer) hLength

/-! ## Allocation and deallocation -/

/-- Allocate an array of `n` slots, each holding `value`. -/
def alloc (α : Type) (n : Nat) (value : α) : Result (Array α n) :=
  allocArray (List.replicate n value) fun r => ⟨⟨r.base, r.offset⟩⟩

@[step]
theorem alloc.spec (α : Type) (n : Nat) (value : α) :
    ⦃ emp ⦄ Array.alloc α n value
      ⦃⇓ a => a ↦ List.replicate n value⦄ := by
  refine allocArray.spec _ _ _ fun r h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨by simp, hOwns⟩

/-- Allocate an array holding exactly `values`. -/
def ofList (values : List α) : Result (Array α values.length) :=
  allocArray values fun r => ⟨⟨r.base, r.offset⟩⟩

@[step]
theorem ofList.spec (values : List α) :
    ⦃ emp ⦄ Array.ofList values ⦃⇓ a => a ↦ values⦄ := by
  refine allocArray.spec _ _ _ fun r h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨rfl, hOwns⟩

/-- Release every slot of the array. -/
def free (a : Array α n) : Result Unit := a.toBuffer.free

@[step]
theorem free.spec (a : Array α n) (values : List α) :
    ⦃ a ↦ values ⦄ a.free ⦃⇓ emp⦄ :=
  Buffer.free.spec a.toBuffer values

/-! ## Indexed access

The primitive specifications own only the slot they access.  The array-level
specifications below derive that ownership from the complete array and
reassemble it afterward. -/

/-- Read the value at index `i`. -/
def read (a : Array α n) (i : Nat) : Result α := a.toBuffer.read i

@[step]
theorem read.spec (a : Array α n) (i : Nat) (value : α) :
    ⦃ a.ptrAt i ↦ value ⦄ a.read i
      ⦃⇓ result => ⌜result = value⌝ ∗ a.ptrAt i ↦ value⦄ :=
  Buffer.read.spec a.toBuffer i value

theorem read.spec_array (a : Array α n) (values : List α) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ a ↦ values ⦄ a.read i
      ⦃⇓ result => ⌜result = values[i]⌝ ∗ a ↦ values⦄ :=
  Buffer.read.spec_array a.toBuffer values i hIndex

/-- Write `value` at index `i`. -/
def write (a : Array α n) (i : Nat) (value : α) : Result Unit :=
  a.toBuffer.write i value

@[step]
theorem write.spec (a : Array α n) (i : Nat) (oldValue newValue : α) :
    ⦃ a.ptrAt i ↦ oldValue ⦄ a.write i newValue
      ⦃⇓ a.ptrAt i ↦ newValue⦄ :=
  Buffer.write.spec a.toBuffer i oldValue newValue

theorem write.spec_array (a : Array α n) (values : List α) (i : Nat)
    (value : α) (hIndex : i < values.length) :
    ⦃ a ↦ values ⦄ a.write i value ⦃⇓ a ↦ values.set i value⦄ :=
  Buffer.write.spec_array a.toBuffer values i value hIndex

/-- Exchange the values at indices `i` and `j`. -/
def swap (a : Array α n) (i j : Nat) : Result Unit := a.toBuffer.swap i j

theorem swap.spec (a : Array α n) (values : List α) (i j : Nat)
    (hi : i < values.length) (hj : j < values.length) :
    ⦃ a ↦ values ⦄ a.swap i j
      ⦃⇓ a ↦ (values.set i values[j]).set j values[i]⦄ :=
  Buffer.swap.spec a.toBuffer values i j hi hj

/-! ## Bulk operations -/

/-- Overwrite every slot with `value`. -/
def fill (a : Array α n) (value : α) : Result Unit := a.toBuffer.fill value

@[step]
theorem fill.spec (a : Array α n) (values : List α) (value : α) :
    ⦃ a ↦ values ⦄ a.fill value ⦃⇓ a ↦ List.replicate n value⦄ :=
  Buffer.fill.spec a.toBuffer values value

/-- Copy every slot of `src` into `dst`.  Both arrays have `n` slots by their
type, so nothing has to be checked. -/
def copy (dst src : Array α n) : Result Unit := dst.toBuffer.copy src.toBuffer

@[step]
theorem copy.spec (dst src : Array α n) (dstValues srcValues : List α) :
    ⦃ dst ↦ dstValues ∗ src ↦ srcValues ⦄ dst.copy src
      ⦃⇓ dst ↦ srcValues ∗ src ↦ srcValues⦄ :=
  Buffer.copy.spec dst.toBuffer src.toBuffer dstValues srcValues rfl

/-- Whether two arrays hold the same values. -/
def compare [DecidableEq α] (left right : Array α n) : Result Bool :=
  Buffer.compare left.toBuffer right.toBuffer

@[step]
theorem compare.spec [DecidableEq α] (left right : Array α n)
    (leftValues rightValues : List α) :
    ⦃ left ↦ leftValues ∗ right ↦ rightValues ⦄ Array.compare left right
      ⦃⇓ result => ⌜result = decide (leftValues = rightValues)⌝ ∗
        (left ↦ leftValues ∗ right ↦ rightValues)⦄ :=
  Buffer.compare.spec left.toBuffer right.toBuffer leftValues rightValues rfl

end Array

/-! ## Slices of statically known length -/

/-- Read a slice back as an array of the length its type records. -/
def Buffer.toArray (b : Buffer α) (n : Nat) : Array α n := ⟨b.ptr⟩

theorem Buffer.pointsTo_toArray {b : Buffer α} {values : List α}
    (hLength : values.length = n) : b ↦ values ⊢ (b.toArray n) ↦ values :=
  entails_trans (Buffer.pointsTo_entails_range b values)
    (Array.range_entails_pointsTo (a := b.toArray n) hLength)

namespace Array

/-! ## Turning a functional mutable array into memory and back -/

/-- Materialize a functional array as a fresh mutable memory array. -/
def mut_to_raw {N : Aeneas.Std.Usize} (value : Aeneas.Std.Array α N) :
    Result (Array α N.val) :=
  allocArray value.val fun r => ⟨⟨r.base, r.offset⟩⟩

@[step]
theorem mut_to_raw.spec {N : Aeneas.Std.Usize} (value : Aeneas.Std.Array α N) :
    ⦃ emp ⦄ mut_to_raw value ⦃⇓ a => a ↦ value.val⦄ := by
  refine allocArray.spec _ _ _ fun r h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨value.property, hOwns⟩

/-- Refunctionalize a mutable array, consuming all of its memory ownership. -/
def end_mut_to_raw {N : Aeneas.Std.Usize} (original : Aeneas.Std.Array α N)
    (a : Array α N.val) :
    Result (Aeneas.Std.Array α N) := do
  let values ← takeRange a.ptr N.val
  pure (original.setSlice! 0 values)

@[step]
theorem end_mut_to_raw.spec {N : Aeneas.Std.Usize}
    (original : Aeneas.Std.Array α N) (a : Array α N.val) (values : List α) :
    ⦃ a ↦ values ⦄ end_mut_to_raw original a
      ⦃⇓ result => ⌜result.val = values⌝⦄ := by
  unfold end_mut_to_raw
  apply triple_ipure
  intro hLength
  have hTake :
      ⦃ a.ptr ↦* values ⦄ takeRange a.ptr N.val
        ⦃⇓ result => ⌜result = values⌝⦄ := by
    exact takeRange.spec_of_length a.ptr values N.val hLength
  apply triple_bind hTake
  intro result
  exact triple_pure fun _ hResult => by
    rw [hResult]
    simp only [Aeneas.Std.Array.setSlice!]
    simp [List.setSlice!, hLength, original.property]

end Array

end Aeneas.SLPoC
