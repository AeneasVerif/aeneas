import Aeneas.SLPoC.MutableData.Ptr
import Aeneas.Std.Slice

/-!
# Buffers

`Buffer α` is the Rust slice `&mut [T]`: a bounded view of the allocation of
[`Ptr.lean`](Ptr.lean), made of a base address, an offset and a length.  Like
an interior pointer it carries no permission — `b ↦ values` is what owns the
slots it spans — and the view is only a *value*: `sub`, `split` and `join`
compute new views, while the lemmas below say how ownership follows them.

Every operation reduces to a pointer operation, and none has a precondition:
`Buffer.sub b i n` and `Buffer.split b i` are total, and a read or a write out
of the range the caller owns simply has no provable triple.

Reads and writes come with two specifications: a slot-level one, which is the
primitive and the one `step` uses, and an array-level one, which owns the whole
view and gives it back.  [`Array.lean`](Array.lean) puts the length in the type
on top of this.
-/

namespace Aeneas.SLPoC

variable {α : Type}

/-- A bounded view of an allocation. -/
structure Buffer (α : Type) where
  base : AllocId
  offset : Nat
  length : Nat
  /- As for `Ptr`, being inhabited is what makes the `unwrap`s of a translated
     Rust program expressible as `Option.get!`. -/
  deriving Inhabited, DecidableEq

namespace Buffer

/-- The pointer to the first slot of the view. -/
def ptr (b : Buffer α) : Ptr α := ⟨b.base, b.offset⟩

/-- The pointer to the slot at index `i` of the view. -/
def ptrAt (b : Buffer α) (i : Nat) : Ptr α := ⟨b.base, b.offset + i⟩

/-- The sub-view of `n` slots from index `i`. -/
def sub (b : Buffer α) (i n : Nat) : Buffer α := ⟨b.base, b.offset + i, n⟩

/-- Split the view at index `i`. -/
def split (b : Buffer α) (i : Nat) : Buffer α × Buffer α :=
  (b.sub 0 i, b.sub i (b.length - i))

/-- Join two views; the value is the left one widened, ownership is what the
join lemma transfers. -/
def join (b₁ b₂ : Buffer α) : Buffer α :=
  ⟨b₁.base, b₁.offset, b₁.length + b₂.length⟩

/-- `b` owns the slots it spans, holding `values`. -/
def pointsTo (b : Buffer α) (values : List α) : IProp :=
  iprop(⌜values.length = b.length⌝ ∗ b.ptr.pointsToRange values)

end Buffer

instance instPointsToBuffer {α : Type} : PointsTo (Buffer α) (List α) :=
  ⟨Buffer.pointsTo⟩

/-! ## Allocation -/

/-- Allocate `n` slots holding `value`. -/
def Buffer.alloc (n : Nat) (value : α) : Result (Buffer α) :=
  allocArray (List.replicate n value) fun r => ⟨r.base, r.offset, n⟩

@[step]
theorem Buffer.alloc.spec (n : Nat) (value : α) :
    ⦃ emp ⦄ Buffer.alloc n value ⦃⇓ b => b ↦ List.replicate n value⦄ := by
  refine allocArray.spec _ _ _ fun r h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨by simp, hOwns⟩

/-! ## Indexed access and deallocation -/

namespace Buffer

def read (b : Buffer α) (i : Nat) : Result α := _root_.Aeneas.SLPoC.read (b.ptrAt i)

@[step]
theorem read.spec (b : Buffer α) (i : Nat) (value : α) :
    ⦃ (b.ptrAt i) ↦ value ⦄ b.read i
      ⦃⇓ result => ⌜result = value⌝ ∗ (b.ptrAt i) ↦ value⦄ :=
  _root_.Aeneas.SLPoC.read.spec (b.ptrAt i) value

def write (b : Buffer α) (i : Nat) (value : α) : Result Unit :=
  _root_.Aeneas.SLPoC.update (b.ptrAt i) value

@[step]
theorem write.spec (b : Buffer α) (i : Nat) (oldValue newValue : α) :
    ⦃ (b.ptrAt i) ↦ oldValue ⦄ b.write i newValue
      ⦃⇓ (b.ptrAt i) ↦ newValue⦄ :=
  _root_.Aeneas.SLPoC.update.spec (b.ptrAt i) oldValue newValue

/-- Release every slot the view spans. -/
def free (b : Buffer α) : Result Unit := freeRange b.ptr b.length

@[step]
theorem free.spec (b : Buffer α) (values : List α) :
    ⦃ b ↦ values ⦄ b.free ⦃⇓ emp⦄ := by
  apply triple_ipure
  intro hLength
  show triple _ (freeRange b.ptr b.length) _
  rw [← hLength]
  exact freeRange.spec b.ptr values

/-! ## The array interface

The specifications above own the single slot they touch; these own the whole
view and give it back, which is the contract a client of an array wants.  As in
[`Ptr.lean`](Ptr.lean) they are not registered with `step`, so that the
slot-level ones stay unambiguous. -/

/-- A view spans as many slots as the values it holds. -/
theorem length_of_pointsTo {b : Buffer α} {values : List α} {h : Heap}
    (hPointsTo : (b ↦ values) h) : values.length = b.length :=
  ((sep_pure_l _ _ h).mp hPointsTo).1

theorem read.spec_array (b : Buffer α) (values : List α) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ b ↦ values ⦄ b.read i
      ⦃⇓ result => ⌜result = values[i]⌝ ∗ b ↦ values⦄ := by
  apply triple_ipure
  intro hLength
  refine triple_conseq (_root_.Aeneas.SLPoC.read.spec_range b.ptr values i hIndex)
    (entails_refl _) fun result h hPost => ?_
  obtain ⟨hResult, hRange⟩ := (sep_pure_l _ _ h).mp hPost
  exact (sep_pure_l _ _ h).mpr
    ⟨hResult, (sep_pure_l _ _ h).mpr ⟨hLength, hRange⟩⟩

theorem write.spec_array (b : Buffer α) (values : List α) (i : Nat) (value : α)
    (hIndex : i < values.length) :
    ⦃ b ↦ values ⦄ b.write i value ⦃⇓ b ↦ values.set i value⦄ := by
  apply triple_ipure
  intro hLength
  refine triple_conseq
    (_root_.Aeneas.SLPoC.update.spec_range b.ptr values i value hIndex)
    (entails_refl _) fun _ h hPost => ?_
  exact (sep_pure_l _ _ h).mpr ⟨by simpa using hLength, hPost⟩

/-! ## Bulk operations

Each is the range operation of [`Ptr.lean`](Ptr.lean) run over the slots the
view spans. -/

/-- Allocate a view holding exactly `values`. -/
def ofList (values : List α) : Result (Buffer α) :=
  allocArray values fun r => ⟨r.base, r.offset, values.length⟩

@[step]
theorem ofList.spec (values : List α) :
    ⦃ emp ⦄ Buffer.ofList values ⦃⇓ b => b ↦ values⦄ := by
  refine allocArray.spec _ _ _ fun r h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨rfl, hOwns⟩

/-- Overwrite every slot with `value`. -/
def fill (b : Buffer α) (value : α) : Result Unit := fillRange b.ptr value b.length

@[step]
theorem fill.spec (b : Buffer α) (values : List α) (value : α) :
    ⦃ b ↦ values ⦄ b.fill value
      ⦃⇓ b ↦ List.replicate b.length value⦄ := by
  apply triple_ipure
  intro hLength
  show triple _ (fillRange b.ptr value b.length) _
  rw [← hLength]
  refine triple_conseq (fillRange.spec b.ptr values value) (entails_refl _)
    fun _ h hPost => (sep_pure_l _ _ h).mpr ⟨by simp [hLength], hPost⟩

/-- The two length facts a binary operation needs, pulled out of what its two
views own. -/
theorem pointsTo_pair_entails (b₁ b₂ : Buffer α) (values₁ values₂ : List α) :
    b₁ ↦ values₁ ∗ b₂ ↦ values₂ ⊢
      iprop(⌜values₁.length = b₁.length ∧ values₂.length = b₂.length⌝ ∗
        (b₁.ptr ↦* values₁ ∗ b₂.ptr ↦* values₂)) := by
  rintro heap ⟨h₁, h₂, hCompatible, rfl, hOne, hTwo⟩
  obtain ⟨hLength₁, hRange₁⟩ := (sep_pure_l _ _ h₁).mp hOne
  obtain ⟨hLength₂, hRange₂⟩ := (sep_pure_l _ _ h₂).mp hTwo
  exact (sep_pure_l _ _ _).mpr
    ⟨⟨hLength₁, hLength₂⟩, h₁, h₂, hCompatible, rfl, hRange₁, hRange₂⟩

/-- …and put back. -/
theorem pair_entails_pointsTo {b₁ b₂ : Buffer α} {values₁ values₂ : List α}
    (hLength₁ : values₁.length = b₁.length)
    (hLength₂ : values₂.length = b₂.length) :
    b₁.ptr ↦* values₁ ∗ b₂.ptr ↦* values₂ ⊢ b₁ ↦ values₁ ∗ b₂ ↦ values₂ := by
  rintro heap ⟨h₁, h₂, hCompatible, rfl, hRange₁, hRange₂⟩
  exact ⟨h₁, h₂, hCompatible, rfl,
    (sep_pure_l _ _ h₁).mpr ⟨hLength₁, hRange₁⟩,
    (sep_pure_l _ _ h₂).mpr ⟨hLength₂, hRange₂⟩⟩

/-- Copy every slot of `src` into `dst`. -/
def copy (dst src : Buffer α) : Result Unit := copyRange dst.ptr src.ptr src.length

@[step]
theorem copy.spec (dst src : Buffer α) (dstValues srcValues : List α)
    (hLength : dst.length = src.length) :
    ⦃ dst ↦ dstValues ∗ src ↦ srcValues ⦄ dst.copy src
      ⦃⇓ dst ↦ srcValues ∗ src ↦ srcValues⦄ := by
  refine triple_conseq ?_ (pointsTo_pair_entails dst src dstValues srcValues)
    (fun _ => entails_refl _)
  apply triple_ipure
  rintro ⟨hDst, hSrc⟩
  show triple _ (copyRange dst.ptr src.ptr src.length) _
  rw [← hSrc]
  exact triple_conseq
    (copyRange.spec dst.ptr src.ptr dstValues srcValues (by omega))
    (entails_refl _)
    (fun _ => pair_entails_pointsTo (by omega) hSrc)

/-- Whether two views hold the same values. -/
def compare [DecidableEq α] (left right : Buffer α) : Result Bool :=
  compareRange left.ptr right.ptr left.length

@[step]
theorem compare.spec [DecidableEq α] (left right : Buffer α)
    (leftValues rightValues : List α) (hLength : left.length = right.length) :
    ⦃ left ↦ leftValues ∗ right ↦ rightValues ⦄ Buffer.compare left right
      ⦃⇓ result => ⌜result = decide (leftValues = rightValues)⌝ ∗
        (left ↦ leftValues ∗ right ↦ rightValues)⦄ := by
  refine triple_conseq ?_
    (pointsTo_pair_entails left right leftValues rightValues)
    (fun _ => entails_refl _)
  apply triple_ipure
  rintro ⟨hLeft, hRight⟩
  show triple _ (compareRange left.ptr right.ptr left.length) _
  rw [← hLeft]
  refine triple_conseq
    (compareRange.spec left.ptr right.ptr leftValues rightValues (by omega))
    (entails_refl _) fun result h hPost => ?_
  obtain ⟨hResult, hRanges⟩ := (sep_pure_l _ _ h).mp hPost
  exact (sep_pure_l _ _ h).mpr
    ⟨hResult, pair_entails_pointsTo hLeft hRight h hRanges⟩

/-- Exchange the values at indices `i` and `j`. -/
def swap (b : Buffer α) (i j : Nat) : Result Unit := do
  let x ← b.read i
  let y ← b.read j
  b.write i y
  b.write j x

theorem swap.spec (b : Buffer α) (values : List α) (i j : Nat)
    (hi : i < values.length) (hj : j < values.length) :
    ⦃ b ↦ values ⦄ b.swap i j
      ⦃⇓ b ↦ (values.set i values[j]).set j values[i]⦄ := by
  unfold Buffer.swap
  apply triple_bind (read.spec_array b values i hi)
  intro x
  apply triple_ipure
  intro hx
  apply triple_bind (read.spec_array b values j hj)
  intro y
  apply triple_ipure
  intro hy
  rw [hx, hy]
  apply triple_bind (write.spec_array b values i values[j] hi)
  intro _
  exact write.spec_array b (values.set i values[j]) j values[i]
    (by simpa using hj)

/-! ## How ownership follows the views -/

/-- A buffer owns the range its pointer owns. -/
theorem pointsTo_def (b : Buffer α) (values : List α) :
    (b ↦ values) = iprop(⌜values.length = b.length⌝ ∗ b.ptr ↦* values) := rfl

/-- Forget the length the view records and keep the range it owns. -/
theorem pointsTo_entails_range (b : Buffer α) (values : List α) :
    b ↦ values ⊢ b.ptr ↦* values :=
  fun h hPointsTo => ((sep_pure_l _ _ h).mp hPointsTo).2

/-- Own a view of a range. -/
theorem range_entails_pointsTo {b : Buffer α} {values : List α}
    (hLength : values.length = b.length) : b.ptr ↦* values ⊢ b ↦ values :=
  fun h hRange => (sep_pure_l _ _ h).mpr ⟨hLength, hRange⟩

/-- `Buffer.split`: the halves own the halves of the range, and both are
interior to the same allocation. -/
theorem pointsTo_split (b : Buffer α) (values : List α) (i : Nat) :
    b.ptr ↦* values ⊣⊢
      (b.split i).1.ptr ↦* values.take i ∗
        (b.sub (values.take i).length (values.length - i)).ptr ↦*
          values.drop i :=
  Ptr.pointsToRange_split b.ptr values i

/-- `Buffer.join`: adjacent views join their ranges.  Joining recombines
ownership without changing either pointer value. -/
theorem pointsTo_join (b₁ b₂ : Buffer α) (xs ys : List α)
    (hAdjacent : b₂.ptr = b₁.ptr.add xs.length) :
    b₁.ptr ↦* xs ∗ b₂.ptr ↦* ys ⊣⊢ (b₁.join b₂).ptr ↦* (xs ++ ys) := by
  rw [hAdjacent]
  exact ⟨(Ptr.pointsToRange_append b₁.ptr xs ys).mpr,
    (Ptr.pointsToRange_append b₁.ptr xs ys).mp⟩

/-- `Buffer.sub`: the ownership of a sub-view is carved out of the view. -/
theorem pointsTo_sub (b : Buffer α) (values : List α) (i : Nat) :
    b.ptr ↦* values ⊣⊢
      b.ptr ↦* values.take i ∗
        (b.sub (values.take i).length (values.length - i)).ptr ↦*
          values.drop i :=
  Ptr.pointsToRange_split b.ptr values i

/-! ## Turning a functional mutable slice into memory and back -/

/-- Materialize a functional slice as a fresh mutable memory buffer. -/
def mut_to_raw (slice : Aeneas.Std.Slice α) : Result (Buffer α) :=
  allocArray slice.val fun r => ⟨r.base, r.offset, slice.val.length⟩

@[step]
theorem mut_to_raw.spec (slice : Aeneas.Std.Slice α) :
    ⦃ emp ⦄ mut_to_raw slice ⦃⇓ b => b ↦ slice.val⦄ := by
  refine allocArray.spec _ _ _ fun r h hOwns => ?_
  exact (sep_pure_l _ _ h).mpr ⟨rfl, hOwns⟩

/-- Refunctionalize a mutable buffer, consuming all of its memory ownership. -/
def end_mut_to_raw (original : Aeneas.Std.Slice α) (b : Buffer α) :
    Result (Aeneas.Std.Slice α) := do
  let values ← takeRange b.ptr b.length
  pure (original.setSlice! 0 values)

@[step]
theorem end_mut_to_raw.spec (original : Aeneas.Std.Slice α) (b : Buffer α)
    (values : List α) :
    ⦃ b ↦ values ⦄ end_mut_to_raw original b
      ⦃⇓ result =>
        ⌜result.val = original.val.setSlice! 0 values⌝⦄ := by
  unfold end_mut_to_raw
  apply triple_ipure
  intro hLength
  have hTake :
      ⦃ b.ptr ↦* values ⦄ takeRange b.ptr b.length
        ⦃⇓ result => ⌜result = values⌝⦄ :=
    takeRange.spec_of_length b.ptr values b.length hLength
  apply triple_bind hTake
  intro result
  exact triple_pure fun _ hResult => by
    rw [hResult, Aeneas.Std.Slice.setSlice!_val]
    rfl

end Buffer

end Aeneas.SLPoC
