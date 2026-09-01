import Aeneas.SLPoC.MutableData.Ptr

/-!
# Buffers

`Buffer α` is a bounded view of the allocation of [`Array.lean`](Array.lean):
a base address, an offset and a length.  Like the interior pointers of
[`Ptr.lean`](Ptr.lean) it carries no permission — `b ↦ values` is what owns the
slots it spans — and the view is only a *value*: `sub`, `split` and `join`
compute new views, while the lemmas below say how ownership follows them.

Every operation reduces to a pointer operation, and none has a precondition:
`Buffer.sub b i n` and `Buffer.split b i` are total, and a read or a write out
of the range the caller owns simply has no provable triple.
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
  deriving Inhabited

namespace Buffer

/-- The pointer to the first slot of the view. -/
def ptr (b : Buffer α) : Ptr α := ⟨b.base, b.offset⟩

/-- The pointer to the slot at index `i` of the view. -/
def ptrAt (b : Buffer α) (i : Nat) : Ptr α := ⟨b.base, b.offset + i⟩

def baseRef (b : Buffer α) : ArrayBase α := b.base

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
def Buffer.alloc (n : Nat) (value : α) : St (Buffer α) :=
  allocArray (Frags.ofList 0 (List.replicate n (.initialized value)))
    fun r => ⟨r, 0, n⟩

@[step]
theorem Buffer.alloc.spec (n : Nat) (value : α) :
    ⦃ emp ⦄ Buffer.alloc n value ⦃⇓ b => b ↦ List.replicate n value⦄ := by
  refine allocArray.spec _ _ _ fun r h hPointsTo => ?_
  refine (sep_pure_l _ _ h).mpr ⟨by simp, ?_⟩
  show Heap.Sub (singleton r (Frags.ofList 0
    ((List.replicate n value).map InitState.initialized))) h
  rw [List.map_replicate]
  exact hPointsTo

/-- Allocate `n` slots and write to none of them. -/
def Buffer.allocUninit (α : Type) (n : Nat) : St (Buffer α) :=
  allocArray (α := α)
    (Frags.ofList 0 (List.replicate n InitState.uninitialized))
    fun r => ⟨r, 0, n⟩

@[step]
theorem Buffer.allocUninit.spec (α : Type) (n : Nat) :
    ⦃ emp ⦄ Buffer.allocUninit α n ⦃⇓ b => b.ptr.pointsToUninit n⦄ :=
  allocArray.spec _ _ _ fun _ => entails_refl _

/-! ## Indexed access and deallocation -/

namespace Buffer

def read (b : Buffer α) (i : Nat) : St α := _root_.Aeneas.SLPoC.read (b.ptrAt i)

@[step]
theorem read.spec (b : Buffer α) (i : Nat) (value : α) :
    ⦃ (b.ptrAt i) ↦ value ⦄ b.read i
      ⦃⇓ result => ⌜result = value⌝ ∗ (b.ptrAt i) ↦ value⦄ :=
  _root_.Aeneas.SLPoC.read.spec (b.ptrAt i) value

def write (b : Buffer α) (i : Nat) (value : α) : St Unit :=
  _root_.Aeneas.SLPoC.update (b.ptrAt i) value

@[step]
theorem write.spec (b : Buffer α) (i : Nat) (oldValue newValue : α) :
    ⦃ (b.ptrAt i) ↦ oldValue ⦄ b.write i newValue
      ⦃⇓ (b.ptrAt i) ↦ newValue⦄ :=
  _root_.Aeneas.SLPoC.update.spec (b.ptrAt i) oldValue newValue

def free (b : Buffer α) : St Unit :=
  guardedModify (fun h => contains h b.baseRef) fun h hContains =>
    ((), h.upd b.baseRef (Frags.release b.offset b.length) hContains)

@[step]
theorem free.spec (b : Buffer α) (values : List α) :
    ⦃ b ↦ values ⦄ b.free ⦃⇓ emp⦄ := by
  apply triple_guardedModify
  intro h hPointsTo frame hCompatible
  obtain ⟨hLength, hRange⟩ := (sep_pure_l _ _ h).mp hPointsTo
  have hContains : contains h b.baseRef := contains_of_sub hRange
  have hFramePreserving :=
    Frags.framePreserving_release (α := InitState α) b.offset b.length
  have hOwns : ∀ j, b.offset ≤ j → j < b.offset + b.length →
      ((h.get b.baseRef).get j).IsOwned := by
    intro j hLow hHigh
    exact Ptr.isOwned_of_pointsToRange hRange (k := j - b.offset)
      (by show j = b.offset + (j - b.offset); omega) (by omega)
  exact ⟨contains_union_left hContains,
    h.upd b.baseRef (Frags.release b.offset b.length) hContains,
    Heap.disjoint_upd_left hFramePreserving hCompatible hContains hOwns,
    Heap.upd_union_left hFramePreserving hCompatible hContains hOwns, trivial⟩

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

end Buffer

end Aeneas.SLPoC
